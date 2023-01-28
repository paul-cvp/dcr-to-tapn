from pm4py.objects.petri_net.obj import *
from pm4py.objects.petri_net.utils import petri_utils as pn_utils
from pm4py.objects.petri_net.exporter import exporter as pnml_exporter

from pm4py.objects.dcr.importer import importer as dcr_importer

from src.mappings import exceptional_cases, single_relations, preoptimizer
from src import util

class Dcr2PetriTransport(object):

    def __init__(self, preoptimize=True, postoptimize=True, map_unexecutable_events=False) -> None:
        self.in_t_types = ['event', 'init', 'initpend', 'pend']
        self.helper_struct = {}
        self.preoptimize = preoptimize
        self.postoptimize = postoptimize
        self.map_unexecutable_events = map_unexecutable_events
        self.preoptimizer = preoptimizer.Preoptimizer()
        self.transitions = {}
        self.mapping_exceptions = None
        self.reachability_timeout = None
        self.print_steps = False

        # self.sim_trace_from_tapaal = None

    def initialize_helper_struct(self, G) -> None:

        for event in G['events']:
            self.helper_struct[event] = {}
            self.helper_struct[event]['places'] = {}
            self.helper_struct[event]['places']['included'] = None
            self.helper_struct[event]['places']['pending'] = None
            self.helper_struct[event]['places']['pending_excluded'] = None
            self.helper_struct[event]['places']['executed'] = None
            self.helper_struct[event]['transitions'] = []
            self.helper_struct[event]['trans_group_index'] = 0
            self.helper_struct[event]['t_types'] = self.in_t_types

            self.transitions[event] = {}
            for event_prime in G['events']:
                self.transitions[event][event_prime] = []

            self.mapping_exceptions = exceptional_cases.ExceptionalCases(self.helper_struct)

    def create_event_pattern_places(self, event, G, tapn, m) -> (PetriNet, Marking):
        default_make_included = True
        default_make_pend = True
        default_make_pend_ex = True
        default_make_exec = True
        if self.preoptimize:
            default_make_included = event in self.preoptimizer.need_included_place
            default_make_pend = event in self.preoptimizer.need_pending_place
            default_make_pend_ex = event in self.preoptimizer.need_pending_excluded_place
            default_make_exec = event in self.preoptimizer.need_executed_place

        if default_make_included:
            inc_place = PetriNet.Place(f'included_{event}')
            tapn.places.add(inc_place)
            self.helper_struct[event]['places']['included'] = inc_place
            # fill the marking
            if event in G['marking']['included']:
                m[inc_place] = 1

        if default_make_pend:
            pend_place = PetriNet.Place(f'pending_{event}')
            tapn.places.add(pend_place)
            self.helper_struct[event]['places']['pending'] = pend_place
            # fill the marking
            if event in G['marking']['pending'] and event in G['marking']['included']:
                m[pend_place] = 1

        if default_make_pend_ex:
            pend_excl_place = PetriNet.Place(f'pending_excluded_{event}')
            tapn.places.add(pend_excl_place)
            self.helper_struct[event]['places']['pending_excluded'] = pend_excl_place
            # fill the marking
            if event in G['marking']['pending'] and not event in G['marking']['included']:
                m[pend_excl_place] = 1

        if default_make_exec:
            exec_place = PetriNet.Place(f'executed_{event}')
            tapn.places.add(exec_place)
            self.helper_struct[event]['places']['executed'] = exec_place
            # fill the marking
            if event in G['marking']['executed']:
                m[exec_place] = 1
        # TODO: Figure out why I put something about event_in_self here
        # event_in_self = False
        # for k, v in self.mapping_exceptions.self_exceptions.items():
        #     if event in v:
        #         event_in_self = True
        if self.preoptimize:  # and not event_in_self:
            ts = ['event']
            if default_make_exec and not event in G['marking']['executed'] and not event in self.preoptimizer.no_init_t:
                ts.append('init')
            if default_make_exec and default_make_pend and not event in self.preoptimizer.no_initpend_t:
                ts.append('initpend')
            if default_make_pend:  # TODO: figure out how to check if you need pending based on the initial marking and rules
                ts.append('pend')
            self.helper_struct[event]['t_types'] = ts

        return tapn, m

    def create_event_pattern(self, event, G, tapn, m) -> (PetriNet, Marking):
        tapn, m = self.create_event_pattern_places(event, G, tapn, m)
        tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct,
                                                                  self.mapping_exceptions)
        self.helper_struct[event]['transitions'].extend(ts)
        return tapn, m

    def post_optimize_petri_net_reachability_graph(self, tapn, m, G=None) -> PetriNet:
        from pm4py.objects.petri_net.utils import reachability_graph
        # from pm4py.visualization.transition_system import visualizer as ts_visualizer
        from pm4py.objects.petri_net.transport_invariant import semantics as tapn_semantics
        max_elab_time = 2 * 60 * 60 #2 hours
        if self.reachability_timeout:
            max_elab_time = self.reachability_timeout
        trans_sys = reachability_graph.construct_reachability_graph(tapn, m, use_trans_name=True,
                                                                    parameters={
                                                                        'petri_semantics': tapn_semantics.TransportInvariantSemantics()
                                                                        , 'max_elab_time': max_elab_time})
        # gviz = ts_visualizer.apply(trans_sys, parameters={ts_visualizer.Variants.VIEW_BASED.value.Parameters.FORMAT: "svg"})
        # ts_visualizer.view(gviz)
        fired_transitions = set()

        for transition in trans_sys.transitions:
            fired_transitions.add(transition.name)

        ts_to_remove = set()
        for t in tapn.transitions:
            if t.name not in fired_transitions:
                ts_to_remove.add(t)
        for t in ts_to_remove:
            tapn = pn_utils.remove_transition(tapn, t)

        changed_places = set()
        for state_list in trans_sys.states:
            for state in state_list.name:
                changed_places.add(state)

        ps_to_remove = tapn.places.difference(changed_places)
        parallel_places = set()
        places_to_rename = {}
        if G:
            for event in G['events']:
                for type, event_place in self.helper_struct[event]['places'].items():
                    for type_prime, event_place_prime in self.helper_struct[event]['places'].items():
                        if event_place and event_place_prime and event_place.name != event_place_prime.name and\
                                event_place not in parallel_places:
                            is_parallel = False
                            ep_ins = event_place.in_arcs
                            epp_ins = event_place_prime.in_arcs
                            ep_outs = event_place.out_arcs
                            epp_outs = event_place_prime.out_arcs
                            if len(ep_ins) == len(epp_ins) and len(ep_outs) == len(epp_outs):
                                ep_sources = set()
                                epp_sources = set()
                                for ep_in in ep_ins:
                                    ep_sources.add(ep_in.source)
                                for epp_in in epp_ins:
                                    epp_sources.add(epp_in.source)
                                ep_targets = set()
                                epp_targets = set()
                                for ep_out in ep_outs:
                                    ep_targets.add(ep_out.target)
                                for epp_out in epp_outs:
                                    epp_targets.add(epp_out.target)
                                if ep_sources == epp_sources and ep_targets == epp_targets:
                                    is_parallel = True
                            if is_parallel:
                                parallel_places.add(event_place_prime)
                                places_to_rename[event_place] = f'{type_prime}_{event_place.name}'
        ps_to_remove = ps_to_remove.union(parallel_places)
        for p in ps_to_remove:
            tapn = pn_utils.remove_place(tapn, p)

        for p, name in places_to_rename.items():
            p.name = name

        return tapn

    # def post_optimize_petri_net_simulation(self, tapn, m) -> (PetriNet, Marking):
    #     '''
    #     For now this is a manual step. It involves:
    #         1. Uploading the tapn with the initial marking to TAPAAL
    #         2. Running the simulation (several times, random transition execution, etc.)
    #         3. Analyzing the trace and only keeping the transitions that are visible in the trace
    #     Parameters
    #     ----------
    #     Returns
    #     -------
    #     '''
    #
    #     # visible_transitions = rg.marking_flow_petri(tapn,m)
    #     import xml.etree.ElementTree as ET
    #
    #     fired_transitions = set()
    #     # changed_places = set()
    #
    #     from pm4py.algo.simulation.playout.petri_net import algorithm as sim
    #     # from pm4py.objects.log.obj import EventLog
    #     from pm4py.algo.simulation.playout.petri_net.algorithm import Variants as sim_variants
    #     from pm4py.objects.petri_net.transport_invariant import semantics as tapn_semantics
    #     # el = EventLog()
    #     el = sim.apply(tapn, m, parameters={'petri_semantics': tapn_semantics.TransportInvariantSemantics(),
    #                                         'noTraces': 1,
    #                                         'maxTraceLength': 1000,
    #                                         'initial_timestamp': 0
    #                                         }, variant=sim_variants.EXTENSIVE)
    #     for event in el[0]:
    #         fired_transitions.add(event)
    #     # for transition in root.findall('transition'):
    #     #     t_name = transition.attrib['id'].replace(tapn_name, '')
    #     #     fired_transitions.add(t_name)
    #     #     for token in transition.findall('token'):
    #     #         p_name = token.attrib['place'].replace(tapn_name, '')
    #     #         changed_places.add(p_name)
    #
    #     ts_to_remove = set()
    #     for t in tapn.transitions:
    #         if t.name not in fired_transitions:
    #             ts_to_remove.add(t)
    #     for t in ts_to_remove:
    #         tapn = pn_utils.remove_transition(tapn, t)
    #
    #     # ps_to_remove = set()
    #     # for p in tapn.places:
    #     #     if p.name not in changed_places:
    #     #         ps_to_remove.add(p)
    #     # for p in ps_to_remove:
    #     #     tapn = pn_utils.remove_place(tapn, p)
    #
    #     return tapn, m
    #
    # def post_optimize_petri_net_tapaal(self, tapn, m, tapaal_trc_file_path) -> (PetriNet, Marking):
    #     '''
    #     For now this is a manual step. It involves:
    #         1. Uploading the tapn with the initial marking to TAPAAL
    #         2. Running the simulation (several times, random transition execution, etc.)
    #         3. Analyzing the trace and only keeping the transitions that are visible in the trace
    #     Parameters
    #     ----------
    #     Returns
    #     -------
    #     '''
    #
    #     #
    #     # visible_transitions = rg.marking_flow_petri(tapn,m)
    #     import xml.etree.ElementTree as ET
    #     tapn_name = 'netFromDCR_'
    #     tree = ET.parse(tapaal_trc_file_path)
    #     root = tree
    #     fired_transitions = set()
    #     changed_places = set()
    #
    #     #TODO: make TAPN import work in pm4py
    #     #tapn, m,fm = pnml_importer.apply(tapn_file_path, variant=pnml_importer.TAPN)
    #
    #     for transition in root.findall('transition'):
    #         t_name = transition.attrib['id'].replace(tapn_name, '')
    #         fired_transitions.add(t_name)
    #         for token in transition.findall('token'):
    #             p_name = token.attrib['place'].replace(tapn_name, '')
    #             changed_places.add(p_name)
    #
    #     ts_to_remove = set()
    #     for t in tapn.transitions:
    #         if t.name not in fired_transitions:
    #             ts_to_remove.add(t)
    #     for t in ts_to_remove:
    #         tapn = pn_utils.remove_transition(tapn, t)
    #
    #     ps_to_remove = set()
    #     for p in tapn.places:
    #         if p.name not in changed_places:
    #             ps_to_remove.add(p)
    #     for p in ps_to_remove:
    #         tapn = pn_utils.remove_place(tapn, p)
    #
    #     return tapn, m

    def dcr2tapn(self, G, tapn_path) -> (PetriNet, Marking):
        self.basic = True  # True (basic) = inc,ex,resp,cond | False = basic + no-resp,mil
        self.timed = False  # False = untimed | True = timed cond (delay) and resp (deadline)
        self.initialize_helper_struct(G)
        tapn = PetriNet("Dcr2Tapn")
        m = Marking()
        # pre-optimize mapping based on DCR graph behaviour
        if self.preoptimize:
            if self.print_steps:
                print('[i] preoptimizing')
            self.preoptimizer.pre_optimize_based_on_dcr_behaviour(G)
            if not self.map_unexecutable_events:
                G = self.preoptimizer.remove_un_executable_events_from_dcr(G)

        # including the handling of exception cases from the induction step
        G = self.mapping_exceptions.filter_exceptional_cases(G)
        if self.preoptimize:
            if self.print_steps:
                print('[i] finding exceptional behaviour')
            self.preoptimizer.preoptimize_based_on_exceptional_cases(G, self.mapping_exceptions)

        # map events
        if self.print_steps:
            print('[i] mapping events')
        for event in G['events']:
            tapn, m = self.create_event_pattern(event, G, tapn, m)
        # all self exceptions have been mapped at this point

        sr = single_relations.SingleRelations(self.helper_struct, self.mapping_exceptions)
        # map effect relations
        if self.print_steps:
            print('[i] map effect relations')
        for event in G['includesTo']:
            for event_prime in G['includesTo'][event]:
                tapn = sr.create_include_pattern(event, event_prime, tapn)
        for event in G['excludesTo']:
            for event_prime in G['excludesTo'][event]:
                tapn = sr.create_exclude_pattern(event, event_prime, tapn)
        for event in G['responseTo']:
            for event_prime in G['responseTo'][event]:
                tapn = sr.create_response_pattern(event, event_prime, tapn)
        if not self.basic:
            for event in G['noResponseTo']:
                for event_prime in G['noResponseTo'][event]:
                    tapn = sr.create_no_response_pattern(event, event_prime, tapn)

        # map constraining relations
        if self.print_steps:
            print('[i] map constraining relations')
        for event in G['conditionsFor']:
            for event_prime in G['conditionsFor'][event]:
                tapn = sr.create_condition_pattern(event, event_prime, tapn)
        if not self.basic:
            for event in G['milestonesFor']:
                for event_prime in G['milestonesFor'][event]:
                    tapn = sr.create_milestone_pattern(event, event_prime, tapn)

        # handle all relation exceptions
        if self.print_steps:
            print('[i] handle all relation exceptions')
        tapn = self.mapping_exceptions.map_exceptional_cases_between_events(tapn, m)

        # post-optimize based on the petri net reachability graph
        if self.postoptimize:
            if self.print_steps:
                print('[i] post optimizing')
            tapn = self.post_optimize_petri_net_reachability_graph(tapn, m, G)

        if self.print_steps:
            print(f'[i] export to {tapn_path}')
        pn_export_format = pnml_exporter.TAPN
        if tapn_path.endswith("pnml"):
            pn_export_format = pnml_exporter.PNML

        pnml_exporter.apply(tapn, m, tapn_path, variant=pn_export_format, parameters={'isTimed': self.timed})

        # post-optimize based on tapaal simulation
        # if self.postoptimize:
        #     print(f'[!] You chose to post optimize the TAPN {tapn_path} please add .trc file path from the TAPAAL simulation:')
        #     trc_file_path = input()
        #     if trc_file_path:
        #         tapn, m = self.post_optimize_petri_net_tapaal(tapn, m, trc_file_path)

        # post-optimize based on pm4py simulation
        # if self.postoptimize:
        #     tapn, m = self.post_optimize_petri_net_simulation(tapn, m)

        return tapn, m


from copy import deepcopy
import itertools
from itertools import combinations


def prepare_all_permutations():
    dcr_template = {
        'events': set(),
        'conditionsFor': {},
        'milestonesFor': {},
        'responseTo': {},
        'noResponseTo': {},
        'includesTo': {},
        'excludesTo': {},
        'conditionsForDelays': {},
        'responseToDeadlines': {},
        'marking': {'executed': set(),
                    'included': set(),
                    'pending': set()
                    }
    }
    effect_relations = ['includesTo', 'excludesTo', 'responseTo', 'noResponseTo']
    constrain_relations = ['conditionsFor', 'milestonesFor']
    all_relations = effect_relations + constrain_relations
    e1 = 'A'
    e2 = 'B'
    dcrs_to_test = {}
    for j in [1, 2]:
        for i in range(6, 0, -1):
            for comb in combinations(all_relations, i):
                if j == 1:
                    for (ai, ae, ap) in itertools.product([True, False], repeat=3):
                        dcr = deepcopy(dcr_template)
                        dcr['events'] = {e1}
                        if ai:
                            dcr['marking']['included'] = {e1}
                        if ae:
                            dcr['marking']['executed'] = {e1}
                        if ap:
                            dcr['marking']['pending'] = {e1}
                        for rel in comb:
                            if not e1 in dcr[rel]:
                                dcr[rel][e1] = set()
                            dcr[rel][e1].add(e1)
                        key = f'self_{repr(comb)}_A{1 if ai else 0}{1 if ae else 0}{1 if ap else 0}'
                        dcrs_to_test[key] = dcr
                else:
                    for (ai, ae, ap, bi, be, bp) in itertools.product([True, False], repeat=6):
                        dcr = deepcopy(dcr_template)
                        dcr['events'] = {e1, e2}
                        if ai:
                            dcr['marking']['included'].add(e1)
                        if ae:
                            dcr['marking']['executed'].add(e1)
                        if ap:
                            dcr['marking']['pending'].add(e1)
                        if bi:
                            dcr['marking']['included'].add(e2)
                        if be:
                            dcr['marking']['executed'].add(e2)
                        if bp:
                            dcr['marking']['pending'].add(e2)
                        for rel in comb:
                            if rel in constrain_relations:
                                if not e2 in dcr[rel]:
                                    dcr[rel][e2] = set()
                                dcr[rel][e2].add(e1)
                            else:
                                if not e1 in dcr[rel]:
                                    dcr[rel][e1] = set()
                                dcr[rel][e1].add(e2)
                        key = f'rel_{repr(comb)}_A{1 if ai else 0}{1 if ae else 0}{1 if ap else 0}_B{1 if bi else 0}{1 if be else 0}{1 if bp else 0}'
                        # if key.replace("'", "").replace("(", "").replace(")", "").replace(",", "").replace(" ", "_") == 'rel_conditionsFor_A100_B100':
                        #     print(dcr)
                        dcrs_to_test[key] = dcr
    return dcrs_to_test


def complete_test(dcrs_to_test):
    past_k = None
    i = 0
    counter = 0
    for k, v in dcrs_to_test.items():
        k_split = k.split('_')
        file_name = k.replace("'", "").replace("(", "").replace(")", "").replace(",", "").replace(" ", "_")
        file_name = file_name + ".tapn"
        res_path = f"../models/all/{file_name}"
        d2p = Dcr2PetriTransport(preoptimize=True, postoptimize=True, map_unexecutable_events=False)
        tapn = d2p.dcr2tapn(v, res_path)
        if k_split[1] != past_k:
            # print(f'[i] {k}')
            i = i + 1
            past_k = k_split[1]
        counter = counter + 1


def run_all():
    '''
    this runs all permutations of 1 or 2 events and 1 or 6 relations and all of their possible markings
    '''
    dcrs_to_test = prepare_all_permutations()
    complete_test(dcrs_to_test)


def run_specific_dcr():
    '''
    here you can write your own graph and run it
    '''
    dcr = {
        'events': {'A', 'B'},
        'conditionsFor': {'A': {'B'}},
        'milestonesFor': {},
        'responseTo': {},
        'noResponseTo': {},
        'includesTo': {},
        'excludesTo': {'A': {'B'}},
        # 'conditionsForDelays': {'A': {'B': 2}},
        # 'responseToDeadlines': {'C': {'B': 5}, 'A': {'B': 7}},
        'marking': {'executed': set(),
                    'included': {'A', 'B'},
                    'pending': set()
                    }
    }

    d2p = Dcr2PetriTransport(preoptimize=True, postoptimize=True, map_unexecutable_events=False)
    print('[i] dcr')
    tapn, m = d2p.dcr2tapn(dcr, tapn_path="../models/one_petri.tapn")


def run_dcrxml_files():
    '''
    here you can specify which files you want to execute in a matrix
    the matrix structure is as follows:
       each line is an input for 1 execution
       one line has the following parameters:
       [source file name under models/dcrxml, destination tapn file name, if it should preoptimize, if it should postoptimize, if it should map unexecutable events]

    Remember to create the models folder at the same level as the src folder and inside the models folder create the dcrxml folder
    '''
    dcrxml_files = [
        # ['test_specific_mapping.xml', 'test_specific_mapping_unoptimized.tapn', True, False, False],  # i=0
        # ['test_specific_mapping.xml', 'test_specific_mapping.tapn', False, True, True],  # i=1 etc.
        # ['DCR_Indicators_220810_Fix2.xml', 'dcr_indicators_fix2_unoptimized.tapn', True, False, False],
        # ['DCR_Indicators_220810_Fix2.xml', 'dcr_indicators_fix2.tapn', False, True, True],
        # ['DCR_Indicators_220906_Fulllog.xml', 'dcr_indicators_full.tapn', False, True, True],
        # ['Road Traffic Fine.xml', 'road_traffic_fine_unoptimized.tapn', True, False, False],
        # ['Expense report example.xml', 'expense_report_unoptimized.tapn', True, False, False],
        # ['Road Traffic Fine.xml', 'road_traffic_fine.tapn', False, True, True],
        # ['Expense report example.xml', 'expense_report.tapn', False, True, True],  # i=8
        ['eshop.xml', 'eshop_unoptimized.pnml', False, False, True],
        ['eshop.xml', 'eshop_dcr_analysis.pnml', True, False, False],
        ['eshop.xml', 'eshop_pn_reachability.pnml', False, True, False],
        ['eshop.xml', 'eshop_full_optimization.pnml', True, True, False],
    ]
    # this runs from i=5 to 8 (so the road traffic fine and expense report optimized and unoptimized conversions
    for mapping_call in dcrxml_files:
        # mapping_call = dcrxml_files[i]
        d2p = Dcr2PetriTransport(preoptimize=mapping_call[2], postoptimize=mapping_call[3],
                                 map_unexecutable_events=mapping_call[4])
        d2p.print_steps = True
        print(f'[i] import {mapping_call[0]}')
        dcr = dcr_importer.apply(f'../models/dcrxml/{mapping_call[0]}')
        print(f'[i] convert {mapping_call[0]}')
        tapn, m = d2p.dcr2tapn(dcr, tapn_path=f"../models/{mapping_call[1]}")


if __name__ == '__main__':
    # uncomment which one you need and read more in the function about what it does
    run_all()  # runs all possible 1,2 event and relation combinations (see the method definition and comments above)
    #run_specific_dcr()  # runs a user defined dcr graph written as a python dict (see the method definition and comments above)
    #run_dcrxml_files()  # runs on specific dcrxml files (see the method definition and comments above)
    print('[i] Done!')
