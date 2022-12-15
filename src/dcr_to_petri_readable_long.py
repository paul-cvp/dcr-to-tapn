from pm4py.objects.petri_net.obj import *
from pm4py.objects.petri_net.utils import petri_utils as pn_utils
from pm4py.objects.petri_net.exporter import exporter as pnml_exporter

from pm4py.objects.dcr.importer import importer as dcr_importer
# from src.mappings import exceptional_cases, preoptimizer

class ExceptionalCases(object):
    def __init__(self):
        self.milestone_condition_pairs = set()
        self.no_response_include_pairs = set()
        self.no_response_exclude_pairs = set()
        self.self_condition_milestone = set()
        self.self_no_response = set()
        self.self_milestone = set()
        self.self_includes = set()
        self.self_excludes = set()
        self.self_response = set()
        self.self_condition = set()
        self.self_response_exclude = set()
        self.condition_include_pairs = set()
        self.condition_exclude_pairs = set()
        self.condition_response_pairs = set()
        self.condition_noresponse_pairs = set()
        self.milestone_noresponse_pairs = set()
        self.response_include_pairs = set()
        self.response_exclude_pairs = set()
        self.cond_res_inc_pairs = set()
        self.cond_res_exc_pairs = set()

class Preoptimizer(object):
        need_included_place = set()
        need_executed_place = set()
        need_pending_place = set()
        need_pending_excluded_place = set()
        un_executable_events = set()

class Dcr2PetriTransport(object):
    helper_struct = {}
    mapping_exceptions = ExceptionalCases()
    preoptimizer = Preoptimizer()
    in_t_types = ['event', 'init', 'initpend', 'pend']
    preoptimize = True
    postoptimize = True
    map_unexecutable_events = False
    sim_trace_from_tapaal = None

    def __init__(self, preoptimize = True, postoptimize = True, map_unexecutable_events = False) -> None:
        self.preoptimize = preoptimize
        self.postoptimize = postoptimize
        self.map_unexecutable_events = map_unexecutable_events
        super().__init__()

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
        self.transitions = {}
        for event in G['events']:
            self.transitions[event] = {}
            for event_prime in G['events']:
                self.transitions[event][event_prime] = []

    def map_existing_transitions_of_copy_0(self,delta,copy_0,t,tapn) -> (PetriNet, PetriNet.Transition):
        trans = copy_0[delta]
        # if trans in tapn.transitions: # since this is a copy this cannot be checked here. trust me bro
        in_arcs = trans.in_arcs
        for arc in in_arcs:
            source = arc.source
            type = arc.properties['arctype'] if 'arctype' in arc.properties else None
            pn_utils.add_arc_from_to(source, t, tapn, type=type, with_check=True)
        out_arcs = trans.out_arcs
        for arc in out_arcs:
            target = arc.target
            type = arc.properties['arctype'] if 'arctype' in arc.properties else None
            pn_utils.add_arc_from_to(t, target, tapn, type=type, with_check=True)
        return tapn, t

    def create_event_pattern_transitions_and_arcs(self, tapn, event):
        inc_place = self.helper_struct[event]['places']['included']
        exec_place = self.helper_struct[event]['places']['executed']
        pend_place = self.helper_struct[event]['places']['pending']
        pend_exc_place = self.helper_struct[event]['places']['pending_excluded']
        i_copy = self.helper_struct[event]['trans_group_index']
        ts = []
        for t_name in self.helper_struct[event]['t_types']:  # ['event','init','initpend','pend']:
            t = PetriNet.Transition(f'{t_name}_{event}{i_copy}', f'{t_name}_{event}{i_copy}_label')
            tapn.transitions.add(t)
            # this if statement handles self response exclude
            if event in self.mapping_exceptions.self_response_exclude:
                pn_utils.add_arc_from_to(t, pend_exc_place, tapn)

            pn_utils.add_arc_from_to(inc_place, t, tapn)
            # this if statement handles self exclude and self response exclude
            if not ((event in self.mapping_exceptions.self_excludes) or (event in self.mapping_exceptions.self_response_exclude)):
                pn_utils.add_arc_from_to(t, inc_place, tapn)

            # this if statement handles self response
            if event in self.mapping_exceptions.self_response:
                pn_utils.add_arc_from_to(t, pend_place, tapn)

            if t_name.__contains__('init'):
                pn_utils.add_arc_from_to(t, exec_place, tapn)
                pn_utils.add_arc_from_to(exec_place, t, tapn, type='inhibitor')
            else:
                pn_utils.add_arc_from_to(t, exec_place, tapn)
                pn_utils.add_arc_from_to(exec_place, t, tapn)

            if t_name.__contains__('pend'):
                pn_utils.add_arc_from_to(pend_place, t, tapn)
            else:
                pn_utils.add_arc_from_to(pend_place, t, tapn, type='inhibitor')
            ts.append(t)
        self.helper_struct[event]['trans_group_index'] += 1
        return tapn, ts

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

        if self.preoptimize:
            ts = ['event']
            if default_make_exec and not event in G['marking']['executed']:
                ts.append('init')
            if default_make_exec and default_make_pend:
                ts.append('initpend')
            if default_make_pend:
                ts.append('pend')
            self.helper_struct[event]['t_types'] = ts

        return tapn, m

    def create_event_pattern(self, event, G, tapn, m) -> (PetriNet, Marking):
        tapn, m = self.create_event_pattern_places(event, G, tapn, m)
        tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
        self.helper_struct[event]['transitions'].extend(ts)
        return tapn, m

    def create_include_pattern(self, event, event_prime, tapn) -> PetriNet:
        inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
        pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
        pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
        copy_0 = self.helper_struct[event]['transitions']
        len_copy_0 = len(copy_0)
        len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
        new_transitions = []
        # copy 1
        if inc_place_e_prime and pend_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)
        # copy 2
        if inc_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

        # map the copy_0 last but before adding the new transitions
        # copy 0
        if inc_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exclude_pattern(self, event, event_prime, tapn) -> PetriNet:
        inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
        pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
        pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
        copy_0 = self.helper_struct[event]['transitions']
        len_copy_0 = len(copy_0)
        len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
        new_transitions = []
            
        # copy 1
        if inc_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')
                
        # copy 2
        if inc_place_e_prime and pend_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)

        # copy 0
        if inc_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_response_pattern(self, event, event_prime, tapn) -> PetriNet:
        inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
        pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
        pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
        copy_0 = self.helper_struct[event]['transitions']
        len_copy_0 = len(copy_0)
        len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
        new_transitions = []
            
        # copy 1
        if pend_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
        # copy 2
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')
                
        # copy 3
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

        # copy 0
        if pend_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_no_response_pattern(self, event, event_prime, tapn) -> PetriNet:
        inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
        pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
        pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
        copy_0 = self.helper_struct[event]['transitions']
        len_copy_0 = len(copy_0)
        len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
        new_transitions = []

        # copy 1
        if pend_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
        # copy 2
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

        # copy 3
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

        # copy 0
        if pend_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_condition_pattern(self, event, event_prime, tapn) -> PetriNet:
        inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
        exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']

        copy_0 = self.helper_struct[event]['transitions']
        len_copy_0 = len(copy_0)
        len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
        new_transitions = []
        # copy 1
        if inc_place_e_prime and exec_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')
                
        # copy 2
        if inc_place_e_prime and exec_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

        # copy 0
        if exec_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_milestone_pattern(self, event, event_prime, tapn) -> PetriNet:
        inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
        pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
        pend_excluded_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

        copy_0 = self.helper_struct[event]['transitions']
        len_copy_0 = len(copy_0)
        len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
        new_transitions = []
        # copy 1
        if inc_place_e_prime and pend_excluded_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn, type='inhibitor')

        # copy 2
        if inc_place_e_prime and pend_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

        # copy 0
        if pend_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                pn_utils.add_arc_from_to(t, pend_excluded_place_e_prime, tapn)
                pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn)

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def filter_exceptional_cases(self, G):
        for e in G['events']:
            for e_prime in G['events']:
                if e == e_prime:
                    # same event multiple self relations
                    if (e in G['includesTo'] and e_prime in G['includesTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        G['excludesTo'][e].remove(e_prime)
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        G['responseTo'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                        self.mapping_exceptions.self_response_exclude.add(e)
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['milestonesFor'] and e_prime in G['milestonesFor'][e]):
                        G['conditionsFor'][e].remove(e_prime)
                        G['milestonesFor'][e].remove(e_prime)
                        self.helper_struct[e]['t_types'] = ['event']
                        self.mapping_exceptions.self_condition_milestone.add(e)
                    # same event one self relation
                    if e in G['includesTo'] and e_prime in G['includesTo'][e]:
                        self.mapping_exceptions.self_includes.add(e)
                        G['includesTo'][e].remove(e_prime)
                    if e in G['excludesTo'] and e_prime in G['excludesTo'][e]:
                        self.mapping_exceptions.self_excludes.add(e)
                        G['excludesTo'][e].remove(e_prime)
                    if e in G['responseTo'] and e_prime in G['responseTo'][e]:
                        self.mapping_exceptions.self_response.add(e)
                        G['responseTo'][e].remove(e_prime)
                    if e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]:
                        self.mapping_exceptions.self_no_response.add(e)
                        G['noResponseTo'][e].remove(e_prime)
                    if e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]:
                        self.mapping_exceptions.self_condition.add(e)
                        G['conditionsFor'][e].remove(e_prime)
                        # removes the creation of the init and initpend transitions
                        self.helper_struct[e]['t_types'] = ['event', 'pend']
                    if e in G['milestonesFor'] and e_prime in G['milestonesFor'][e]:
                        self.mapping_exceptions.self_milestone.add(e)
                        G['milestonesFor'][e].remove(e_prime)
                        # removes the creation of the pend and initpend transitions
                        self.helper_struct[e]['t_types'] = ['event', 'init']
                else:
                    # distinct events
                    # 1 constrain + 3 effect relations
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        self.mapping_exceptions.cond_res_inc_pairs.add((e, e_prime))
                        G['responseTo'][e].remove(e_prime)
                        G['conditionsFor'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                    # 1 constrain + 2 effect relations
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        self.mapping_exceptions.condition_include_pairs.add((e, e_prime))
                        G['conditionsFor'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        self.mapping_exceptions.cond_res_inc_pairs.add((e, e_prime))
                        G['responseTo'][e].remove(e_prime)
                        G['conditionsFor'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]) and (e in G['responseTo'] and e_prime in G['responseTo'][e]):
                        self.mapping_exceptions.cond_res_exc_pairs.add((e, e_prime))
                        G['responseTo'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                        G['conditionsFor'][e].remove(e_prime)
                    # 4 effect relations
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]) \
                            and (e in G['includesTo'] and e_prime in G['includesTo'][e]) and (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]):
                        G['excludesTo'][e].remove(e_prime)
                        G['noResponseTo'][e].remove(e_prime)
                    # 3 effect relations
                    if (e in G['excludesTo'] and e_prime in G['excludesTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]) \
                            and (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]):
                        G['excludesTo'][e].remove(e_prime)
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]) \
                            and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        G['noResponseTo'][e].remove(e_prime)
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]) \
                            and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        G['noResponseTo'][e].remove(e_prime)
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]) \
                            and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        self.mapping_exceptions.response_include_pairs.add((e, e_prime))
                        G['responseTo'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                    # constrain + effect relation
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        self.mapping_exceptions.condition_include_pairs.add((e, e_prime))
                        G['conditionsFor'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        self.mapping_exceptions.condition_exclude_pairs.add((e, e_prime))
                        G['conditionsFor'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['responseTo'] and e_prime in G['responseTo'][e]):
                        self.mapping_exceptions.condition_response_pairs.add((e, e_prime))
                        G['conditionsFor'][e].remove(e_prime)
                        G['responseTo'][e].remove(e_prime)
                    if (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]) and (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]):
                        G['conditionsFor'][e].remove(e_prime)
                        G['noResponseTo'][e].remove(e_prime)
                        self.mapping_exceptions.condition_noresponse_pairs.add((e, e_prime))
                    if (e in G['milestonesFor'] and e_prime in G['milestonesFor'][e]) and (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]):
                        G['milestonesFor'][e].remove(e_prime)
                        G['noResponseTo'][e].remove(e_prime)
                        self.mapping_exceptions.milestone_noresponse_pairs.add((e, e_prime))

                    # 2 effect relations
                    if (e in G['excludesTo'] and e_prime in G['excludesTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        # having an exclude and include means you only map the include
                        G['excludesTo'][e].remove(e_prime)
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        self.mapping_exceptions.response_include_pairs.add((e, e_prime))
                        G['responseTo'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                    if (e in G['responseTo'] and e_prime in G['responseTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        self.mapping_exceptions.response_exclude_pairs.add((e, e_prime))
                        G['responseTo'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                    if (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]) and (e in G['responseTo'] and e_prime in G['responseTo'][e]):
                        # having a response and noresponse means you only map the response
                        G['noResponseTo'][e].remove(e_prime)
                    if (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]) and (e in G['includesTo'] and e_prime in G['includesTo'][e]):
                        self.mapping_exceptions.no_response_include_pairs.add((e, e_prime))
                        G['noResponseTo'][e].remove(e_prime)
                        G['includesTo'][e].remove(e_prime)
                    if (e in G['noResponseTo'] and e_prime in G['noResponseTo'][e]) and (e in G['excludesTo'] and e_prime in G['excludesTo'][e]):
                        self.mapping_exceptions.no_response_exclude_pairs.add((e, e_prime))
                        G['noResponseTo'][e].remove(e_prime)
                        G['excludesTo'][e].remove(e_prime)
                    # 2 constrain relations
                    if (e in G['milestonesFor'] and e_prime in G['milestonesFor'][e]) and (e in G['conditionsFor'] and e_prime in G['conditionsFor'][e]):
                        self.mapping_exceptions.milestone_condition_pairs.add((e, e_prime))
                        G['milestonesFor'][e].remove(e_prime)
                        G['conditionsFor'][e].remove(e_prime)

        return G

    def map_exceptional_cases_between_events(self, tapn) -> PetriNet:
        tapn = self.create_exception_condition_include_pattern(tapn)
        tapn = self.create_exception_condition_exclude_pattern(tapn)
        tapn = self.create_exception_condition_response_pattern(tapn)

        tapn = self.create_exception_response_include_pattern(tapn)
        tapn = self.create_exception_response_exclude_pattern(tapn)

        tapn = self.create_exception_condition_response_include_pattern(tapn)
        tapn = self.create_exception_condition_response_exclude_pattern(tapn)
        return tapn

    def create_exception_condition_include_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.condition_include_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1 and 2
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)

                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

                        if i == 1:
                            pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 3 and 4
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)

                        pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                        if i == 1:
                            pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_condition_exclude_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.condition_include_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime,t,tapn)
                    pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)

            # copy 2
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

            # copy 3
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_condition_response_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.condition_include_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime,t,tapn)
                    pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)

            # copy 2 and 3
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

                        if i == 1:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)
                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)

            # copy 3 and 4
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                        if i == 1:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)
                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_response_include_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.response_include_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
            # copy 2
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t,inc_place_e_prime,tapn)

                    pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 3
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t,inc_place_e_prime,tapn)

                    pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_response_exclude_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.response_exclude_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)
            # copy 2
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 3
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_condition_response_include_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.cond_res_inc_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                    pn_utils.add_arc_from_to(pend_place_e_prime,t,tapn)
            # copy 2 and 3
            for i in [1,2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')
                        pn_utils.add_arc_from_to(t,inc_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

                        if i == 1:
                            pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 4 and 5
            for i in [1,2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t,inc_place_e_prime, tapn)

                        pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                        if i == 1:
                            pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_condition_response_exclude_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.cond_res_exc_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            for delta in range(len_delta):
                tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime,t,tapn)
                    pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
            # copy 2 and 3
            for i in [1,2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

                        if i == 1:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')
                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)

            # copy 4 and 5
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                        if i == 1:
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')
                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
                        elif i == 2:
                            pn_utils.add_arc_from_to(t,pend_excl_place_e_prime,tapn)
                            pn_utils.add_arc_from_to(pend_excl_place_e_prime,t,tapn)

            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_condition_no_response_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.condition_noresponse_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            if pend_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)

                        pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)
            # copy 2 and 3
            for i in [1, 2]:
                if inc_place_e_prime and pend_excl_place_e_prime:
                    for delta in range(len_delta):
                        tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                        new_transitions.extend(ts)
                        for t in ts:
                            tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                            pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

                            if i == 1:
                                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)
                            elif i == 2:
                                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')
            # copy 3 and 4
            for i in [1, 2]:
                if inc_place_e_prime and pend_excl_place_e_prime:
                    for delta in range(len_delta):
                        tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                        new_transitions.extend(ts)
                        for t in ts:
                            tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                            pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                            pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

                            if i == 1:
                                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)
                            elif i == 2:
                                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

            # copy 0
            if pend_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_no_response_exclude_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.no_response_exclude_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            if pend_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
            # copy 2
            if inc_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 3
            if inc_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

            # copy 0
            if pend_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_no_response_include_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.no_response_include_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            if pend_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)
                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)

                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
            # copy 2
            if inc_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')
                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 3
            if inc_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')
                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

            # copy 0
            if pend_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_milestone_no_response_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.milestone_noresponse_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []

            # copy 1
            if inc_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # copy 2
            if inc_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)

            # copy 0
            if pend_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_condition_milestone_pattern(self, tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.milestone_condition_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            exec_place_e_prime = self.helper_struct[event_prime]['places']['executed']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')
                        if i == 1:
                            pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')
                        elif i == 2:
                            pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)
                            pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)

            # copy 2
            for i in [1, 2]:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
                        if i == 1:
                            pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')
                        elif i == 2:
                            pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)
                            pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)


            # copy 0
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

                pn_utils.add_arc_from_to(t, exec_place_e_prime, tapn)
                pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_milestone_exclude_pattern(self,tapn) -> PetriNet:
        for (event,event_prime) in self.mapping_exceptions.milestone_exclude_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excluded_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            if inc_place_e_prime and pend_excluded_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn, type='inhibitor')

            # copy 2
            if inc_place_e_prime and pend_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

            # copy 0
            if pend_excluded_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excluded_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_milestone_include_pattern(self,tapn) -> PetriNet:
        for (event, event_prime) in self.mapping_exceptions.milestone_include_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excl_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']
            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            if inc_place_e_prime and pend_place_e_prime and pend_excl_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)
            # copy 2
            if inc_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

            # map the copy_0 last but before adding the new transitions
            # copy 0
            if inc_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')
            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def create_exception_milestone_response_pattern(self,tapn) -> PetriNet:
        for (event,event_prime) in self.mapping_exceptions.milestone_response_pairs:
            inc_place_e_prime = self.helper_struct[event_prime]['places']['included']
            pend_place_e_prime = self.helper_struct[event_prime]['places']['pending']
            pend_excluded_place_e_prime = self.helper_struct[event_prime]['places']['pending_excluded']

            copy_0 = self.helper_struct[event]['transitions']
            len_copy_0 = len(copy_0)
            len_delta = int(len_copy_0 / len(self.helper_struct[event]['t_types']))
            new_transitions = []
            # copy 1
            if inc_place_e_prime and pend_excluded_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                        pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn, type='inhibitor')
                        pn_utils.add_arc_from_to(t, pend_excluded_place_e_prime,tapn)

            # copy 2
            if inc_place_e_prime and pend_place_e_prime:
                for delta in range(len_delta):
                    tapn, ts = self.create_event_pattern_transitions_and_arcs(tapn, event)
                    new_transitions.extend(ts)
                    for t in ts:
                        tapn, t = self.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                        pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                        pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                        pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')
                        pn_utils.add_arc_from_to(t,pend_place_e_prime,tapn)

            # copy 0
            if pend_excluded_place_e_prime:
                for t in copy_0:
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excluded_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn)

            self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn

    def pre_optimize_based_on_dcr_behaviour(self,G):
        need_pending_excluded_place = set()

        inclusion_events = set()
        exclusion_events = set()

        condition_events = set()

        response_events = set()
        no_response_events = set()
        milestone_events = set()

        for event in G['events']:
            inclusion_events = inclusion_events.union(set(G['includesTo'][event] if event in G['includesTo'] else set()))
            exclusion_events = exclusion_events.union(set(G['excludesTo'][event] if event in G['excludesTo'] else set()))

            condition_events = condition_events.union(set(G['conditionsFor'][event] if event in G['conditionsFor'] else set()))

            response_events = response_events.union(set(G['responseTo'][event] if event in G['responseTo'] else set()))
            no_response_events = no_response_events.union(set(G['noResponseTo'][event] if event in G['noResponseTo'] else set()))
            milestone_events = milestone_events.union(set(G['milestonesFor'][event] if event in G['milestonesFor'] else set()))

        not_included_events = set(G['events']).difference(set(G['marking']['included']))
        not_included_become_included = not_included_events.intersection(inclusion_events)
        included_become_excluded = set(G['marking']['included']).intersection(exclusion_events)
        need_included_place = not_included_become_included.union(included_become_excluded)
        unexecutable_events = not_included_events.difference(inclusion_events)

        need_executed_place = set(G['marking']['executed']).union(set(G['conditionsFor'])) # condition_events

        need_pending_place = set(G['marking']['pending']).union(response_events)
        need_pending_excluded_place = need_pending_place.intersection(need_included_place)

        self.preoptimizer.need_included_place = need_included_place
        self.preoptimizer.need_executed_place = need_executed_place
        self.preoptimizer.need_pending_place = need_pending_place
        self.preoptimizer.need_pending_excluded_place = need_pending_excluded_place
        self.preoptimizer.un_executable_events = unexecutable_events

    def remove_un_executable_events_from_dcr(self, G):

        for rule in ['conditionsFor', 'milestonesFor', 'responseTo', 'noResponseTo', 'includesTo', 'excludesTo']:
            for re in self.preoptimizer.un_executable_events:
                G[rule].pop(re, None)
            for event in G['events']:
                if event not in self.preoptimizer.un_executable_events and event in G[rule]:
                    G[rule][event] = G[rule][event].difference(self.preoptimizer.un_executable_events)

        G['marking']['included'] = set(G['marking']['included']).difference(self.preoptimizer.un_executable_events)
        G['marking']['executed'] = set(G['marking']['executed']).difference(self.preoptimizer.un_executable_events)
        G['marking']['pending'] = set(G['marking']['pending']).difference(self.preoptimizer.un_executable_events)
        G['events'] = set(G['events']).difference(self.preoptimizer.un_executable_events)
        return G

    def post_optimize_petri_net_reachability_graph(self, tapn, m) -> PetriNet:
        from pm4py.objects.petri_net.utils import reachability_graph
        # from pm4py.visualization.transition_system import visualizer as ts_visualizer
        from pm4py.objects.petri_net.transport_invariant import semantics as tapn_semantics

        trans_sys = reachability_graph.construct_reachability_graph(tapn, m, use_trans_name=True,
                                                                    parameters={'petri_semantics': tapn_semantics.TransportInvariantSemantics()})
                                                                                #,'max_elab_time': 2*60})
        # gviz = ts_visualizer.apply(ts, parameters={ts_visualizer.Variants.VIEW_BASED.value.Parameters.FORMAT: "svg"})
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
        for p in ps_to_remove:
            tapn = pn_utils.remove_place(tapn, p)

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
        self.basic = True # True (basic) = inc,ex,resp,cond | False = basic + no-resp,mil
        self.timed = False # False = untimed | True = timed cond (delay) and resp (deadline)

        self.initialize_helper_struct(G)
        tapn = PetriNet("Dcr2Tapn")
        m = Marking()
        # pre-optimize mapping based on DCR graph behaviour
        if self.preoptimize:
            self.pre_optimize_based_on_dcr_behaviour(G)
        if not self.map_unexecutable_events:
            G = self.remove_un_executable_events_from_dcr(G)

        # including the handling of exception cases from the induction step
        G = self.filter_exceptional_cases(G)

        # map events
        for event in G['events']:
            tapn, m = self.create_event_pattern(event, G, tapn, m)
        # all self exceptions have been mapped at this point

        # map effect relations
        print('[i] map effect relations')
        for event in G['includesTo']:
            for event_prime in G['includesTo'][event]:
                tapn = self.create_include_pattern(event, event_prime, tapn)
        for event in G['excludesTo']:
            for event_prime in G['excludesTo'][event]:
                tapn = self.create_exclude_pattern(event, event_prime, tapn)
        for event in G['responseTo']:
            for event_prime in G['responseTo'][event]:
                tapn = self.create_response_pattern(event, event_prime, tapn)
        if not self.basic:
            for event in G['noResponseTo']:
                for event_prime in G['noResponseTo'][event]:
                    tapn = self.create_no_response_pattern(event, event_prime, tapn)

        # map constraining relations
        print('[i] map constraining relations')
        for event in G['conditionsFor']:
            for event_prime in G['conditionsFor'][event]:
                tapn = self.create_condition_pattern(event, event_prime, tapn)
        if not self.basic:
            for event in G['milestonesFor']:
                for event_prime in G['milestonesFor'][event]:
                    tapn = self.create_milestone_pattern(event, event_prime, tapn)
        # handle all relation exceptions
        print('[i] handle all relation exceptions')
        tapn = self.map_exceptional_cases_between_events(tapn)
        # post-optimize based on the petri net reachability graph
        if self.postoptimize:
            print('[i] post optimizing')
            tapn = self.post_optimize_petri_net_reachability_graph(tapn, m)

        print('[i] export')
        pnml_exporter.apply(tapn, m, tapn_path, variant=pnml_exporter.TAPN)

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

if __name__ == '__main__':
    # dcr = {
    #     'events': {'A', 'B', 'C'},
    #     'conditionsFor': {'A': {'B'}},
    #     'milestonesFor': {},
    #     'responseTo': {'C': {'B'}, 'A': {'B'}},
    #     'noResponseTo': {},
    #     'includesTo': {'A': {'B', 'C'}},
    #     'excludesTo': {'B': {'C'}},
    #     'conditionsForDelays': {'A': {'B': 2}},
    #     'responseToDeadlines': {'C': {'B': 5}, 'A': {'B': 7}},
    #     'marking': {'executed': set(),
    #                 'included': {'A'},
    #                 'pending': set()
    #                 }
    # }
    # d2p = Dcr2PetriTransport(preoptimize=True, postoptimize=True, map_unexecutable_events=False)
    # print('[i] dcr')
    # tapn, m = d2p.dcr2tapn(dcr, tapn_path="../models/petri.tapn")

    dcrxml_tapn_files = [['test_specific_mapping.xml', 'test_specific_mapping_unoptimized.tapn', True, False, False],
                         ['test_specific_mapping.xml', 'test_specific_mapping.tapn', True, True, False],
                         ['DCR_Indicators_220810_Fix2.xml', 'dcr_indicators_fix2_unoptimized.tapn', True, False, False],
                         ['DCR_Indicators_220810_Fix2.xml', 'dcr_indicators_fix2.tapn', True, True, False],
                         ['DCR_Indicators_220906_Fulllog.xml', 'dcr_indicators_full_unoptimized.tapn', True, False, False],
                         ['DCR_Indicators_220906_Fulllog.xml', 'dcr_indicators_full.tapn', True, True, False]]

    mapping_call = dcrxml_tapn_files[4]
    d2p = Dcr2PetriTransport(preoptimize=mapping_call[2], postoptimize=mapping_call[3], map_unexecutable_events=mapping_call[4])
    print('[i] import fix2')
    dcr_indicators_fix2 = dcr_importer.apply(f'../models/dcrxml/{mapping_call[0]}')
    print('[i] convert fix2')
    tapn, m = d2p.dcr2tapn(dcr_indicators_fix2, tapn_path=f"../models/{mapping_call[1]}")


