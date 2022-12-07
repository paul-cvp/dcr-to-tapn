from pm4py.objects.petri_net.obj import *
from pm4py.objects.petri_net.utils import petri_utils as pn_utils
from pm4py.objects.petri_net.exporter import exporter as pnml_exporter

import itertools


class Dcr2PetriTransport(object):

    def __init__(self, G=None) -> None:
        if G:
            self.prepare_helper_data_structure(G)
        super().__init__()

    # checks to not create duplicates where rules might overlap (they shouldn't)
    def check_arc_exists(self, source, target, tapn: PetriNet):
        if source and target:
            for arc in tapn.arcs:
                if arc.source.name == source.name and arc.target.name == target.name:
                    return True
        return False

    def check_place_exists(self, place: PetriNet.Place, tapn: PetriNet):
        for tapn_place in tapn.places:
            if tapn_place.name == place.name:
                return True
        return False

    def check_transition_exists(self, transition: PetriNet.Transition, tapn: PetriNet):
        for tapn_transition in tapn.transitions:
            if tapn_transition.name == transition.name:
                return True
        return False

    # preparations
    def prepare_helper_data_structure(self, G):
        # keeping track of stuff
        self.pending_places = {}
        self.pending_excluded_places = {}
        self.makes_pending_place = {}
        self.makes_pending_excluded_place = {}
        self.pp_pe_tuples_by_event_prime = {}
        self.execute_places = {}
        self.include_places = {}

        self.all_places = {}
        self.all_transitions = {}

        # helper sets
        # there will be or 3^n (2^(n+1) - r) transitions for each condition and milestone relation where r number of conditions
        self.conditions_count = {}
        self.milestones_count = {}

        # there will be 2^(n+1) transitions for each inclusion/exclusion response/noresponse relation where n number events
        self.event_inc_exc_count = {}
        self.inc_ex_set = {}
        self.event_resp_no_resp_count = {}
        self.resp_no_resp_set = {}

        self.origin_pending_event = {}

        # optimiziation to reduce pn size
        self.need_pending_place = set(G['marking']['pending'])
        not_included_become_included = set(G['events']).difference(set(G['marking']['included']))  # all events - included
        included_become_excluded = set(G['marking']['included'])
        inc_exc = set()
        self.need_executed_place = set()  # set(G['events']).difference(set(G['marking']['executed']))
        self.self_included = set()
        self.self_excluded = set()
        self.self_condition = set()
        self.self_response = set()
        self.self_noresponse = set()
        self.self_milestone = set()
        self.already_executed = set(G['marking']['executed'])
        self.executed_and_included = set(G['marking']['included']).intersection(self.already_executed)
        self.milestone_response_pair = {}
        # timed stuff
        self.multiple_pending = set()
        self.inc_ex_transport_pp_pe_timed_token = set()
        self.reverse_response_mapping = {}
        for k, v in G['responseTo'].items():
            for i in v:
                if i in self.reverse_response_mapping:
                    self.reverse_response_mapping[i].add(k)
                else:
                    self.reverse_response_mapping[i] = set([k])

        for event in G['events']:
            if event in G['includesTo'] and event in G['includesTo'][event]:
                self.self_included.add(event)
                #ignore self includes
                G['includesTo'][event] = G['includesTo'][event].difference(set(event))
            if event in G['excludesTo'] and event in G['excludesTo'][event]:
                self.self_excluded.add(event)
            if event in G['conditionsFor'] and event in G['conditionsFor'][event]:
                self.self_condition.add(event)
            if event in G['milestonesFor'] and event in G['milestonesFor'][event]:
                self.self_milestone.add(event)
            if event in G['responseTo'] and event in G['responseTo'][event]:
                self.self_response.add(event)
                #ignore self response in the mapping
                G['responseTo'][event] = G['responseTo'][event].difference(set(event))
            if event in G['noResponseTo'] and event in G['noResponseTo'][event]:
                self.self_noresponse.add(event)

            self.all_places[event] = set()
            self.all_transitions[event] = set()

            self.conditions_count[event] = len(set(G['conditionsFor'][event])) if event in G['conditionsFor'] else 0
            self.milestones_count[event] = len(set(G['milestonesFor'][event])) if event in G['milestonesFor'] else 0

            self.inc_ex_set[event] = set(G['includesTo'][event] if event in G['includesTo'] else set()).union(set(G['excludesTo'][event] if event in G['excludesTo'] else set()))
            self.resp_no_resp_set[event] = set(G['responseTo'][event] if event in G['responseTo'] else set()).union(set(G['noResponseTo'][event] if event in G['noResponseTo'] else set()))

            self.event_inc_exc_count[event] = len(self.inc_ex_set[event])
            self.event_resp_no_resp_count[event] = len(self.resp_no_resp_set[event])

            self.need_pending_place = self.need_pending_place.union(self.resp_no_resp_set[event])
            self.need_pending_place = self.need_pending_place.union(set(G['milestonesFor'][event]) if event in G['milestonesFor'] else set())

            not_included_become_included = not_included_become_included.intersection(set(G['excludesTo'][event]) if event in G['excludesTo'] else set())
            included_become_excluded = included_become_excluded.intersection(set(G['includesTo'][event]) if event in G['includesTo'] else set())
            inc_exc = inc_exc.union(set(G['includesTo'][event]) if event in G['includesTo'] else set()).union(
                set(G['excludesTo'][event]) if event in G['excludesTo'] else set())

            self.need_executed_place = self.need_executed_place.union(set(G['conditionsFor'][event]) if event in G['conditionsFor'] else set())

            for event2 in G['events']:
                if (event in G['milestonesFor'] and event in G['responseTo'] and event2 in G['responseTo'][event] and event2 in G['milestonesFor'][event]):
                    self.milestone_response_pair[event] = event2

            if event in self.reverse_response_mapping and len(self.reverse_response_mapping[event]) > 1:
                self.multiple_pending = self.multiple_pending.union(set(self.reverse_response_mapping[event]))
            if len(self.inc_ex_set[event].intersection(self.reverse_response_mapping)) > 0:
                self.inc_ex_transport_pp_pe_timed_token.add(event)

        self.need_included_place = not_included_become_included.union(included_become_excluded).union(inc_exc)

        self.inc_ex_pending_set = self.need_included_place.intersection(self.need_pending_place)

    # creation of tapn from dcr
    def create_places_with_marking(self, G, tapn, m=None, timed_dcr=False):
        for event in G['events']:
            # TODO: add the smart filtering of not needing to check if there are no conditions for e
            if event in self.need_executed_place:
                executed_place = PetriNet.Place(f'executed_{event}')
                tapn.places.add(executed_place)
                self.all_places[event].add(executed_place)
                self.execute_places[event] = executed_place
            # TODO: test the smart filtering of not needing to check if included if always included or not excluded etc...
            if event in self.need_included_place:
                included_place = PetriNet.Place(f'included_{event}')
                tapn.places.add(included_place)
                self.all_places[event].add(included_place)
                self.include_places[event] = included_place

            # TODO: test the smart filtering of not needing to check if pending if there are no responses to e and e is not a milestone for another event
            if event in self.need_pending_place:
                if timed_dcr and event in self.reverse_response_mapping:
                    self.pending_places[event] = []
                    self.pending_excluded_places[event] = []
                    self.pp_pe_tuples_by_event_prime[event] = []
                    for re_event in self.reverse_response_mapping[event]:  # G['responseTo'].get(event, set()):
                        pending_place = PetriNet.Place(f'pending_{event}_by_{re_event}')
                        if re_event in G['responseToDeadlines'] and len(G['responseToDeadlines'][re_event]) > 0 and \
                                event in G['responseToDeadlines'][re_event] and G['responseToDeadlines'][re_event][event] > 0:
                            pending_place.properties['ageinvariant'] = G['responseToDeadlines'][re_event][event]
                        tapn.places.add(pending_place)
                        self.all_places[event].add(pending_place)
                        self.pending_places[event].append(pending_place)
                        self.makes_pending_place[re_event] = pending_place
                        self.origin_pending_event[pending_place] = re_event
                        if event in self.inc_ex_pending_set:
                            pending_excl_place = PetriNet.Place(f'pending_excluded_{event}_by_{re_event}')
                            tapn.places.add(pending_excl_place)
                            self.all_places[event].add(pending_excl_place)
                            self.pending_excluded_places[event].append(pending_excl_place)
                            self.makes_pending_excluded_place[re_event] = pending_excl_place
                            self.origin_pending_event[pending_excl_place] = re_event
                            self.pp_pe_tuples_by_event_prime[event].append((pending_place, pending_excl_place))
                else:
                    pending_place = PetriNet.Place(f'pending_{event}')
                    tapn.places.add(pending_place)
                    self.all_places[event].add(pending_place)
                    self.pending_places[event] = pending_place
                    
                    # if event in self.inc_ex_pending_set:
                    #     pex_place = PetriNet.Place(f'pending_excluded_{event}')
                    #     tapn.places.add(pex_place)
                    #     self.all_places[event].add(pex_place)
                    #     self.pending_excluded_places[event] = pex_place

        m = self.create_marking(G, m)
        return tapn, m

    def create_marking(self, G, m):
        # marking
        for event in G['marking']['included']:
            if event in self.need_included_place:
                included_place = self.include_places[event]
                m[included_place] = 1
        for event in G['marking']['executed']:
            if event in self.need_executed_place:
                executed_place = self.execute_places[event]
                m[executed_place] = 1
        for event in G['marking']['pending']:
            if event in self.need_pending_place:
                pending_place = self.pending_places[event]
                if isinstance(pending_place, list):
                    m[pending_place[0]] = 1
                else:
                    m[pending_place] = 1
        return m

    # def map_multiple_pending(self, tapn, event, event_prime):
    #     event_transitions = self.all_transitions[event]
    #     event_prime_pending_by_event_place = self.pending_places[event_prime]  # TODO get the by_event place
    #     event_prime_pending_not_by_event_places = self.pending_places[event_prime].difference(event_prime_pending_by_event_place)
    #     event_prime_pending_excluded_by_event_place = self.pending_excluded_places[event_prime]  # TODO get the by_event place
    #     event_prime_pending_excluded_not_by_event_places = self.pending_excluded_places[event_prime].difference(event_prime_pending_excluded_by_event_place)

    def create_transitions_and_arcs(self, G, tapn: PetriNet, timed_dcr=False):
        # make transitions
        transport_idx = 1
        for event in G['events']:
            ie = self.event_inc_exc_count[event]
            ie = 2 ** ie  # we need 2 transitions to satisfy 1 inclusion/exclusion

            c = self.conditions_count[event]
            c = 3 ** c  # we need 3 transitions to satisfy 1 condition

            r = self.event_resp_no_resp_count[event]
            r = 2 ** r  # we need 2 transitions to satisfy 1 response/no-response

            m = self.milestones_count[event]
            m = 3 ** m  # we need 3 transitions to satisfy 1 milestone

            # this is a sanity check
            n = ie * c * r * m  # need the product of the above transitions in total worst case (each permutation)

            i = 0

            if event in G['marking']['included'] or event in self.need_included_place:
                if n == 1:
                    wts, tapn = self.create_within_event_structure(event, tapn, timed=timed_dcr)  # , pending_by_list=pending_by_list)
                else:
                    # inclusion and exclusions
                    if event in self.inc_ex_set and len(self.inc_ex_set[event]) > 0:
                        if event in self.self_excluded:
                            inc_ex_permutations = [list(zip(self.inc_ex_set[event], x)) for x in itertools.product([0], repeat=len(self.inc_ex_set[event]))]
                        else:
                            inc_ex_permutations = [list(zip(self.inc_ex_set[event], x)) for x in itertools.product([1, 0], repeat=len(self.inc_ex_set[event]))]
                        # for pending inc exc add as many permutations of type to as needed
                        if timed_dcr and event in self.inc_ex_transport_pp_pe_timed_token:
                            idx_of_pending = 0
                            for relation in ['excludesTo', 'includesTo']:
                                if event in G[relation]:
                                    for event_prime in G[relation][event]:
                                        if event_prime in self.inc_ex_pending_set:
                                            for _ in range(len(self.reverse_response_mapping[event_prime])):
                                                inc_ex_permutations.append([(event_prime, 2)])
                    else:
                        inc_ex_permutations = [None]
                    # conditions
                    cond_permutations = [None]
                    if event in G['conditionsFor'] and len(G['conditionsFor'][event]) > 0:
                        if event in self.self_condition:
                            cond_permutations = [list(zip(G['conditionsFor'][event], x)) for x in itertools.product([2], repeat=len(G['conditionsFor'][event]))]
                        else:
                            same = {}
                            for score in range(3):
                                same[score] = set()
                            for event_prime in G['conditionsFor'][event]:
                                if event_prime in self.need_included_place and event_prime in self.need_executed_place:
                                    same[0].add(event_prime)
                                if event_prime in self.need_included_place:
                                    same[1].add(event_prime)
                                if event_prime in self.need_executed_place:
                                    same[2].add(event_prime)

                            temp_cond_permutations = [list(zip(G['conditionsFor'][event], x)) for x in itertools.product([2, 1, 0], repeat=len(G['conditionsFor'][event]))]
                            cp = []
                            for tuples in temp_cond_permutations:
                                include = True
                                for tuple in tuples:
                                    if tuple[0] not in same[tuple[1]]:
                                        include = False
                                if include:
                                    cp.append(tuples)
                            if len(cp) > 0:
                                cond_permutations = cp
                    # responses
                    resp_no_resp_permutations = [None]
                    if event in self.resp_no_resp_set and len(self.resp_no_resp_set[event]) > 0:
                        same = {}
                        for score in range(2):
                            same[score] = set()

                        for event_prime in self.resp_no_resp_set[event]:
                            if event in self.milestone_response_pair and event_prime == self.milestone_response_pair[event]:
                                same[1].add(event_prime)
                            else:
                                same[0].add(event_prime)
                                same[1].add(event_prime)
                        temp_resp_no_resp_permutations = [list(zip(self.resp_no_resp_set[event], x)) for x in itertools.product([1, 0], repeat=len(self.resp_no_resp_set[event]))]
                        rip = []
                        for tuples in temp_resp_no_resp_permutations:
                            include = True
                            for tuple in tuples:
                                if tuple[0] not in same[tuple[1]]:
                                    include = False
                            if include:
                                rip.append(tuples)
                        if len(rip) > 0:
                            resp_no_resp_permutations = rip
                    # responses with time
                    resp_no_resp_permutations_timed = [None]
                    if event in self.resp_no_resp_set and len(self.resp_no_resp_set[event]) > 0:
                        same = {}
                        for score in range(6):
                            same[score] = set()

                        for event_prime in self.resp_no_resp_set[event]:
                            if event in self.milestone_response_pair and event_prime == self.milestone_response_pair[event]:
                                same[4].add(event_prime)
                            else:
                                same[3].add(event_prime)
                                same[4].add(event_prime)
                            same[5].add(event_prime)
                            same[0].add(event_prime)
                            same[1].add(event_prime)
                            same[2].add(event_prime)

                        temp_timed_resp_no_resp_permutations = [list(zip(self.resp_no_resp_set[event], x)) for x in itertools.product(list(range(5, -1, -1)),
                                                                                                                                      repeat=len(self.resp_no_resp_set[event]))]
                        rip = []
                        for tuples in temp_timed_resp_no_resp_permutations:
                            include = True
                            for tuple in tuples:
                                if tuple[0] not in same[tuple[1]]:
                                    include = False
                            if include:
                                rip.append(tuples)
                        if len(rip) > 0:
                            resp_no_resp_permutations_timed = rip
                    # milestones
                    mi_permutations = [None]
                    if event in G['milestonesFor'] and len(G['milestonesFor'][event]) > 0:
                        same = {}
                        for score in range(3):
                            same[score] = set()
                        for event_prime in G['milestonesFor'][event]:
                            if not (event in self.milestone_response_pair and event_prime == self.milestone_response_pair[event]):
                                if event_prime in self.need_included_place and event_prime in self.need_pending_place:
                                    same[0].add(event_prime)
                                if event_prime in self.need_included_place:
                                    same[1].add(event_prime)
                                if event_prime in self.need_pending_place:
                                    same[2].add(event_prime)
                                if event_prime in self.need_pending_place and timed_dcr:
                                    same[2].add(event_prime)

                        temp_mi_permutations = [list(zip(G['milestonesFor'][event], x)) for x in itertools.product([2, 1, 0], repeat=len(G['milestonesFor'][event]))]
                        mip = []
                        for tuples in temp_mi_permutations:
                            include = True
                            for tuple in tuples:
                                if tuple[0] not in same[tuple[1]]:
                                    include = False
                            if include:
                                mip.append(tuples)
                        if len(mip) > 0:
                            mi_permutations = mip

                    idx_of_excluded_pending = 0
                    # all
                    # all_permutations = list(itertools.product(inc_ex_permutations, cond_permutations, resp_no_resp_permutations, mi_permutations))
                    all_permutations = list(itertools.product(inc_ex_permutations, cond_permutations, resp_no_resp_permutations_timed, mi_permutations))
                    # create relation arcs and wihin event structures
                    for in_ex_perm, cond_perm, resp_no_resp_perm, mi_perm in all_permutations:
                        i = i + 1

                        ts, tapn = self.create_within_event_structure(event, tapn, i, timed=timed_dcr)
                        for t in ts:
                            if in_ex_perm:
                                for event_prime, j in in_ex_perm:
                                    included_place_event_prime = self.include_places[event_prime] if event_prime in self.include_places else None
                                    if j == 0: # rule 2
                                        pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                        # this solves exclusion
                                        if event in G['excludesTo'] and event_prime in G['excludesTo'][event]:
                                            if timed_dcr and event_prime in self.inc_ex_pending_set:
                                                for pp_event_prime in self.pending_places[event_prime]:
                                                    inh_arc = pn_utils.add_arc_from_to(pp_event_prime, t, tapn)
                                                    inh_arc.properties['arctype'] = 'inhibitor'
                                        else:
                                            pn_utils.add_arc_from_to(t, included_place_event_prime, tapn)
                                    elif j == 1: # rule 1
                                        # this solves self excludes
                                        t_arc = pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                        t_arc.properties['arctype'] = 'inhibitor'
                                        # this solves inclusion
                                        if event in G['includesTo'] and event_prime in G['includesTo'][event]:
                                            # if the target event does not become excluded only the initial transition needs to include it.
                                            if not self.check_arc_exists(t, included_place_event_prime, tapn):
                                                pn_utils.add_arc_from_to(t, included_place_event_prime, tapn)
                                            # else:
                                            if timed_dcr and event_prime in self.inc_ex_pending_set:
                                                for pe_event_prime in self.pending_excluded_places[event_prime]:
                                                    inh_arc = pn_utils.add_arc_from_to(pe_event_prime, t, tapn)
                                                    inh_arc.properties['arctype'] = 'inhibitor'
                                    elif j == 2: # rule 3
                                        # pending inc exc with time
                                        #TODO: this needs to be extended for untimed and pending excluded place
                                        pp, pe = self.pp_pe_tuples_by_event_prime[event_prime][idx_of_pending]
                                        if event in G['includesTo'] and event_prime in G['includesTo'][event]:
                                            # transport includes
                                            pn_utils.add_arc_from_to(t, included_place_event_prime, tapn)
                                            inh_arc = pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                            inh_arc.properties['arctype'] = 'inhibitor'
                                            t1_arc = pn_utils.add_arc_from_to(pe, t, tapn)
                                            t2_arc = pn_utils.add_arc_from_to(t, pp, tapn)
                                            t1_arc.properties['arctype'] = 'transport'
                                            t2_arc.properties['arctype'] = 'transport'
                                            t1_arc.properties['transportindex'] = transport_idx
                                            t2_arc.properties['transportindex'] = transport_idx
                                            transport_idx = transport_idx + 1

                                        elif event in G['excludesTo'] and event_prime in G['excludesTo'][event]:
                                            # transport excludes
                                            pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                            t1_arc = pn_utils.add_arc_from_to(pp, t, tapn)
                                            t2_arc = pn_utils.add_arc_from_to(t, pe, tapn)
                                            t1_arc.properties['arctype'] = 'transport'
                                            t2_arc.properties['arctype'] = 'transport'
                                            t1_arc.properties['transportindex'] = transport_idx
                                            t2_arc.properties['transportindex'] = transport_idx
                                            transport_idx = transport_idx + 1
                                        idx_of_pending = idx_of_pending + 1

                            if cond_perm:
                                # extra check to see if the condition affected set of event_prime has the same behaviour and can be linked by a single event transition
                                for event_prime, h in cond_perm:  # these are the events_prime that need to interplay with each other or are the same
                                    condition_included_place = self.include_places[event_prime] if event_prime in self.include_places else None
                                    condition_executed_place = self.execute_places[event_prime] if event_prime in self.execute_places else None
                                    if h == 0:  # and not condition_executed_place and not condition_included_place:  # create type 1 of condition connection
                                        # executed place
                                        pn_utils.add_arc_from_to(t, condition_executed_place, tapn)
                                        pn_utils.add_arc_from_to(condition_executed_place, t, tapn)
                                        # included place
                                        t_arc = pn_utils.add_arc_from_to(condition_included_place, t, tapn)
                                        t_arc.properties['arctype'] = 'inhibitor'
                                    elif h == 1:  # and not condition_executed_place and not condition_included_place:  # create type 2 of condition connection
                                        # executed place
                                        t_arc = pn_utils.add_arc_from_to(condition_executed_place, t, tapn)
                                        t_arc.properties['arctype'] = 'inhibitor'
                                        # included place
                                        t_arc = pn_utils.add_arc_from_to(condition_included_place, t, tapn)
                                        t_arc.properties['arctype'] = 'inhibitor'
                                    elif h == 2:  # create type 3 of condition connection
                                        # executed place
                                        # These are transport arcs
                                        transport_arc1 = pn_utils.add_arc_from_to(t, condition_executed_place, tapn)
                                        transport_arc2 = pn_utils.add_arc_from_to(condition_executed_place, t, tapn)
                                        if timed_dcr:
                                            transport_arc1.properties['arctype'] = 'transport'
                                            transport_arc2.properties['arctype'] = 'transport'
                                            transport_arc1.properties['transportindex'] = transport_idx
                                            transport_arc2.properties['transportindex'] = transport_idx
                                            transport_idx = transport_idx + 1
                                            if event in G['conditionsForDelays'] and len(G['conditionsForDelays'][event]) > 0 and \
                                                    event_prime in G['conditionsForDelays'][event] and G['conditionsForDelays'][event][event_prime] > 0:
                                                transport_arc1.properties['agemin'] = G['conditionsForDelays'][event][event_prime]
                                                transport_arc2.properties['agemin'] = G['conditionsForDelays'][event][event_prime]
                                        # included place
                                        pn_utils.add_arc_from_to(t, condition_included_place, tapn)
                                        pn_utils.add_arc_from_to(condition_included_place, t, tapn)
                            if resp_no_resp_perm:
                                for event_prime, r in resp_no_resp_perm:
                                    included_place_event_prime = self.include_places[event_prime] if event_prime in self.include_places else None
                                    pending_place_event_prime = self.pending_places[event_prime] if event_prime in self.pending_places else None
                                    # pending_excluded_place_event_prime = self.pending_excluded_places[event_prime] if event_prime in self.pending_excluded_places else None

                                    # timed response
                                    if isinstance(pending_place_event_prime, list) and event_prime in self.inc_ex_pending_set:
                                        pp_itself = self.makes_pending_place[event]
                                        pe_itself = self.makes_pending_excluded_place[event]
                                        match r:
                                            case 0:
                                                t_arc = pn_utils.add_arc_from_to(pe_itself, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                                # this solves response
                                                if event in G['responseTo'] and event_prime in G['responseTo'][event]:
                                                    # if the target event does not become excluded only the initial transition needs to include it if it exists.
                                                    pn_utils.add_arc_from_to(t, pe_itself, tapn)
                                                # pending excluded others
                                                for pe_others in self.pending_excluded_places[event_prime]:
                                                    if pe_others != pe_itself:
                                                        pe_others_arc = pn_utils.add_arc_from_to(pe_others, t, tapn)
                                                        pe_others_arc.properties['arctype'] = 'inhibitor'
                                                # to included event prime
                                                t_arc = pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                            case 1:
                                                pn_utils.add_arc_from_to(pe_itself, t, tapn)
                                                # this solves no response
                                                if event in G['noResponseTo'] and event_prime in G['noResponseTo'][event]:
                                                    pass
                                                else:
                                                    pn_utils.add_arc_from_to(t, pe_itself, tapn)
                                                # pending excluded others
                                                for pe_others in self.pending_excluded_places[event_prime]:
                                                    if pe_others != pe_itself:
                                                        pe_others_arc = pn_utils.add_arc_from_to(pe_others, t, tapn)
                                                        pe_others_arc.properties['arctype'] = 'inhibitor'
                                                # to included event prime
                                                t_arc = pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                            case 2:
                                                t_arc = pn_utils.add_arc_from_to(pe_itself, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                                pn_utils.add_arc_from_to(t, pe_itself, tapn)
                                                # pending others
                                                for pe_others in self.pending_excluded_places[event_prime]:
                                                    if pe_others != pe_itself:
                                                        pn_utils.add_arc_from_to(pe_others, t, tapn)
                                                # to included event prime
                                                t_arc = pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                            case 3:
                                                t_arc = pn_utils.add_arc_from_to(pp_itself, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                                # this solves response
                                                if event in G['responseTo'] and event_prime in G['responseTo'][event]:
                                                    # if the target event does not become excluded only the initial transition needs to include it if it exists.
                                                    pn_utils.add_arc_from_to(t, pp_itself, tapn)
                                                # pending others
                                                for pp_others in self.pending_places[event_prime]:
                                                    if pp_others != pp_itself:
                                                        pp_others_arc = pn_utils.add_arc_from_to(pp_others, t, tapn)
                                                        pp_others_arc.properties['arctype'] = 'inhibitor'
                                                # to included event prime
                                                pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                                pn_utils.add_arc_from_to(t, included_place_event_prime, tapn)
                                            case 4:
                                                pn_utils.add_arc_from_to(pp_itself, t, tapn)
                                                # this solves no response
                                                if event in G['noResponseTo'] and event_prime in G['noResponseTo'][event]:
                                                    pass
                                                else:
                                                    pn_utils.add_arc_from_to(t, pp_itself, tapn)
                                                # pending others
                                                for pp_others in self.pending_places[event_prime]:
                                                    if pp_others != pp_itself:
                                                        pp_others_arc = pn_utils.add_arc_from_to(pp_others, t, tapn)
                                                        pp_others_arc.properties['arctype'] = 'inhibitor'
                                                # to included event prime
                                                pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                                pn_utils.add_arc_from_to(t, included_place_event_prime, tapn)
                                            case 5:
                                                t_arc = pn_utils.add_arc_from_to(pp_itself, t, tapn)
                                                t_arc.properties['arctype'] = 'inhibitor'
                                                pn_utils.add_arc_from_to(t, pp_itself, tapn)
                                                # pending others
                                                for pp_others in self.pending_places[event_prime]:
                                                    if pp_others != pp_itself:
                                                        pn_utils.add_arc_from_to(pp_others, t, tapn)
                                                # to included event prime
                                                pn_utils.add_arc_from_to(included_place_event_prime, t, tapn)
                                                pn_utils.add_arc_from_to(t, included_place_event_prime, tapn)
                                    else:
                                        # untimed response
                                        if isinstance(pending_place_event_prime, list):
                                            pending_place_event_prime = self.makes_pending_place[event]
                                        if r == 0:
                                            pn_utils.add_arc_from_to(pending_place_event_prime, t, tapn)
                                            # this solves no response
                                            if event in G['noResponseTo'] and event_prime in G['noResponseTo'][event]:
                                                pass
                                            else:
                                                pn_utils.add_arc_from_to(t, pending_place_event_prime, tapn)
                                        elif r == 1:
                                            t_arc = pn_utils.add_arc_from_to(pending_place_event_prime, t, tapn)
                                            t_arc.properties['arctype'] = 'inhibitor'
                                            # this solves response
                                            if event in G['responseTo'] and event_prime in G['responseTo'][event]:
                                                # if the target event does not become excluded only the initial transition needs to include it if it exists.
                                                if not self.check_arc_exists(t, pending_place_event_prime, tapn):
                                                    pn_utils.add_arc_from_to(t, pending_place_event_prime, tapn)
                            if mi_perm:
                                for event_prime, m in mi_perm:
                                    mi_included_place = self.include_places[event_prime] if event_prime in self.include_places else None
                                    mi_pending_place = self.pending_places[event_prime] if event_prime in self.pending_places else None
                                    mi_pending_excluded_place = self.pending_excluded_places[event_prime] if event_prime in self.pending_excluded_places else None

                                    if m == 2:  # create type 3 of milestone connection
                                        # pending place
                                        if isinstance(mi_pending_place, list):
                                            for mi_pp in mi_pending_place:
                                                arc = pn_utils.add_arc_from_to(mi_pp, t, tapn)
                                                arc.properties['arctype'] = 'inhibitor'
                                        else:
                                            arc = pn_utils.add_arc_from_to(mi_pending_place, t, tapn)
                                            arc.properties['arctype'] = 'inhibitor'
                                        # included place
                                        pn_utils.add_arc_from_to(mi_included_place, t, tapn)
                                        pn_utils.add_arc_from_to(t, mi_included_place, tapn)
                                    elif m == 1: # create type 2 of milestone connection
                                        # pending place
                                        if isinstance(mi_pending_place, list):
                                            for mi_pp in mi_pending_place:
                                                arc = pn_utils.add_arc_from_to(mi_pp, t, tapn)
                                                arc.properties['arctype'] = 'inhibitor'
                                            for mi_pe in mi_pending_excluded_place:
                                                arc = pn_utils.add_arc_from_to(mi_pe, t, tapn)
                                                arc.properties['arctype'] = 'inhibitor'
                                        else:
                                            arc = pn_utils.add_arc_from_to(mi_pending_place, t, tapn)
                                            arc.properties['arctype'] = 'inhibitor'
                                        # included place
                                        arc = pn_utils.add_arc_from_to(mi_included_place, t, tapn)
                                        arc.properties['arctype'] = 'inhibitor'
                                    elif m == 0:  # create type 1 of milestone connection
                                        # pending place
                                        if timed_dcr:
                                            mi_pe = mi_pending_excluded_place[idx_of_excluded_pending]
                                            t1_arc = pn_utils.add_arc_from_to(mi_pe, t, tapn)
                                            t2_arc = pn_utils.add_arc_from_to(t, mi_pe, tapn)
                                            t1_arc.properties['arctype'] = 'transport'
                                            t2_arc.properties['arctype'] = 'transport'
                                            t1_arc.properties['transportindex'] = transport_idx
                                            t2_arc.properties['transportindex'] = transport_idx
                                            transport_idx = transport_idx + 1
                                            idx_of_excluded_pending = idx_of_excluded_pending + 1
                                        else:
                                            pn_utils.add_arc_from_to(mi_pending_place, t, tapn)
                                            pn_utils.add_arc_from_to(t, mi_pending_place, tapn)
                                        # included place
                                        arc = pn_utils.add_arc_from_to(mi_included_place, t, tapn)
                                        arc.properties['arctype'] = 'inhibitor'

        return tapn

    def create_within_event_structure(self, event, tapn, i=None, timed=False):  # , pending_by_list=None):
        '''
        creates arcs and transition between places belonging to the same event
        :param event: dcr event
        :param i: index of included excluded tapn structure
        :return:
        '''
        initial_transition_naming = f'Initial_{event}'
        transition_naming = f'{event}'
        if i:
            initial_transition_naming = f'Initial_{event}{i}'
            transition_naming = f'{event}{i}'

        included_place = self.include_places[event] if event in self.include_places else None
        executed_place = self.execute_places[event] if event in self.execute_places else None
        pending_place = self.pending_places[event] if event in self.pending_places else None

        ts = []
        # we repeat the base structure for when e is pending and when e is not pending
        repeat_for_pending = [1, 0]
        if not pending_place:
            repeat_for_pending = [0]
        if timed and isinstance(pending_place, list):
            # z = 0
            for x in repeat_for_pending:
                if x == 0:
                    if event in self.need_executed_place and event not in self.self_condition:
                        initial_transition = PetriNet.Transition(initial_transition_naming,
                                                                 f'{initial_transition_naming}_label')
                        tapn.transitions.add(initial_transition)
                    # this should be the mandatory always created event transition
                    transition = PetriNet.Transition(transition_naming, f'{transition_naming}_label')
                    tapn.transitions.add(transition)
                    # 03.09 change
                    for pp in pending_place:
                        if event in self.need_executed_place:
                            pi_arc = pn_utils.add_arc_from_to(pp, initial_transition, tapn)
                            pi_arc.properties['arctype'] = 'inhibitor'
                        p_arc = pn_utils.add_arc_from_to(pp, transition, tapn)
                        p_arc.properties['arctype'] = 'inhibitor'
                    if included_place:
                        if event in self.need_executed_place and event not in self.self_condition:
                            pn_utils.add_arc_from_to(included_place, initial_transition, tapn)
                            if event not in self.self_excluded:
                                pn_utils.add_arc_from_to(initial_transition, included_place, tapn)

                        pn_utils.add_arc_from_to(included_place, transition, tapn)
                        if event not in self.self_excluded:
                            pn_utils.add_arc_from_to(transition, included_place, tapn)

                    if executed_place and event not in self.self_condition:
                        if event in self.need_executed_place:
                            arc = pn_utils.add_arc_from_to(executed_place, initial_transition, tapn)
                            arc.properties['arctype'] = 'inhibitor'
                            pn_utils.add_arc_from_to(initial_transition, executed_place, tapn)

                        pn_utils.add_arc_from_to(executed_place, transition, tapn)
                        pn_utils.add_arc_from_to(transition, executed_place, tapn)

                    self.all_transitions[event].add(transition)
                    ts.append(transition)
                    if event in self.need_executed_place and event not in self.self_condition:
                        self.all_transitions[event].add(initial_transition)
                        ts.append(initial_transition)

                elif x == 1:  # this is pending
                    for pp in pending_place:
                        if event in self.need_executed_place and event not in self.self_condition:
                            initial_transition = PetriNet.Transition(f'{initial_transition_naming}_pend_by_{self.origin_pending_event[pp]}',
                                                                     f'{initial_transition_naming}_pend_by_{self.origin_pending_event[pp]}_label')
                            tapn.transitions.add(initial_transition)
                        transition = PetriNet.Transition(f'{transition_naming}_pend_by_{self.origin_pending_event[pp]}',
                                                         f'{transition_naming}_pend_by_{self.origin_pending_event[pp]}_label')
                        tapn.transitions.add(transition)
                        # 03.09 change
                        if event in self.need_executed_place:
                            pn_utils.add_arc_from_to(pp, initial_transition, tapn)
                        pn_utils.add_arc_from_to(pp, transition, tapn)

                        if included_place:
                            if event in self.need_executed_place and event not in self.self_condition:
                                pn_utils.add_arc_from_to(included_place, initial_transition, tapn)
                                if event not in self.self_excluded:
                                    pn_utils.add_arc_from_to(initial_transition, included_place, tapn)

                            pn_utils.add_arc_from_to(included_place, transition, tapn)
                            if event not in self.self_excluded:
                                pn_utils.add_arc_from_to(transition, included_place, tapn)

                        if executed_place and event not in self.self_condition:
                            if event in self.need_executed_place:
                                arc = pn_utils.add_arc_from_to(executed_place, initial_transition, tapn)
                                arc.properties['arctype'] = 'inhibitor'
                                pn_utils.add_arc_from_to(initial_transition, executed_place, tapn)

                            pn_utils.add_arc_from_to(executed_place, transition, tapn)
                            pn_utils.add_arc_from_to(transition, executed_place, tapn)

                        self.all_transitions[event].add(transition)
                        ts.append(transition)
                        if event in self.need_executed_place and event not in self.self_condition:
                            self.all_transitions[event].add(initial_transition)
                            ts.append(initial_transition)
                # if pp:
                # for pp in pending_place:
                #     if x == 1:
                #         if event in self.need_executed_place:
                #             pn_utils.add_arc_from_to(pp, initial_transition, tapn)
                #         pn_utils.add_arc_from_to(pp, transition, tapn)
                #     elif x == 0:
                #         if event in self.need_executed_place:
                #             pi_arc = pn_utils.add_arc_from_to(pp, initial_transition, tapn)
                #             pi_arc.properties['arctype'] = 'inhibitor'
                #         p_arc = pn_utils.add_arc_from_to(pp, transition, tapn)
                #         p_arc.properties['arctype'] = 'inhibitor'
                # z = z + 1
        else:
            for x in repeat_for_pending:
                if x == 0:
                    if event in self.need_executed_place and event not in self.self_condition:
                        initial_transition = PetriNet.Transition(initial_transition_naming, f'{initial_transition_naming}_label')
                        tapn.transitions.add(initial_transition)
                    # this should be the mandatory always created event transition
                    transition = PetriNet.Transition(transition_naming, f'{transition_naming}_label')
                    tapn.transitions.add(transition)
                elif x == 1:  # this is pending
                    if event in self.need_executed_place and event not in self.self_condition:
                        initial_transition = PetriNet.Transition(f'{initial_transition_naming}_pend', f'{initial_transition_naming}_pend_label')
                        tapn.transitions.add(initial_transition)
                    transition = PetriNet.Transition(f'{transition_naming}_pend', f'{transition_naming}_pend_label')
                    tapn.transitions.add(transition)

                if included_place:
                    if event in self.need_executed_place and event not in self.self_condition:
                        pn_utils.add_arc_from_to(included_place, initial_transition, tapn)
                        if event not in self.self_excluded:
                            pn_utils.add_arc_from_to(initial_transition, included_place, tapn)

                    pn_utils.add_arc_from_to(included_place, transition, tapn)
                    if event not in self.self_excluded:
                        pn_utils.add_arc_from_to(transition, included_place, tapn)

                if executed_place and event not in self.self_condition:
                    if event in self.need_executed_place:
                        arc = pn_utils.add_arc_from_to(executed_place, initial_transition, tapn)
                        arc.properties['arctype'] = 'inhibitor'
                        pn_utils.add_arc_from_to(initial_transition, executed_place, tapn)

                    pn_utils.add_arc_from_to(executed_place, transition, tapn)
                    pn_utils.add_arc_from_to(transition, executed_place, tapn)

                self.all_transitions[event].add(transition)
                ts.append(transition)
                if event in self.need_executed_place and event not in self.self_condition:
                    self.all_transitions[event].add(initial_transition)
                    ts.append(initial_transition)
                if pending_place:
                    if x == 1:
                        if event in self.need_executed_place:
                            pn_utils.add_arc_from_to(pending_place, initial_transition, tapn)
                        pn_utils.add_arc_from_to(pending_place, transition, tapn)
                    elif x == 0:
                        if event in self.need_executed_place:
                            pi_arc = pn_utils.add_arc_from_to(pending_place, initial_transition, tapn)
                            pi_arc.properties['arctype'] = 'inhibitor'
                        p_arc = pn_utils.add_arc_from_to(pending_place, transition, tapn)
                        p_arc.properties['arctype'] = 'inhibitor'

        return ts, tapn

    def dcr2tapn(self, G, tapn_path="../models/petri.pnml"):
        self.prepare_helper_data_structure(G)
        tapn = PetriNet("Dcr2Tapn")
        m = Marking()

        timed_dcr = False
        if ('conditionsForDelays' in G and len(G['conditionsForDelays']) > 0) or ('responseToDeadlines' in G and len(G['responseToDeadlines']) > 0):
            timed_dcr = True

        tapn, m = self.create_places_with_marking(G, tapn, m, timed_dcr=timed_dcr)
        tapn = self.create_transitions_and_arcs(G, tapn, timed_dcr=timed_dcr)

        pnml_exporter.apply(tapn, m, tapn_path, variant=pnml_exporter.TAPN)
        return tapn


if __name__ == '__main__':
    d2p = Dcr2PetriTransport()

    graph = {
        'events': {'A', 'B', 'C'},
        'conditionsFor': {'A': {'B'}},
        'milestonesFor': {},
        'responseTo': {'C': {'B'}, 'A': {'B'}},
        'noResponseTo': {},
        'includesTo': {'A': {'B', 'C'}},
        'excludesTo': {'B': {'C'}},
        'conditionsForDelays': {'A': {'B': 2}},
        'responseToDeadlines': {'C': {'B': 5}, 'A': {'B': 7}},
        'marking': {'executed': set(),
                    'included': {'A'},
                    'pending': set()
                    }
    }

    tapn = d2p.dcr2tapn(graph, tapn_path="../models/petri.pnml")
