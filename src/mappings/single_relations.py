from pm4py.objects.petri_net.obj import *
from pm4py.objects.petri_net.utils import petri_utils as pn_utils

from src import util


class SingleRelations(object):

    def __init__(self, helper_struct, mapping_exceptions) -> None:
        self.helper_struct = helper_struct
        self.mapping_exceptions = mapping_exceptions

    def create_include_pattern(self, event, event_prime, tapn) -> PetriNet:
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
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn)
        # copy 2
        if inc_place_e_prime and pend_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
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
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

        # copy 2
        if inc_place_e_prime and pend_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
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
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(t, pend_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
        # copy 2
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excl_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

        # copy 3
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
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
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                    pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn)
        # copy 2
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excl_place_e_prime, t, tapn, type='inhibitor')

        # copy 3
        if inc_place_e_prime and pend_excl_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
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
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(exec_place_e_prime, t, tapn, type='inhibitor')

        # copy 2
        if inc_place_e_prime and exec_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)
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
        if inc_place_e_prime or pend_excluded_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn, type='inhibitor')

        # copy 2
        if inc_place_e_prime or pend_excluded_place_e_prime:
            for delta in range(len_delta):
                tapn, ts = util.create_event_pattern_transitions_and_arcs(tapn, event, self.helper_struct, self.mapping_exceptions)
                new_transitions.extend(ts)
                for t in ts:
                    tapn, t = util.map_existing_transitions_of_copy_0(delta, copy_0, t, tapn)

                    pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn, type='inhibitor')

                    pn_utils.add_arc_from_to(t, pend_excluded_place_e_prime, tapn)
                    pn_utils.add_arc_from_to(pend_excluded_place_e_prime, t, tapn)


        # copy 0
        if pend_place_e_prime:
            for t in copy_0:
                pn_utils.add_arc_from_to(t, inc_place_e_prime, tapn)
                pn_utils.add_arc_from_to(inc_place_e_prime, t, tapn)

                pn_utils.add_arc_from_to(pend_place_e_prime, t, tapn, type='inhibitor')

        self.helper_struct[event]['transitions'].extend(new_transitions)
        return tapn
