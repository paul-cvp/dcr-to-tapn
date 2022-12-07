
class Preoptimizer(object):
    need_included_place = set()
    need_executed_place = set()
    need_pending_place = set()
    need_pending_excluded_place = set()
    un_executable_events = set()

    def pre_optimize_based_on_dcr_behaviour(self, G):
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

        need_executed_place = condition_events #set(G['marking']['executed']).union(condition_events)

        need_pending_place = set(G['marking']['pending']).union(response_events)
        need_pending_excluded_place = need_pending_place.intersection(need_included_place)

        self.preoptimizer.need_included_place = need_included_place
        self.preoptimizer.need_executed_place = need_executed_place
        self.preoptimizer.need_pending_place = need_pending_place
        self.preoptimizer.need_pending_excluded_place = need_pending_excluded_place
        self.preoptimizer.un_executable_events = unexecutable_events