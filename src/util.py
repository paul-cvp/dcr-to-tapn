
def get_expected_places_transitions_arcs(G):
    # 3^(conditions + milestones) * 2^((inc+exc)+(resp+no_resp))*2 for each event in relations
    expected_transitions = 0
    # 3*no of events
    expected_places = 4* len(G['events'])
    # arcs:
    #   - events * 12
    #   - conditions * 9
    #   - milestones * 8
    #   - responses * 2
    #   - noResponses * 2
    #   - includes * 2
    #   - exludes * 2
    expected_arcs = 0

    for event in G['events']:
        expected_transitions += ((3 ** (len(G['conditionsFor'][event]) if event in G['conditionsFor'] else 0 +
                                len(G['milestonesFor'][event]) if event in G['milestonesFor'] else 0)) *
                                 (3 ** ((len(G['includesTo'][event]) if event in G['includesTo'] else 0 +
                                len(G['excludesTo'][event]) if event in G['excludesTo'] else 0)) *
                                  (4 ** (len(G['responseTo'][event]) if event in G['responseTo'] else 0 +
                                len(G['noResponseTo'][event]) if event in G['noResponseTo'] else 0)))) * 4

        expected_arcs += 2 ^ ((3 ^ (len(set(G['includesTo'][event] if event in G['includesTo'] else set()).union(
            set(G['excludesTo'][event] if event in G['excludesTo'] else set()))))) *
                              (4 ^ (len(set(G['responseTo'][event] if event in G['responseTo'] else set()).union(
                                  set(G['noResponseTo'][event] if event in G['noResponseTo'] else set()))))) *
                              (3 ^ ((len(set(G['conditionsFor'][event])) if event in G['conditionsFor'] else 0))) *
                              (3 ^ ((len(set(G['milestonesFor'][event])) if event in G['milestonesFor'] else 0))))

    expected_arcs += len(G['events']) * 24
    return expected_places, expected_transitions, expected_arcs