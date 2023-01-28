#TODO.
# for now run the src/dcr_to_petri_readable.py file
from copy import deepcopy
import itertools
from itertools import combinations

from src.dcr_to_petri_readable import Dcr2PetriTransport
from pm4py.objects.dcr.importer import importer as dcr_importer

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
        res_path = f"models/all/{file_name}"
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


if __name__ == '__main__':
    # uncomment which one you need and read more in the function about what it does
    run_all()  # runs all possible 1,2 event and relation combinations (see the method definition and comments above)
    # run_specific_dcr()  # runs a user defined dcr graph written as a python dict (see the method definition and comments above)
    #run_dcrxml_files()  # runs on specific dcrxml files (see the method definition and comments above)
    print('[i] Done!')