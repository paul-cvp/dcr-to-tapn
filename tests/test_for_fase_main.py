import unittest

from src.dcr_to_petri_fase import Dcr2PetriTransport
from src import util

class FaseTestCase(unittest.TestCase):

    def test_paper_example(self):
        '''
        
        '''
        G = {
            'events': {'EditPaymentInfo','AddOrder','Checkout'},
            'conditionsFor': {'Checkout':{'EditPaymentInfo'}},
            'milestonesFor': {},
            'responseTo': {'AddOrder':{'Checkout'}},
            'noResponseTo': {},
            'includesTo': {'AddOrder':{'Checkout'},'Checkout':{'AddOrder'}},
            'excludesTo': {'Checkout':{'Checkout'},'AddOrder':{'AddOrder'}},
            'marking': {'executed': {},
                        'included': {'EditPaymentInfo','AddOrder'},
                        'pending': {}
                        }
        }
        tapn_path = '../models/fase/paper_example_no_cancel.tapn'
        d2p = Dcr2PetriTransport()

        tapn = d2p.dcr2tapn(G, tapn_path)

        p,t,a = util.get_expected_places_transitions_arcs(G)
        self.assertEqual(p,len(tapn.places))
        self.assertEqual(t,len(tapn.transitions))
        self.assertEqual(a,len(tapn.arcs))

if __name__ == '__main__':

    unittest.main()