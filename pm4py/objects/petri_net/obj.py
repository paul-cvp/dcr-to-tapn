'''
    This file is part of PM4Py (More Info: https://pm4py.fit.fraunhofer.de).

    PM4Py is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    PM4Py is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with PM4Py.  If not, see <https://www.gnu.org/licenses/>.
'''
from collections import Counter
from copy import deepcopy
from typing import Any


class PetriNet(object):
    class Place(object):

        def __init__(self, name, in_arcs=None, out_arcs=None, properties=None):
            self.__name = name
            self.__in_arcs = set() if in_arcs is None else in_arcs
            self.__out_arcs = set() if out_arcs is None else out_arcs
            self.__properties = dict() if properties is None else properties

        def __set_name(self, name):
            self.__name = name

        def __get_name(self):
            return self.__name

        def __get_out_arcs(self):
            return self.__out_arcs

        def __get_in_arcs(self):
            return self.__in_arcs

        def __get_properties(self):
            return self.__properties

        def __repr__(self):
            return str(self.name)

        def __str__(self):
            return self.__repr__()

        def __eq__(self, other):
            # keep the ID for now in places
            return id(self) == id(other)

        def __hash__(self):
            # keep the ID for now in places
            return id(self)

        def __deepcopy__(self, memodict={}):
            if id(self) in memodict:
                return memodict[id(self)]
            new_place = PetriNet.Place(self.name, properties=self.properties)
            memodict[id(self)] = new_place
            for arc in self.in_arcs:
                new_arc = deepcopy(arc, memo=memodict)
                new_place.in_arcs.add(new_arc)
            for arc in self.out_arcs:
                new_arc = deepcopy(arc, memo=memodict)
                new_place.out_arcs.add(new_arc)
            return new_place

        name = property(__get_name, __set_name)
        in_arcs = property(__get_in_arcs)
        out_arcs = property(__get_out_arcs)
        properties = property(__get_properties)

    class Transition(object):

        def __init__(self, name, label=None, in_arcs=None, out_arcs=None, properties=None):
            self.__name = name
            self.__label = None if label is None else label
            self.__in_arcs = set() if in_arcs is None else in_arcs
            self.__out_arcs = set() if out_arcs is None else out_arcs
            self.__properties = dict() if properties is None else properties

        def __set_name(self, name):
            self.__name = name

        def __get_name(self):
            return self.__name

        def __set_label(self, label):
            self.__label = label

        def __get_label(self):
            return self.__label

        def __get_out_arcs(self):
            return self.__out_arcs

        def __get_in_arcs(self):
            return self.__in_arcs

        def __get_properties(self):
            return self.__properties

        def __repr__(self):
            if self.label is None:
                return "("+str(self.name)+", None)"
            else:
                return "("+str(self.name)+", '"+str(self.label)+"')"

        def __str__(self):
            return self.__repr__()

        def __eq__(self, other):
            # keep the ID for now in transitions
            return id(self) == id(other)

        def __hash__(self):
            # keep the ID for now in transitions
            return id(self)

        def __deepcopy__(self, memodict={}):
            if id(self) in memodict:
                return memodict[id(self)]
            new_trans = PetriNet.Transition(self.name, self.label, properties=self.properties)
            memodict[id(self)] = new_trans
            for arc in self.in_arcs:
                new_arc = deepcopy(arc, memo=memodict)
                new_trans.in_arcs.add(new_arc)
            for arc in self.out_arcs:
                new_arc = deepcopy(arc, memo=memodict)
                new_trans.out_arcs.add(new_arc)
            return new_trans

        name = property(__get_name, __set_name)
        label = property(__get_label, __set_label)
        in_arcs = property(__get_in_arcs)
        out_arcs = property(__get_out_arcs)
        properties = property(__get_properties)

    class Arc(object):

        def __init__(self, source, target, weight=1, properties=None):
            if type(source) is type(target):
                raise Exception('Petri nets are bipartite graphs!')
            self.__source = source
            self.__target = target
            self.__weight = weight
            self.__properties = dict() if properties is None else properties

        def __get_source(self):
            return self.__source

        def __get_target(self):
            return self.__target

        def __set_weight(self, weight):
            self.__weight = weight

        def __get_weight(self):
            return self.__weight

        def __get_properties(self):
            return self.__properties

        def __repr__(self):
            source_rep = repr(self.source)
            target_rep = repr(self.target)
            return source_rep+"->"+target_rep

        def __str__(self):
            return self.__repr__()

        def __hash__(self):
            return id(self)

        def __eq__(self, other):
            # same_type = False
            # if 'arctype' in other.properties and 'arctype' in self.properties:
            #     same_type = self.properties['arctype'] == other.properties['arctype']

            return self.source == other.source and self.target == other.target  # and same_type

        def __deepcopy__(self, memodict={}):
            if id(self) in memodict:
                return memodict[id(self)]
            new_source = memodict[id(self.source)] if id(self.source) in memodict else deepcopy(self.source,
                                                                                                memo=memodict)
            new_target = memodict[id(self.target)] if id(self.target) in memodict else deepcopy(self.target,
                                                                                                memo=memodict)
            memodict[id(self.source)] = new_source
            memodict[id(self.target)] = new_target
            new_arc = PetriNet.Arc(new_source, new_target, weight=self.weight, properties=self.properties)
            memodict[id(self)] = new_arc
            return new_arc

        source = property(__get_source)
        target = property(__get_target)
        weight = property(__get_weight, __set_weight)
        properties = property(__get_properties)

    def __init__(self, name=None, places=None, transitions=None, arcs=None, properties=None):
        self.__name = "" if name is None else name
        self.__places = set() if places is None else places
        self.__transitions = set() if transitions is None else transitions
        self.__arcs = set() if arcs is None else arcs
        self.__properties = dict() if properties is None else properties

        self.__arc_matrix = {}

    def __get_arc_matrix(self):
        return self.__arc_matrix

    def __get_name(self):
        return self.__name

    def __set_name(self, name):
        self.__name = name

    def __get_places(self):
        return self.__places

    def __get_transitions(self):
        return self.__transitions

    def __get_arcs(self):
        return self.__arcs

    def __get_properties(self):
        return self.__properties

    def __hash__(self):
        ret = 0
        for p in self.places:
            ret += hash(p)
            ret = ret % 479001599
        for t in self.transitions:
            ret += hash(t)
            ret = ret % 479001599
        return ret

    def __eq__(self, other):
        # for the Petri net equality keep the ID for now
        return id(self) == id(other)

    def __deepcopy__(self, memodict={}):
        from pm4py.objects.petri_net.utils.petri_utils import add_arc_from_to
        this_copy = PetriNet(self.name)
        memodict[id(self)] = this_copy
        for place in self.places:
            place_copy = PetriNet.Place(place.name, properties=place.properties)
            this_copy.places.add(place_copy)
            memodict[id(place)] = place_copy
        for trans in self.transitions:
            trans_copy = PetriNet.Transition(trans.name, trans.label, properties=trans.properties)
            this_copy.transitions.add(trans_copy)
            memodict[id(trans)] = trans_copy
        for arc in self.arcs:
            add_arc_from_to(memodict[id(arc.source)], memodict[id(arc.target)], this_copy, weight=arc.weight)
        return this_copy

    def __repr__(self):
        ret = ["places: ["]
        places_rep = []
        for place in self.places:
            places_rep.append(repr(place))
        places_rep.sort()
        ret.append(" " + ", ".join(places_rep) + " ")
        ret.append("]\ntransitions: [")
        trans_rep = []
        for trans in self.transitions:
            trans_rep.append(repr(trans))
        trans_rep.sort()
        ret.append(" " + ", ".join(trans_rep) + " ")
        ret.append("]\narcs: [")
        arcs_rep = []
        for arc in self.arcs:
            arcs_rep.append(repr(arc))
        arcs_rep.sort()
        ret.append(" " + ", ".join(arcs_rep) + " ")
        ret.append("]")
        return "".join(ret)

    def __str__(self):
        return self.__repr__()

    name = property(__get_name, __set_name)
    places = property(__get_places)
    transitions = property(__get_transitions)
    arcs = property(__get_arcs)
    properties = property(__get_properties)
    arc_matrix = property(__get_arc_matrix)

class Token(object):

    def __init__(self,place:PetriNet.Place = None, age:int = None) -> None:
        self.__place = place
        self.__age = 0 if age is None else age

    def __get_place(self):
        return self.__place

    def __set_place(self, place:PetriNet.Place):
        self.__name = place

    def __get_age(self):
        return self.__age

    def __set_age(self, age):
        self.__age = age

    place = property(__get_place, __set_place)
    age = property(__get_age, __set_age)

class Marking(Counter):
    pass

    def __hash__(self):
        r = 0
        for p in self.items():
            r += 31 * hash(p[0]) * p[1]
        return r

    def __eq__(self, other):
        if not self.keys() == other.keys():
            return False
        for p in self.keys():
            if other.get(p) != self.get(p):
                return False
        return True

    def __le__(self, other):
        if not self.keys() <= other.keys():
            return False
        for p in self.keys():
            if other.get(p) < self.get(p):
                return False
        return True

    def __add__(self, other):
        m = Marking()
        for p in self.items():
            m[p[0]] = p[1]
        for p in other.items():
            m[p[0]] += p[1]
        return m

    def __sub__(self, other):
        m = Marking()
        for p in self.items():
            m[p[0]] = p[1]
        for p in other.items():
            m[p[0]] -= p[1]
            if m[p[0]] == 0:
                del m[p[0]]
        return m

    def __repr__(self):
        return str([str(p.name) + ":" + str(self.get(p)) for p in sorted(list(self.keys()), key=lambda x: x.name)])

    def __str__(self):
        return self.__repr__()

    def __deepcopy__(self, memodict={}):
        marking = Marking()
        memodict[id(self)] = marking
        for place in self:
            place_occ = self[place]
            new_place = memodict[id(place)] if id(place) in memodict else PetriNet.Place(place.name, properties=place.properties)
            marking[new_place] = place_occ
        return marking

class TimeMarking(dict):
    # for each place there is a set of tokens with an age

    def __init__(self) -> None:
        super().__init__()

    def __setitem__(self, k: PetriNet.Place, v: Any) -> None:
        if not k in self.keys():
            self[k] = set()
        if isinstance(v, Token):
            self[k].add(v)
        elif isinstance(v,int):
            self[k].add(Token(k,v))
        elif isinstance(v,(int,int)):
            for i in v[0]:
                self[k].add(Token(k,v[1]))

    def __getitem__(self, k: PetriNet.Place) -> set():
        return super().__getitem__(k)

    def add_token_with_age(self,t:Token,place:PetriNet.Place,age=0):
        if t:
            token = t
            place = t.place
        else:
            token = Token(place,age)
        if not place in self.keys():
            self[place] = set()
        self[place].add(token)
        return token

    def add_delay(self,duration=1):
        for places in self.keys():
            for k in self[places]:
                self[k].age += duration

    def remove_token_from_place(self,place,token):
        self[place].remove(token)
        return token

    def move_token(self,place_from,place_to,token,transport=False):
        t = self.remove_token_from_place(place_from,token)
        if transport:
            t.place = place_to
        else:
            t.place = place_to
            t.age = 0
        self.add_token_with_age(t)
