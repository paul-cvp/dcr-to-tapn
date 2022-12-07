from enum import Enum
from collections import Counter

class DCR(object):

    class Marking(Counter):

        def __init__(self, included, executed, pending) -> None:
            self.__included = included
            self.__executed = executed
            self.__pending = pending
            super().__init__()

    class Event(object):

        def __init__(self, id, label) -> None:
            self.__id = id
            self.__label = label

    class Rule(object):

        def __init__(self, type, event, event_prime) -> None:
            self.__type = type
            self.__event = event
            self.__event_prime = event_prime

    def __init__(self, events, rules, marking) -> None:
        self.__events = events
        self.__rules = rules
        self.__marking = marking


