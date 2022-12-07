from pm4py.util import constants


def parse_element(curr_el, parent, dcr):
    tag = curr_el.tag.lower()
    match tag:
        case 'event':
            id = curr_el.get('id')
            if id:
                match parent.tag:
                    case 'events':
                        dcr['events'].add(id)
                    case 'included' | 'executed':
                        dcr['marking'][parent.tag].add(id)
                    case 'pendingResponses':
                        dcr['marking']['pending'].add(id)
                    case _:
                        pass
        case 'label':
            id = curr_el.get('id')
            dcr['labels'].add(id)
        case 'labelMapping':
            eventId = curr_el.get('eventId')
            labelId = curr_el.get('labelId')
            dcr['labelMapping'].add((eventId, labelId))
        case 'condition':
            event = curr_el.get('sourceId')
            event_prime = curr_el.get('targetId')
            filter_level = curr_el.get('filterLevel')
            description = curr_el.get('description').strip()  # might have an ISO format duration
            delay = curr_el.get('time')
            groups = curr_el.get('groups')
            if not dcr['conditionsFor'].__contains__(event_prime):
                dcr['conditionsFor'][event_prime] = set()
            dcr['conditionsFor'][event_prime].add(event)

            if delay:
                if not dcr['conditionsForDelays'].__contains__(event_prime):
                    dcr['conditionsForDelays'][event_prime] = set()
                import isodate
                delay_days = isodate.parse_duration(delay).days
                dcr['conditionsForDelays'][event_prime].add((event, delay_days))

        case 'response':
            event = curr_el.get('sourceId')
            event_prime = curr_el.get('targetId')
            filter_level = curr_el.get('filterLevel')
            description = curr_el.get('description').strip()  # might have an ISO format duration
            deadline = curr_el.get('time')
            groups = curr_el.get('groups')
            if not dcr['responseTo'].__contains__(event):
                dcr['responseTo'][event] = set()
            dcr['responseTo'][event].add(event_prime)

            if deadline:
                if not dcr['responseToDeadlines'].__contains__(event):
                    dcr['responseToDeadlines'][event] = set()
                import isodate
                deadline_days = isodate.parse_duration(deadline).days
                dcr['responseToDeadlines'][event].add((event_prime, deadline_days))

        case 'include' | 'exclude' | 'noresponse':
            event = curr_el.get('sourceId')
            event_prime = curr_el.get('targetId')
            filter_level = curr_el.get('filterLevel')
            description = curr_el.get('description').strip()  # might have an ISO format duration
            deadline = curr_el.get('time')
            groups = curr_el.get('groups')
            if not dcr[f'{tag}sTo'].__contains__(event):
                dcr[f'{tag}sTo'][event] = set()
            dcr[f'{tag}sTo'][event].add(event_prime)
        case 'milestone':
            event = curr_el.get('sourceId')
            event_prime = curr_el.get('targetId')
            filter_level = curr_el.get('filterLevel')
            description = curr_el.get('description').strip()  # might have an ISO format duration
            deadline = curr_el.get('time')
            groups = curr_el.get('groups')
            if not dcr[f'{tag}sFor'].__contains__(event_prime):
                dcr[f'{tag}sFor'][event_prime] = set()
            dcr[f'{tag}sFor'][event_prime].add(event)
        case _:
            pass
    for child in curr_el:
        dcr = parse_element(child, curr_el, dcr)

    return dcr


def import_xml_tree_from_root(root):
    dcr = {
        'events': set(),
        'labels': set(),
        'labelMapping': set(),
        'conditionsFor': {},  # this should be a dict with events as keys and sets as values
        'milestonesFor': {},
        'responseTo': {},
        'noResponseTo': {},
        'includesTo': {},
        'excludesTo': {},
        'conditionsForDelays': {}, # this should be a dict with events as keys and tuples as values
        'responseToDeadlines': {},
        'marking': {'executed': set(),
                    'included': set(),
                    'pending': set()
                    }
    }

    return parse_element(root, None, dcr)


def apply(path, parameters=None):
    if parameters is None:
        parameters = {}

    from lxml import etree, objectify

    parser = etree.XMLParser(remove_comments=True)
    xml_tree = objectify.parse(path, parser=parser)

    return import_xml_tree_from_root(xml_tree.getroot())


def import_from_string(dcr_string, parameters=None):
    if parameters is None:
        parameters = {}

    if type(dcr_string) is str:
        dcr_string = dcr_string.encode(constants.DEFAULT_ENCODING)

    from lxml import etree, objectify

    parser = etree.XMLParser(remove_comments=True)
    root = objectify.fromstring(dcr_string, parser=parser)

    return import_xml_tree_from_root(root)
