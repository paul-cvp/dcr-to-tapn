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
from enum import Enum

from pm4py.objects.conversion.dcr.variants import to_inhibitor_net, to_timed_arc_petri_net
from pm4py.objects.dcr.timed.obj import TimedDcrGraph
from pm4py.util import exec_utils


class Variants(Enum):
    TO_INHIBITOR_NET = to_inhibitor_net
    TO_TIMED_ARC_PETRI_NET = to_timed_arc_petri_net


DEFAULT_VARIANT = Variants.TO_INHIBITOR_NET
TO_INHIBITOR_NET = Variants.TO_INHIBITOR_NET
TO_TIMED_ARC_PETRI_NET = Variants.TO_TIMED_ARC_PETRI_NET


def apply(obj, variant=DEFAULT_VARIANT, parameters=None):
    if parameters is None:
        parameters = {}
    if isinstance(obj, TimedDcrGraph):
        obj = obj.obj_to_template()
    return exec_utils.get_variant(variant).apply(obj, parameters=parameters)
