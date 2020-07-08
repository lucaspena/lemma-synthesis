from lemsynth_utils import *

from z3 import *

# This function takes in a string denoting the sort of which we want to create a set
# Note that this function just returns the sort
def createSetSort(sort_string):
    if sort_string == 'int':
        int_set_sort = SetSort(IntSort())
        return int_set_sort
    else:
        raise ValueError('Only integer sets supported')

# This function takes in a variable name, its sort (a set) and creates the a z3py const of that name with that sort
# It is a special case of a function that exists in lemsynth_utils
def createSetVar(name, sort):
    return createSortVar(name, sort)

# Given a set sort, returns the sort of its elements
def getElementType(set_sort):
    return set_sort.domain()

# Returns an empty set of the appropriate sort
def getSortEmptySet(set_sort):
    element_sort = getElementType(set_sort)
    sort_empty_set = EmptySet(element_sort)
    return sort_empty_set

# Returns the universal set of the appropriate sort
def getSortUniversalSet(set_sort):
    element_sort = getElementTye(set_sort)
    sort_universal_set = FullSet(element_sort)
    return sort_universal_set


# Given a python set, returns the corresponding z3py set constant (this constant is explicitly constructed)
# This is useful in giving constraints to the big model encoding from the true models, which contain python sets
# The function explicitly asks for the sort of its elements, as we might encode many sorts using the same python representation, for example: length as well as keys represented by integers
# An attempt to disambugiate in the future could get the implementation more towards a better python encoding/representation for various sorts that we use
def getZ3SetConstEncoding(element_sort, python_set):
    if element_sort == 'int':
        z3_set = EmptySet(IntSort())
    else:
        raise ValueError('Only IntSort sets supported.')
    # The assumption is that python_set is a list or a set in python
    # Therefore, one can iterate over it
    for elem in python_set:
        # UNDESIRABLE: the elements added are expected to be only intergers or booleans, so using 'elem' in set add is ok at the moment
        # What really needs to be done is to get the appropriate Z3ConstEncoding for the python constant held in 'elem' and use that in the set add
        # TODO: fix this issue
        z3_set = SetAdd(z3_set, elem)
    return z3_set

# This function is not needed now because there is no current utility for converting a z3 set constant into a python set
# Must define when need arises
# def getPythonSetConstEncoding(z3_set):
#     return None

# Here is a list of z3py functions that already exist. These can be used to construct expressions involving sets and are generic w.r.t the sort of the elements of the set(s)
## Union: SetUnion(set1, set2) --- takes in two sets a and b of the same set sort and creates the expression denoting their union. Others below are similar
## Intersection: SetIntersect(set1, set2)
## Complement: SetComplement(set)
## Difference: SetDifference(set1, set2) -- expresses (set1 \setminus set2)
## Membership: IsMember(elem, set)
## Addition of one element: SetAdd(set, elem)
## Removal of one element: SetDel(set, elem)
## Cardinality predicate: SetHasSize(set, size)
## Subset predicate: IsSubset(set1, set2) --- expresses (set1 \subseteq set2)
## Universal and empty sets: general functions exist, but they need the sort of the elements. Alternatives are provided above that are themselves implemented using the general function
