# This module defines the API for the UCT fragment.
# Currently it is enough to define and handle the sorts that are supported.

import z3
from naturalproofs.AnnotatedContext import AnnotatedContext, default_annctx
import naturalproofs.utils as utils


class UCTSort:
    """
    Class representing a sort in the UCT signature.
    """
    def __init__(self, name, z3sort, is_foreground=False):
        """
        There are three parameters that define a UCT sort.
        :param name (string): Name or 'alias' of the uct sort.
        :param z3sort (z3.SortRef): The underlying z3 sort that is used to phrase smt queries.
        :param is_foreground (bool): If the given sort is a foreground sort.
        """
        self.name = name
        self.z3sort = z3sort
        self.is_foreground = is_foreground
        if is_foreground and z3sort != z3.IntSort():
            raise ValueError('Currently foreground sort can only be represented using integers.')
        # Additional parameters
        # Lattice structure
        self.lattice_lessequals_operator = None
        self.lattice_top = None
        self.lattice_bottom = None

    # Functions to access the additional parameters
    def get_lattice_lessequals_operator(self):
        return self.lattice_lessequals_operator

    def get_lattice_top_element(self):
        return self.lattice_top

    def get_lattice_bottom_element(self):
        return self.lattice_bottom


# Sorts supported in the UCT fragment
# Foreground sort
fgsort = UCTSort('Fg', z3.IntSort(), True)
# Set of foreground sort
fgsetsort = UCTSort('FgSet', z3.SetSort(z3.IntSort()))
fgsetsort.lattice_lessequals_operator = utils.IsSubset_Int_as_FuncDeclRef
fgsetsort.lattice_top = z3.FullSet(z3.IntSort())
fgsetsort.lattice_bottom = z3.EmptySet(z3.IntSort())
# Generic integer sort
intsort = UCTSort('Int', z3.IntSort())
# Set of integer sort
intsetsort = UCTSort('IntSet', z3.SetSort(z3.IntSort()))
intsetsort.lattice_lessequals_operator = utils.IsSubset_Int_as_FuncDeclRef
intsetsort.lattice_top = z3.FullSet(z3.IntSort())
intsetsort.lattice_bottom = z3.EmptySet(z3.IntSort())
# Boolean sort
boolsort = UCTSort('Bool', z3.BoolSort())
boolsort.lattice_lessequals_operator = utils.Implies_as_FuncDeclRef
boolsort.lattice_top = z3.BoolVal(True)
boolsort.lattice_bottom = z3.BoolVal(False)


# Functions to manipulate sort information
def get_uct_sort(exprref, annctx=default_annctx):
    """
    Retrieve the sort of the given expression in terms of UCTSort objects.
    :param exprref: z3.ExprRef
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext
    :return: tuple of UCTSort objects or None
    """
    if not isinstance(exprref, z3.ExprRef):
        raise TypeError('ExprRef expected.')
    if not isinstance(annctx, AnnotatedContext):
        raise TypeError('AnnotatedContext expected.')
    # The sort of the expression is the range sort of the declaration
    declaration = exprref.decl()
    sig = annctx.read_alias_annotation(declaration)
    if sig is None:
        # Signature cannot be looked up in the annotated context. Default to using z3 sort in the client code.
        return sig
    else:
        return sig[-1]


# Specialised function that is used very commonly in the naturalproofs package
def is_expr_fg_sort(exprref, annctx=default_annctx):
    """
    Determine if the sort of the given expression is a foreground sort
    :param exprref: z3.ExprRef
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext
    :return: Bool
    """
    uct_sort = get_uct_sort(exprref, annctx)
    return uct_sort == fgsort
