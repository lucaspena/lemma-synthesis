# This module defines AliasedSortRef, the SortRef subclass that will be used to denote the foreground sort in
# natural proofs

# TODO: add checks for expressions being well-formed with respect to the alias annotations.

import z3
from naturalproofs.AnnotatedContext import AnnotatedContext, read_alias_annotation


class AliasedSortRef(z3.ArithSortRef):
    """
    Class to represent generic foreground sort in the natural proofs solver.
    The internal representation is that of integers.
    """
    __sort_alias__ = None


def FGSort(name, ctx):
    """
    Creates an AliasedSortRef object whose __sort_alias__ is the given name.
    The ctx object stores the name as well.
    :param name: String
    :param ctx: AnnotatedContext
    :return: AliasedSortRef
    """
    if not isinstance(ctx, AnnotatedContext):
        raise TypeError('Foreground sort must be created using an AnnotatedContext.')
    if ctx.__fg_sort_name__ is not None:
        raise ValueError('The given context already has a foreground sort.')
    ctx.__fg_sort_name__ = name
    sort_ast = z3.Z3_mk_int_sort(ctx.ref())
    fg_sort = AliasedSortRef(sort_ast, ctx)
    fg_sort.__sort_alias__ = name
    return fg_sort


def is_sort_fg_sort(sortref):
    """
    Determines if the given SortRef object is a foreground sort instance.
    The context in which this is computed is the object's own ctx field.
    :param sortref: SortRef
    :return: Bool
    """
    if not isinstance(sortref, z3.SortRef):
        raise TypeError('SortRef Expected.')
    if not isinstance(sortref, AliasedSortRef):
        return False
    else:
        return sortref.ctx.__fg_sort_name__ == sortref.__sort_alias__


def is_expr_fg_sort(exprref):
    """
    Determines if the sort of the given expression is that of the foreground sort by reading the
    __signature_alias_annotation__ field in an AnnotatedContext object. The context object used is the one present in
    the expression's ctx field.
    :param exprref: ExprRef
    :return: Bool
    """
    if not isinstance(exprref, z3.ExprRef):
        raise TypeError('ExprRef expected')
    ctx = exprref.ctx
    if not isinstance(ctx, AnnotatedContext):
        raise TypeError('Given expression was not created in an AnnotatedContext.')
    fg_sort_name = ctx.__fg_sort_name__
    if fg_sort_name is None:
        raise ValueError('The context of the given expression does not specify a foreground sort.')
    declaration = exprref.decl()
    # Last component of signature indicates the range of the declaration, and hence the sort of the expression.
    exprref_sort = read_alias_annotation(declaration)[-1]
    return exprref_sort == fg_sort_name

ann_ctx = AnnotatedContext()