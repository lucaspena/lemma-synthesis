# This module defines the API to declare variables and functions in the UCT fragment.
# The way these declarations combine is the regular z3py API as these are all z3py objects.

# This API essentially creates a wrapper around the z3py api by simply logging information about the signature of
# declarations in an AnnotatedContext object.

import z3
from naturalproofs.fgsort import is_sort_fg_sort
from naturalproofs.AnnotatedContext import add_alias_annotation


def Const(name, intended_sort):
    """
    Wrapper around z3.Const
    :param name: string
    :param intended_sort: z3.SortRef
    :return: z3.ExprRef
    """
    expr = z3.Const(name, intended_sort)
    if is_sort_fg_sort(intended_sort):
        annotated_ctx = intended_sort.ctx
        fg_sort_name = annotated_ctx.__fg_sort_name__
        add_alias_annotation(expr, tuple([fg_sort_name]))
    return expr


def Consts(names, intended_sort):
    """
    Wrapper around z3.Consts
    :param names: string containing all the names separated by a space
    :param intended_sort: z3.SortRef
    :return: z3.ExprRef
    """
    exprs = z3.Consts(names, intended_sort)
    if is_sort_fg_sort(intended_sort):
        annotated_ctx = intended_sort.ctx
        fg_sort_name = annotated_ctx.__fg_sort_name__
        for expr in exprs:
            add_alias_annotation(expr, tuple([fg_sort_name]))
    return exprs


def Function(name, *signature):
    """
    Wrapper around z3.Function
    :param name: string
    :param signature: tuple of z3.SortRef objects
    :return: z3.FuncDeclRef
    """
    func = z3.Function(name, *signature)
    range_sort = signature[-1]
    if is_sort_fg_sort(range_sort):
        annotated_ctx = range_sort.ctx
        fg_sort_name = annotated_ctx.__fg_sort_name__
        signature_annotation = tuple([sig.__repr__() if is_sort_fg_sort(sig) else fg_sort_name for sig in signature])
        add_alias_annotation(func, signature_annotation)
    return func
