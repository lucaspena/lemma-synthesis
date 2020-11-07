# This module defines the API to declare variables and functions in the UCT fragment.
# The way these declarations combine is the regular z3py API as the returned objects are all z3py objects.

# This API essentially creates a wrapper around the z3py api by simply logging information about the signature of
# declarations in an AnnotatedContext object.

import z3
from naturalproofs.uct import UCTSort
from naturalproofs.AnnotatedContext import AnnotatedContext, default_annctx, add_alias_annotation


def Const(name, uct_sort, annctx=default_annctx):
    """
    Wrapper around z3.Const
    :param name: string
    :param uct_sort: naturalproofs.uct.UCTSort
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext
    :return: z3.ExprRef
    """
    if not isinstance(uct_sort, UCTSort):
        raise TypeError('UCTSort expected.')
    z3const = z3.Const(name, uct_sort.z3sort)
    if not isinstance(annctx, AnnotatedContext):
        raise TypeError('AnnotatedContext expected.')
    add_alias_annotation(z3const.decl(), tuple([uct_sort]), annctx)
    return z3const


def Consts(names, uct_sort, annctx=default_annctx):
    """
    Wrapper around z3.Consts
    :param names: string containing all the names separated by a space
    :param uct_sort: naturalproofs.uct.UCTSort
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext
    :return: list of z3.ExprRef
    """
    if not isinstance(uct_sort, UCTSort):
        raise TypeError('UCTSort expected.')
    z3consts = z3.Consts(names, uct_sort.z3sort)
    if not isinstance(annctx, AnnotatedContext):
        raise TypeError('AnnotatedContext expected.')
    for z3const in z3consts:
        add_alias_annotation(z3const.decl(), tuple([uct_sort]), annctx)
    return z3consts


def Function(name, *uct_signature, annctx=default_annctx):
    """
    Wrapper around z3.Function
    :param name: string
    :param uct_signature: tuple of naturalproofs.uct.UCTSort
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext
    :return: z3.FuncDeclRef
    """
    if not all([isinstance(sig, UCTSort) for sig in uct_signature]):
        raise TypeError('UCTSort expected.')
    if not isinstance(annctx, AnnotatedContext):
        raise TypeError('AnnotatedContext expected.')
    z3sig = [sig.z3sort for sig in uct_signature]
    z3func = z3.Function(name, *z3sig)
    add_alias_annotation(z3func, uct_signature, annctx)
    return z3func
