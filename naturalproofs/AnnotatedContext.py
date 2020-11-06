# This module defines AnnotatedContext, a z3.Context subclass with an extra dictionary that keeps track of various
# annotations
# This is a hack around z3py's handling of AstRef objects where the ast objects of subterms are not persistent across
# constructions of the ast objects of superterms. However, context objects are persistent.

import z3


class AnnotatedContext(z3.Context):
    __signature_alias_annotation__ = None
    __fg_sort_name__ = None

    def __init__(self):
        self.__signature_alias_annotation__ = dict()
        super(AnnotatedContext, self).__init__()


# Functions to manipulate __signature_alias_annotation__
def _signature_alias_annotation_repr(astref):
    return astref.__repr__()


def read_alias_annotation(astref):
    """
    Returns the alias annotation given an expression. The context used is the one in the expression's ctx field.
    :param astref: z3.AstRef
    :return: tuple of strings or None
    """
    if not isinstance(astref, z3.AstRef):
        raise TypeError('AstRef expected.')
    context = astref.ctx
    if not isinstance(context, AnnotatedContext):
        raise TypeError('The context of the given expression does not have alias annotations.')
    else:
        key = _signature_alias_annotation_repr(astref)
        signature_annotation = context.__signature_alias_annotation__.get(key, None)
        return signature_annotation


def add_alias_annotation(astref, signature, update=False):
    """
    Adds to the __signature_alias_annotation__ dictionary keyed by the string representation of the given
    expression, where the value is the aliased signature of the expression. The expression is
    meant to be a function or a variable.
    :param astref: z3.AstRef
    :param signature: tuple of strings
    :param update: Bool (if update is False then previous entries cannot be overwritten)
    :return: None
    """
    if not isinstance(astref, z3.AstRef):
        raise TypeError('AstRef Expected.')
    context = astref.ctx
    if not isinstance(context, AnnotatedContext):
        raise TypeError('The context of the given expression cannot be annotated.')
    else:
        key = _signature_alias_annotation_repr(astref)
        previous_value = read_alias_annotation(astref)
        if not update and previous_value is not None:
            raise ValueError('Context already has an entry for given expression.')
        if not isinstance(signature, tuple):
            # The expr is a constant and signature was the sort of the expr
            signature = tuple([signature])
        context.__signature_alias_annotation__[key] = signature
