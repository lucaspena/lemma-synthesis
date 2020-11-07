# This module defines various annotations over the expressions used in z3py
# This is a hack around z3py's handling of AstRef objects where the ast objects of subterms are not persistent across
# constructions of the ast objects of superterms. Therefore annotations have to be maintained outside.

import z3


class AnnotatedContext:
    """
    Class with annotations about various functions.
    Current annotations:
    - Signature-alias-annotation: keeps track of an 'alias' for the domain/range sorts of various functions.
    - fg-sort-name: Name of the 'foreground' sort used in natural proofs.
    """
    def __init__(self):
        self.__signature_alias_annotation__ = dict()


# Default annotated context. Only one context needed currently.
default_annctx = AnnotatedContext()


# Functions to manipulate __signature_alias_annotation__
def _signature_alias_annotation_key_repr(astref, annctx=default_annctx):
    # Internal function to convert AstRef objects to representation against which annotations for that object
    # can be stored in the __signature_alias_annotation__ dictionary.
    return astref.__repr__()


def read_alias_annotation(funcdeclref, annctx=default_annctx):
    """
    Returns the alias annotation given an expression if present in annctx.
    :param funcdeclref: z3.FuncDeclRef
    :param annctx: annotated context in which to look up alias annotation
    :return: tuple of naturalproofs.uct.UCTSort objects or None
    """
    if not isinstance(funcdeclref, z3.FuncDeclRef):
        raise TypeError('FuncDeclRef expected.')
    if not isinstance(annctx, AnnotatedContext):
        raise TypeError('AnnotatedContext expected.')
    else:
        key = _signature_alias_annotation_key_repr(funcdeclref)
        signature_annotation = annctx.__signature_alias_annotation__.get(key, None)
        return signature_annotation


def add_alias_annotation(funcdeclref, signature, update=False, annctx=default_annctx):
    """
    Adds to the __signature_alias_annotation__ dictionary keyed by a representation of the given
    expression, where the value is the aliased signature of the expression. The expression is
    meant to be a function, and its signature is (**input-sorts, output-sort).Constants are functions with
    only one component in the signature.
    :param funcdeclref: z3.FuncDeclRef
    :param signature: tuple of naturalproofs.uct.UCTSort objects
    :param update: Bool (if update is False then previous entries cannot be overwritten)
    :param annctx: annotated context in which to add alias annotation
    :return: None
    """
    if not isinstance(funcdeclref, z3.FuncDeclRef):
        raise TypeError('FuncDeclRef Expected.')
    if not isinstance(annctx, AnnotatedContext):
        raise TypeError('AnnotatedContext expected.')
    else:
        key = _signature_alias_annotation_key_repr(funcdeclref)
        previous_value = read_alias_annotation(funcdeclref)
        if not update and previous_value is not None:
            raise ValueError('Entry already exists. To override provide update=True.')
        if not isinstance(signature, tuple):
            # The expr is a constant and signature was the sort of the expr
            signature = tuple([signature])
        annctx.__signature_alias_annotation__[key] = signature
