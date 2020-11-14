"""
This module defines the basic function pertaining to finite models: extraction. An smt model is created with 
respect to a quantifier-free goal. The extracted model must have a finite foreground universe and must 
preserve the satisfaction of the original goal. This is done by restricting the smt model to the subterm-closed 
set containing the set of foreground terms in the quantifier-free goal.  

This module also defines the format of the finite model. These models are meant to be used explicitly 
and are therefore not abstracted behind an interface.  
Given a vocabulary of functions f1, f2, ..fm, of arity a1, a2, ...am, the model is as follows:  
model :: dict {'fk' : dict_fk}  
where 'fk' is some representation of the function fk, and  
dict_fk :: dict {(e1, e2,... ek) : fk(e1, e2, ...ek)}  
where (e1, e2, ...ek) is a tuple such that e1, e2,.. etc are concrete values in python that are dependent on the 
domain and range sorts of fk.    
In particular if the arity k is 0, then dict_fk will be of the following form:  
dict_fk :: dict {() : fk()}  

These models are meant to be partial models, and in general it will not be possible to evaluate an arbitrary formula 
on such a model, just those that are quantifier-free with foreground terms in the set of terms used to extract the 
finite model.  
"""

import itertools
# import copy
import z3
# model.compact should be turned off to not get lambdas, only actual arrays/sets.
z3.set_param('model.compact', False)

from naturalproofs.AnnotatedContext import default_annctx 
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import get_vocabulary, get_uct_signature
from naturalproofs.extensions.finitemodel_utils import transform_fg_universe, collect_fg_universe


def extract_finite_model(smtmodel, terms, vocabulary=None, annctx=default_annctx):
    """
    Finite model extraction.  
    Foreground universe of extracted model corresponds to terms with subterm-closure. If vocabulary is not specified, 
    the entire vocabulary tracked in annctx is used.  
    :param smtmodel: z3.ModelRef  
    :param terms: set of z3.ExprRef  
    :param vocabulary: set of z3.ExprRef  
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext  
    :return: dict  
    """
    model = dict()
    # TODO: the assumption is that uninterpreted functions have arguments only from the foreground sort. Must handle
    #  cases where uninterpreted functions have arguments in other domains, primarily integers.
    # Subterm-close the given terms assuming one-way functions
    # TODO: checks for all terms being of the foreground sort.
    subterm_closure = _get_all_subterms(terms)
    elems = {smtmodel.eval(term, model_completion=True) for term in subterm_closure}
    if vocabulary is None:
        vocabulary = get_vocabulary(annctx)
    for func in vocabulary:
        arity = func.arity()
        *input_signature, output_sort = get_uct_signature(func, annctx)
        # Only supporting uninterpreted functions with input arguments all from the foreground sort
        if not all(sig == fgsort for sig in input_signature):
            raise ValueError('Function with input(s) not from the foreground sort. Unsupported.')
        func_key_repr = model_key_repr(func)
        # Distinguish common cases for faster execution
        if arity == 0:
            model[func_key_repr] = {(): _extract_value(smtmodel.eval(func(), model_completion=True), output_sort)}
        elif arity == 1:
            model[func_key_repr] = {(_extract_value(elem, fgsort),): _extract_value(smtmodel.eval(func(elem), model_completion=True), output_sort) for elem in elems}
        else:
            func_dict = dict()
            args = itertools.product(elems, repeat=arity)
            for arg in args:
                arg_value = tuple(_extract_value(component, fgsort) for component in arg)
                func_dict[arg_value] = _extract_value(smtmodel.eval(func(*arg), model_completion=True), output_sort)
            model[func_key_repr] = func_dict
    return model


# Helper functions for extract_finite_model
# Return all subterms of the given set of terms
def _get_all_subterms(terms):
    """
    :param terms: set of z3.ExprRef
    :return: set of z3.ExprRef
    """
    subterm_closure = set()
    for term in terms:
        subterm_closure.add(term)
        if term.decl().arity != 0:
            subterm_closure = subterm_closure | _get_all_subterms(set(term.children()))
    return subterm_closure


# Representation of keys in the finite model top-level dictionary.
def model_key_repr(funcdeclref):
    # Should be equivalent to naturalproofs.AnnotatedContext._alias_annotation_key_repr(funcdeclref)
    # For z3.FuncDeclRef objects, this is almost always equal to name()
    return funcdeclref.name()


def _extract_value(value, uct_sort):
    """
    Converts the value of a concrete constant represented as a z3.ExprRef into a simple python type
    that can be explicitly manipulated.  
    The explicit conversion scheme is as follows:  
    fgsort -> int  
    fgsetsort -> set of int  
    intsort -> int  
    intsetsort -> set of int  
    boolsort -> bool  
    :param value: z3.ExprRef  
    :param uct_sort: uct.UCTSort  
    :return: any  
    """
    # value assumed to be such that value.decl().arity == 0
    if uct_sort == boolsort:
        # value is either BoolVal(True) or BoolVal(False)
        return z3.is_true(value)
    elif uct_sort == fgsort or uct_sort == intsort:
        # value is an IntVal(v) for some number v
        return value.as_long()
    elif uct_sort == fgsetsort or uct_sort == intsetsort:
        # value is a set of integers.
        # model.compact has been disabled (see top of file). ArrayRef should not have lambdas in it.
        if not isinstance(value, z3.ArrayRef):
            raise ValueError('Something is wrong. Model is returning lambdas instead of arrays.')
        # iteratively deconstruct the expression to build the set of python numbers.
        extracted_set = set()
        value = value.__deepcopy__()
        while True:
            if z3.is_K(value):
                # Base case. Either full set or empty set.
                if z3.simplify(value[0]):
                    # Full set of integers. Raise exception.
                    raise ValueError('Model assigned infinite sets to some interpretations. Unsupported.')
                else:
                    return extracted_set
            elif z3.is_store(value):
                remaining_set, entry, if_belongs = value.childrne()
                value = remaining_set
                extracted_set = extracted_set | ({entry.as_long()} if z3.is_true(if_belongs) else {})
            else:
                raise ValueError('ArrayRef is constructed with neither Store nor K. Possible multidimensional arrays. '
                                 'Unsupported.') 
    else:
        raise ValueError('UCT Sort type not supported for extraction of models.')


def recover_value(value, uct_sort):
    """
    Inverse of _extract_value. Given a pythonic value, returns a z3 embedding of it depending on its uct sort. The 
    explicit embedding scheme is as follows:
    fgsort -> z3.ArithRef
    fgsetsort -> z3.ArrayRef
    intsort -> z3.ArithRef
    intsetsort -> z3.ArrayRef
    boolsort -> z3.BoolRef
    :param value: any
    :param uct_sort: naturalproofs.uct.UCTSort
    :return: z3.ExprRef
    """
    # TODO: typecheck all the arguments
    if uct_sort in {fgsort, intsort}:
        return z3.IntVal(value)
    elif uct_sort == boolsort:
        return z3.BoolVal(value)
    elif uct_sort in {fgsetsort, intsetsort}:
        expr = z3.EmptySet(z3.IntSort())
        for elem in value:
            expr = z3.SetAdd(expr, z3.IntVal(elem))
    else:
        raise ValueError('Sort not supported. Check for a list of available sorts in the naturalproofs.uct module.')


# Some common functions on finite models
def get_fg_elements(finite_model, annctx=default_annctx):
    # fg_elem_set = set()
    # _ = transform_fg_universe(finite_model, lambda x: (fg_elem_set.add(x), x)[1], annctx)
    # return fg_elem_set
    return collect_fg_universe(finite_model, annctx)


def add_fg_element_offset(finite_model, offset_value, annctx=default_annctx):
    return transform_fg_universe(finite_model, lambda x: x + offset_value, annctx)
