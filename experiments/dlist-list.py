from z3 import *
import importlib_resources

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
import naturalproofs.decls_api as api
from lemsynth.lemsynth_engine import solveProblem


####### Section 0
# some general FOL macros
# TODO: move to utils
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return If(b, l, r)

# Datastructure initialisations Below are some dictionaries being
# initialised. Will be updated later with constants/functions/definitions of
# different input/output signatures

# fcts_z3 holds z3 function/predicate/recursive definition symbols.
# The signatures are written as
# <arity>_<input-tuple-type_underscore-separated>_<output-type>
# for non-recursive functions. Signatures are
# <rec*>_<arity>_<input-tuple-type_underscore-separated>_<output-type>
# forrecursive functions/predicates where <rec*> is a string starting with rec
fcts_z3 = {}

# Axioms always provide boolean output and may have different signatures for inputs
# Z3 axioms return z3's boolean type and the python version returns a boolean value
axioms_z3 = {}
axioms_python = {}

# Unfolding recursive definitions.

# The Z3 version says that the recursive call and its unfolding are equivalent
# The python version computes the value based on one level of unfolding given a
# concrete model
unfold_recdefs_z3 = {}
unfold_recdefs_python = {}

# NOTE: All axioms as well as unfoldings will only take one argument 'w'
# corresponding to the input parameters (apart from the model argument for the
# python versions). For those that require multiple arguments, this will be
# packed into a tuple before calling the functions/axioms.


######## Section 1
# Variables and Function Symbols

# The z3py variable for a z3 variable will be the same as its string value.
# So we will use the string 'x' for python functions and just x for creating z3 types
x, ret, nil = api.Consts('x ret nil', fgsort)
fcts_z3['0_int'] = [x, ret, nil]

######## Section 2
# Functions
next = api.Function('next', fgsort, fgsort)
prev = api.Function('prev', fgsort, fgsort)

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil
prev_nil_z3 = prev(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

def prev_nil_python(model):
    return model['prev'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
fcts_z3['1_int_int'] = [next, prev]
#axioms_z3['0'] = [next_nil_z3, prev_nil_z3]
#axioms_python['0'] = [next_nil_python, prev_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
list = api.Function('list', fgsort, boolsort)
dlist = api.Function('dlist', fgsort, boolsort)

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), If(x == nil, True, list(next(x))))

def udlist_z3(x):
    return Iff( dlist(x), IteBool(x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(prev(next(x)) == x, dlist(next(x))) )))

# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def udlist_python(x, model):
    if x == model['nil']:
        return True
    elif model['next'][x] == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        doubly_linked_cond = model['prev'][next_val] == x
        return doubly_linked_cond and model['dlist'][next_val]

unfold_recdefs_z3['1_int_bool'] = [ulist_z3, udlist_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, udlist_python]
pfp_dict = {}
pfp_dict['list'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (and (list (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''

pfp_dict['dlist'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (ite (= (next {primary_arg}) {nil})
              true
              (and (= (prev (next {primary_arg})) {primary_arg})
                   (and (dlist (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})) )))
    (lemma {primary_arg} {rest_args}))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [list,dlist]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, ret):
    return IteBool(x == nil, ret == nil, ret == next(x))

def vc(x, ret):
    return Implies(dlist(x),
                    Implies(pgm(x, ret), list(ret)))

deref = [x]
const = [nil]
verification_condition = vc(x,ret)

# End of input

###########################################################################################################################
# Lemma synthesis stub 
##########################################################################################################################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'dlist-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, grammar_string, config_params, synth_dict)
