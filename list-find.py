from z3 import *
from src.set_sort import *
from src.lemsynth_engine import *

####### Section 0
# some general FOL macros
# TODO: move to utils
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

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
x, y, yp, nil = Ints('x y yp nil')
fcts_z3['0_int'] = [x, y, yp, nil]

####### Section 2
# Functions
next = Function('next', IntSort(), IntSort())

# Axioms for next and next' of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
fcts_z3['1_int_int'] = [next]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
list = Function('list', IntSort(), BoolSort())
lsegy = Function('lsegy', IntSort(), BoolSort())
lsegyp = Function('lsegyp', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))) )

def ulsegy_z3(x):
    return Iff( lsegy(x), IteBool(x == y, True, lsegy(next(x))) )

def ulsegyp_z3(x):
    return Iff( lsegyp(x), IteBool(x == yp, True, lsegyp(next(x))) )


# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def ulsegy_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next'][x]
        return model['lsegy'][next_val]

def ulsegyp_python(x, model):
    if x == model['yp']:
        return True
    else:
        next_val = model['next'][x]
        return model['lsegyp'][next_val]

unfold_recdefs_z3['1_int_bool'] = [ulist_z3, ulsegy_z3, ulsegyp_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, ulsegy_python, ulsegyp_python]
pfp_dict = {}
pfp_dict['list'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (and (list (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''
pfp_dict['lsegy'] = '''
(=> (ite (= {primary_arg} {y})
         true
         (and (lsegy (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''
pfp_dict['lsegyp'] = '''
(=> (ite (= {primary_arg} {yp})
         true
         (and (lsegyp (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [list, lsegy, lsegyp]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, y, yp):
    precondition = And(lsegy(x), list(y))
    program_body = next(y) == yp
    return And(precondition, program_body)

def vc(x, y, yp):
    return Implies( pgm(x, y, yp), And(lsegyp(x), list(yp)) )

deref = [x]
const = [nil, y, yp]
verification_condition = vc(x,y,yp)

# End of input

###########################################################################################################################
# Lemma synthesis stub 
##########################################################################################################################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'list-find'

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, config_params, synth_dict)