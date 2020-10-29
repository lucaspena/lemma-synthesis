import importlib_resources
from z3 import *
from lemsynth.lemsynth_engine import *

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
x, y, ret, nil = Ints('x y ret nil')
fcts_z3['0_int'] = [x, y, ret, nil]

######## Section 2
# Functions
next = Function('next', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil
# key_nil_z3 = key(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# def key_nil_python(model):
#     return model['key'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
# TODO: what to do about -1 for key axioms?
fcts_z3['1_int_int'] = [next, key]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
lseg_y = Function('lseg_y', IntSort(), BoolSort())
slseg_y = Function('slseg_y', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulseg_y_z3(x):
    return Iff( lseg_y(x), IteBool(x == y, True, lseg_y(next(x))) )

def uslseg_y_z3(x):
    return Iff( slseg_y(x), IteBool( x == y,
                                     True,
                                     IteBool( next(x) == y,
                                              True,
                                              And(key(x) <= key(next(x)), slseg_y(next(x)))) ))

# Python versions for finding valuation on true models
def ulseg_y_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next'][x]
        return model['lseg_y'][next_val]

def uslseg_y_python(x, model):
    if x == model['y']:
        return True
    elif model['next'][x] == model['y']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slseg_y'][next_val]

unfold_recdefs_z3['1_int_bool'] = [ulseg_y_z3, uslseg_y_z3]
unfold_recdefs_python['1_int_bool'] = [ulseg_y_python, uslseg_y_python]
pfp_dict = {}
pfp_dict['lseg_y'] = '''
(=> (ite (= {primary_arg} {y})
         true
         (and (lseg_y (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''

pfp_dict['slseg_y'] = '''
(=> (ite (= {primary_arg} {y})
         true
         (ite (= (next {primary_arg}) {y})
              true
              (and (<= (key {primary_arg}) (key (next {primary_arg})))
                   (and (slseg_y (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))))
    (lemma {primary_arg} {rest_args}))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [lseg_y, slseg_y]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, y, ret):
    return IteBool(x == y, ret == y, ret == next(x))

def vc(x, y, ret):
    return Implies( slseg_y(x),
                    Implies(pgm(x, y, ret), lseg_y(ret)))

deref = [x]
const = [nil, y]
verification_condition = vc(x,y,ret)

# End of input

###########################################################################################################################
# Lemma synthesis stub 
##########################################################################################################################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'slseg-lseg'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, grammar_string, config_params, synth_dict)
