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
y, nil = Ints('y nil')
fcts_z3['0_int'] = [y, nil]

######## Section 2
# Functions
next = Function('next', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
# TODO: what to do about -1 for key axioms?
fcts_z3['1_int_int'] = [next]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
lsegy = Function('lsegy', IntSort(), BoolSort())
lsegny = Function('lsegny', IntSort(), BoolSort())
clisty = Function('clisty', IntSort(), BoolSort())
clistny = Function('clistny', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulsegy_z3(x):
    return Iff( lsegy(x), IteBool(x == y, True, lsegy(next(x))) )

def ulsegny_z3(x):
    return Iff( lsegny(x), IteBool(x == next(y), True, lsegny(next(x))) )

# note clist does not define a cyclic list unless it is called on y
def uclisty_z3(x):
    return Iff( clisty(x), And(x != nil, lsegy(next(x))) )

def uclistny_z3(x):
    return Iff( clistny(x), And(x != nil, lsegny(next(x))) )

unfold_recdefs_z3['1_int_bool'] = [ulsegy_z3, ulsegny_z3, uclisty_z3, uclistny_z3]
pfp_dict = {}
pfp_dict['lsegy'] = '''
(=> (ite (= (next {primary_arg}) {y})
         true
         (and (lsegy (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''
pfp_dict['lsegny'] = '''
(=> (ite (= (next {primary_arg}) (next {y}))
         true
         (and (lsegny (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''
pfp_dict['clisty'] = '''
(and (not (= {primary_arg} nil)) (lsegy (next {primary_arg})))'''
pfp_dict['clistny'] = '''
(and (not (= {primary_arg} nil)) (lsegny (next {primary_arg})))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [lsegy, lsegny, clisty, clistny]

############# Section 5
# Program, VC, and Instantiation

def vc(x):
    return Implies( clisty(x), clistny(next(next(x))) )

deref = []
const = [nil, y, next(y)]
verification_condition = vc(y)

# End of input

###########################################################################################################################
# Lemma synthesis stub 
##########################################################################################################################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['elems'] = [*range(3)]
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'cyclic-next'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, grammar_string, config_params, synth_dict)
