import importlib_resources
from z3 import *
from lemsynth.set_sort import *
from lemsynth.lemsynth_engine import *

####### Section 0
# some general FOL macros
# TODO: move to utils
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

fcts_z3 = {}
axioms_z3 = {}
axioms_python = {}

# Unfolding recursive definitions.
unfold_recdefs_z3 = {}
unfold_recdefs_python = {}

######## Section 1
# Variables and Function Symbols

# The z3py variable for a z3 variable will be the same as its string value.
x, ret, nil = Ints('x ret nil')
skolem = Int('skolem')
fcts_z3['0_int'] = [x, ret, nil, skolem]

######## Section 2
# Functions
next = Function('next', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
# TODO: what to do about -1 for key axioms?
fcts_z3['1_int_int'] = [next, key]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
SetIntSort = createSetSort('int')
list = Function('list', IntSort(), BoolSort())
slist = Function('slist', IntSort(), BoolSort())
keys = Function('keys', IntSort(), SetIntSort)
xks = Function('xks', SetIntSort)

############ Section 4
# Unfolding recursive definitions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))) )

def uslist_z3(x):
    return Iff( slist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(key(x) <= key(next(x)), slist(next(x)))) ))

def ukeys_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    then_case = Implies(is_nil, keys(x) == emptyset)
    else_case = Implies(Not(is_nil), keys(x) == SetAdd(keys(next(x)), key(x)))
    return And(then_case, else_case)

# Python versions for finding valuation on true models
unfold_recdefs_z3['1_int_bool'] = [ulist_z3, uslist_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_z3]

pfp_dict = {}
pfp_dict['list'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (and (list (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))'''

pfp_dict['slist'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (ite (= (next {primary_arg}) {nil})
              true
              (and (<= (key {primary_arg}) (key (next {primary_arg})))
                   (and (slist (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))))
    (lemma {primary_arg} {rest_args}))'''

fcts_z3['recpreds-loc_1_int_bool'] = [list, slist]

############# Section 5
# Program, VC, and Instantiation

def vc(x, ret):
    return Implies( list(x),
                    Implies(And(keys(x) == xks(), x == nil, ret == nil),
                            And(slist(ret), keys(ret) == xks())) )

deref = [x, next(x), skolem, next(skolem)]
const = [nil]
verification_condition = vc(x, ret)

# End of input

######################
# Lemma synthesis stub 
######################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'lem-member'
# Grammar string is empty because no lemma synthesis is needed
grammar_string = ''

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, grammar_string, config_params, synth_dict)
