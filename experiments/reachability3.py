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
x, c, s, nil = Ints('x c s nil')
fcts_z3['0_int'] = [x, c, s, nil]

######## Section 2
# Functions
v1 = Function('v1', IntSort(), IntSort())
v2 = Function('v2', IntSort(), IntSort())
p = Function('p', IntSort(), IntSort())
n = Function('n', IntSort(), IntSort())

fcts_z3['1_int_int'] = [v1, v2, p, n]

# Axioms: precondition
pre_z3 = v1(s) == v2(s)

def pre_python(model):
    return model['v1'][model['s']] == model['v2'][model['s']]

axioms_z3['0'] = [pre_z3]
axioms_python['0'] = [pre_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
reach = Function('reach', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ureach_z3(x):
    cond = v1(p(x)) != c
    assign1 = v1(x) == n(v1(p(x)))
    assign2 = IteBool( v2(p(x)) != c,
                       v2(x) == n(v2(p(x))),
                       v2(x) == v2(p(x)) )
    assign = And(assign1, assign2)
    return Iff( reach(x), IteBool( x == s,
                                   True,
                                   And( reach(p(x)), cond, assign ) ) )

# Python versions for finding valuation on true models
def ureach_python(x, model):
    p_val = model['p'][x]
    v1_curr = model['v1'][x]
    v1_p = model['v1'][p_val]
    n_v1_p = model['n'][v1_p]
    v2_curr = model['v2'][x]
    v2_p = model['v2'][p_val]
    n_v2_p = model['n'][v2_p]
    if x == model['s']:
        return True
    else:
        rec = model['reach'][p_val]
        cond = v1_p != model['c']
        assign1 = v1_curr == n_v1_p
        ret = rec and cond and assign1
        if v2_p != model['c']:
            return ret and v2_curr == n_v2_p
        else:
            return ret and v2_curr == v2_p

unfold_recdefs_z3['1_int_bool'] = [ureach_z3]
unfold_recdefs_python['1_int_bool'] = [ureach_python]
pfp_dict = {}
pfp_dict['reach'] = '''
                    (=>  
                    (ite (= {primary_arg} {s})
                         true
                         (and (and (reach (p {primary_arg})) (lemma (p {primary_arg}) {rest_args}))
                              (and (not (= (v1 (p {primary_arg})) {c})) 
                                   (and (= (v1 {primary_arg}) (n (v1 (p {primary_arg})))) 
                                        (ite (not (= (v2 (p {primary_arg})) {c})) 
                                             (= (v2 {primary_arg}) (n (v2 (p {primary_arg})))) 
                                             (= (v2 {primary_arg}) (v2 (p {primary_arg}))))))))
                    (lemma {primary_arg} {rest_args}))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [reach]

############# Section 5
# Program, VC, and Instantiation

def vc(x):
    lhs = And( reach(x), v1(x) == nil )
    rhs = Or( v2(x) == nil, v2(x) == c )
    return Implies( lhs, rhs )

deref = [x, p(x), v1(p(x)), v2(p(x))]
const = [nil, s, c]
verification_condition = vc(x)

# End of input

###########################################################################################################################
# Lemma synthesis stub 
##########################################################################################################################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'reachability3'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, grammar_string, config_params, synth_dict)
