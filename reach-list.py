from z3 import *
from lemma_synthesis import *

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
x, s, nil = Ints('x s nil')
fcts_z3['0_int'] = [x, s, nil]

######## Section 2
# Functions
v = Function('v', IntSort(), IntSort())
v1 = Function('v1', IntSort(), IntSort())
v2 = Function('v2', IntSort(), IntSort())
p = Function('p', IntSort(), IntSort())
n = Function('n', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = n(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['n'][model['nil']] == model['nil']

fcts_z3['1_int_int'] = [v, v1, v2, p, n]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
list = Function('list', IntSort(), BoolSort())
reach = Function('reach', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(n(x))) )

def ureach_z3(x):
    pre = And(v1(x) != nil, v1(x) == v(x), v2(x) == n(v(x)))
    neg_while = Or(v1(x) == v2(x), v2(x) == nil)
    inner_ite = IteBool( n(v2(p(x))) == v1(p(x)),
                         v2(x) == v1(x),
                         And(v1(x) == n(v1(p(x))), v2(x) == n(n(v2(p(x))))) )
    outer_ite = IteBool( n(v2(p(x))) == nil, v2(x) == nil, inner_ite )
    return Iff( reach(x), IteBool( x == s,
                                   pre,
                                   And(reach(p(x)), neg_while, v(x) == v(p(x)), outer_ite) ) )

# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        n_val = model['n'][x]
        return model['list'][n_val]

def ureach_python(x, model):
    p_val = model['p'][x]
    v_curr = model['v'][x]
    n_v = model['n'][v_curr]
    v_p = model['v'][p_val]
    n_v_p = model['n'][v_p]
    v1_curr = model['v1'][x]
    v1_p = model['v1'][p_val]
    n_v1_p = model['n'][v1_p]
    v2_curr = model['v2'][x]
    v2_p = model['v2'][p_val]
    n_v2_p = model['n'][v2_p]
    n_n_v2_p = model['n'][n_v2_p]
    if x == model['s']:
        return v1_curr != model['nil'] and v1_curr == v_curr and v2_curr == n_v
    else:
        rec = model['reach'][p_val]
        neg_while = v1_curr == v2_curr or v2_curr == model['nil']
        ret = rec and neg_while and v_curr == v_p
        if n_v2_p == nil:
            return ret and v2_curr == model['nil']
        elif n_v2_p == v1_p:
            return ret and v2_curr == v1_curr
        else:
            return ret and v1_curr == n_v1_p and v2_curr == n_n_v2_p

unfold_recdefs_z3['1_int_bool'] = [ulist_z3, ureach_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, ureach_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [list, reach]

############# Section 5
# Program, VC, and Instantiation

def vc(x):
    lhs = And( reach(x), v2(x) == nil )
    rhs = list(v(x))
    return Implies( lhs, rhs )

deref = [x]
const = [nil, s]
elems = [*range(5)]
config_params = {'mode': 'random', 'num_true_models': 20}

# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

# continuously get valid lemmas until VC has been proven
while True:
    lemmas = getSygusOutput(elems, config_params, fcts_z3, axioms_python, axioms_z3,
                             valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                             vc(x), 'reach-list')
    # lemmas = lemmas + ['(define-fun lemma ((x Int) (nil Int) (c Int)) Bool (=> (reach x) (or (= c  (v2 x)) (= (v1 x) (v2 x)))))']
    print("lemmas: {}".format(lemmas))
    for lemma in lemmas:
        z3py_lemma = translateLemma(lemma, fcts_z3)
        if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
            print('lemma has already been proposed')
            continue
        model = getFalseModel(axioms_z3, fcts_z3, valid_lemmas, unfold_recdefs_z3, deref, const, z3py_lemma, True)
        if model != None:
            print('proposed lemma cannot be proved.')
            invalid_lemmas = invalid_lemmas + [ z3py_lemma ]
            # TODO: add to bag of unwanted lemmas (or add induction principle of lemma to axioms)
            # and continue
        else:
            valid_lemmas = valid_lemmas + [ z3py_lemma ]
            break
