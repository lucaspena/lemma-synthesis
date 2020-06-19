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
x, c, nil = Ints('x ret nil')
fcts_z3['0_int'] = [x, c, nil]

######## Section 2
# Functions
v1 = Function('v1', IntSort(), IntSort())
v2 = Function('v2', IntSort(), IntSort())
p = Function('p', IntSort(), IntSort())
n = Function('n', IntSort(), IntSort())

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
# TODO: what to do about -1 for key axioms?
fcts_z3['1_int_int'] = [v1, v2, p, n]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
reach = Function('reach', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ureach_z3(x):
    cond = v1(p(x)) != nil
    assign1 = v1(x) == n(v1(p(x)))
    assign2 = IteBool( v2(p(x)) != c,
                       v2(x) == n(v2(p(x))),
                       v2(x) == v2(p(x)) )
    assign = And(assign1, assign2)
    return Iff( reach(x), IteBool( v1(x) == v2(x),
                                   True,
                                   And( reach(p(x)), cond, assign ) ) )

# Python versions for finding valuation on true models
def ureach_python(x, model):
    n_val = model['n'][x]
    p_val = model['p'][x]
    v1_curr = model['v1'][x]
    v1_p = model['v1'][p_val]
    n_v1_p = model['next'][v1_p]
    v2_curr = model['v2'][x]
    v2_p = model['v2'][p_val]
    n_v2_p = model['next'][v2_p]
    if v1_curr == v2_curr:
        return True
    else:
        rec = model['reach'][p_val]
        cond = v1_p != model['nil']
        assign1 = v1_curr == n_v1_p
        ret = rec and cond and assign1
        if v2_p != model['c']:
            return ret and v2_curr == n_v2_p
        else:
            return ret and v2_curr == v2_p

unfold_recdefs_z3['1_int_bool'] = [ureach_z3]
unfold_recdefs_python['1_int_bool'] = [ureach_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [reach]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, ret):
    return IteBool(x == nil, ret == nil, ret == next(x))

def vc(x, ret):
    return Implies( slist(x),
                    Implies(pgm(x, ret), list(ret)))

deref = [x]
const = [nil]
elems = [*range(3)]
num_true_models = 10

# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

# continuously get valid lemmas until VC has been proven
while True:
    lemmas = getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3,
                            valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                            vc(x,ret), 'slist-list')
    for lemma in lemmas:
        z3py_lemma = translateLemma(lemma, fcts_z3)
        if z3py_lemma in invalid_lemmas:
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
