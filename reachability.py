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
x, c, nil = Ints('x c nil')
fcts_z3['0_int'] = [x, c, nil]

######## Section 2
# Functions
v1 = Function('v1', IntSort(), IntSort())
v2 = Function('v2', IntSort(), IntSort())
p = Function('p', IntSort(), IntSort())
n = Function('n', IntSort(), IntSort())

fcts_z3['1_int_int'] = [v1, v2, p, n]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
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
    p_val = model['p'][x]
    v1_curr = model['v1'][x]
    v1_p = model['v1'][p_val]
    n_v1_p = model['n'][v1_p]
    v2_curr = model['v2'][x]
    v2_p = model['v2'][p_val]
    n_v2_p = model['n'][v2_p]
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
pfp_dict = {}
pfp_dict['reach'] = '''
                    (=>  
                    (ite (= (v1 {primary_arg}) (v2 {primary_arg}))
                         true
                         (and (and (reach (p {primary_arg})) (lemma (p {primary_arg}) {rest_args}))
                              (and (not (= (v1 (p {primary_arg})) {nil})) 
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
const = [nil, c]

###########################################################################################################################
# Lemma synthesis stub to follow: must be replaced with a uniform function call between all examples.
##########################################################################################################################
# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []
elems = [*range(5)]

cex_models = []
config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True
config_params['cex_models'] = cex_models

fresh = Int('fresh')
skolem = Int('skolem')

# continuously get valid lemmas until VC has been proven
while True:
    lemma = getSygusOutput(elems, config_params, fcts_z3, axioms_python, axioms_z3,
                           valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                           vc(x), 'reachability')
    rhs_lemma = translateLemma(lemma[0], fcts_z3)
    index = int(lemma[1][-2])
    lhs_lemma = fcts_z3['recpreds-loc_1_int_bool'][index](fresh)
    z3py_lemma = Implies(lhs_lemma, rhs_lemma)
    print('proposed lemma: ' + str(z3py_lemma))
    if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
        print('lemma has already been proposed')
        exit(0)
        #continue
    lemma_deref = [skolem, v1(skolem), v2(skolem), p(skolem), v1(p(skolem)), v2(p(skolem))]
    (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, valid_lemmas, unfold_recdefs_z3, lemma_deref, const, z3py_lemma, True)
    if false_model_z3 != None:
        print('proposed lemma cannot be proved.')
        invalid_lemmas = invalid_lemmas + [ z3py_lemma ]
        use_cex_models = config_params.get('use_cex_models', False)
        if use_cex_models:
            cex_models = cex_models + [false_model_dict]
    else:
        valid_lemmas = valid_lemmas + [ z3py_lemma ]
        # Reset countermodels and invalid lemmas to empty because we have additional information to retry those proofs.
        cex_models = []
        invalid_lemmas = []
    # Update countermodels before next round of synthesis
    config_params['cex_models'] = cex_models