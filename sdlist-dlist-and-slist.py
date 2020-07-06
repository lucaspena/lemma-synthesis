from z3 import *
from false_models import *
from lemma_synthesis import *
from lemsynth_utils import *

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
x, ret, nil = Ints('x ret nil')
fcts_z3['0_int'] = [x, ret, nil]

######## Section 2
# Functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil
prev_nil_z3 = prev(nil) == nil
# key_nil_z3 = key(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

def prev_nil_python(model):
    return model['prev'][model['nil']] == model['nil']

# def key_nil_python(model):
#     return model['key'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
# TODO: what to do about -1 for key axioms?
fcts_z3['1_int_int'] = [next, prev, key]
axioms_z3['0'] = [next_nil_z3, prev_nil_z3]
axioms_python['0'] = [next_nil_python, prev_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
dlist = Function('dlist', IntSort(), BoolSort())
slist = Function('slist', IntSort(), BoolSort())
sdlist = Function('sdlist', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def udlist_z3(x):
    return Iff( dlist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(prev(next(x)) == x, dlist(next(x)))) ))

def uslist_z3(x):
    return Iff( slist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(key(x) <= key(next(x)), slist(next(x)))) ))

def usdlist_z3(x):
    return Iff( sdlist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(key(x) <= key(next(x)),
                                                prev(next(x)) == x, sdlist(next(x)))) ))

# Python versions for finding valuation on true models
def udlist_python(x, model):
    if x == model['nil']:
        return True
    elif model['next'][x] == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        doubly_linked_cond = model['prev'][next_val] == x
        return doubly_linked_cond and model['dlist'][next_val]

def uslist_python(x, model):
    if x == model['nil']:
        return True
    elif model['next'][x] == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slist'][next_val]

def usdlist_python(x, model):
    if x == model['nil']:
        return True
    elif model['next'][x] == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        doubly_linked_cond = model['prev'][next_val] == x
        return sorted_cond and doubly_linked_cond and model['sdlist'][next_val]

unfold_recdefs_z3['1_int_bool'] = [udlist_z3, uslist_z3, usdlist_z3]
unfold_recdefs_python['1_int_bool'] = [udlist_python, uslist_python, usdlist_python]
pfp_dict = {}
pfp_dict['dlist'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (ite (= (next {primary_arg}) {nil})
              true
              (and (= (prev (next {primary_arg})) {primary_arg})
                   (and (dlist {primary_arg}) (lemma (next {primary_arg}) {rest_args})) )))
    (lemma {primary_arg} {rest_args}))'''
    
pfp_dict['slist'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (ite (= (next {primary_arg}) {nil})
              true
              (and (<= (key {primary_arg}) (key (next {primary_arg})))
                   (and (slist {primary_arg}) (lemma (next {primary_arg}) {rest_args})))))
    (lemma {primary_arg} {rest_args}))'''

pfp_dict['sdlist'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (ite (= (next {primary_arg}) {nil})
              true
              (and (and (<= (key {primary_arg}) (key (next {primary_arg})))
                        (and (sdlist {primary_arg}) (lemma (next {primary_arg}) {rest_args})))
                    (= (prev (next {primary_arg})) {primary_arg}))))
    (lemma {primary_arg} {rest_args}))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [dlist, slist, sdlist]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, ret):
    return IteBool(x == nil, ret == nil, ret == next(x))

def vc(x, ret):
    return Implies( sdlist(x),
                    Implies(pgm(x, ret), And(dlist(ret), slist(ret))))

deref = [x]
const = [nil]

# End of input
###########################################################################################################################
# Lemma synthesis stub to follow: must be replaced with a uniform function call between all examples.
##########################################################################################################################
# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

cex_models = []
config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True
config_params['cex_models'] = cex_models

fresh = Int('fresh')
skolem = Int('skolem')

# continuously get valid lemmas until VC has been proven
while True:
    lemma = getSygusOutput([], config_params, fcts_z3, axioms_python, axioms_z3,
                           valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                           vc(x,ret), 'sdlist-dlist-and-slist')
    rhs_lemma = translateLemma(lemma[0], fcts_z3)
    index = int(lemma[1][-2])
    lhs_lemma = fcts_z3['recpreds-loc_1_int_bool'][index](fresh)
    z3py_lemma = Implies(lhs_lemma, rhs_lemma)
    print('proposed lemma: ' + str(z3py_lemma))
    if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
        print('lemma has already been proposed')
        continue
    lemma_deref = [skolem, next(skolem), prev(skolem)]
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

