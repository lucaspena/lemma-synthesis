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
x, k, nil = Ints('x k nil')
skolem = Int('skolem')
fcts_z3['0_int'] = [x, k, nil, skolem]

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
# TODO: add support for recursive functions
SetIntSort = createSetSort('int')
slist = Function('slist', IntSort(), BoolSort())
slist_find_k = Function('slist_find_k', IntSort(), BoolSort())
keys = Function('keys', IntSort(), SetIntSort)

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))))

def uslist_z3(x):
    return Iff( slist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(key(x) <= key(next(x)), slist(next(x)))) ))

def uslist_find_k_z3(x):
    return Iff( slist_find_k(x), IteBool( x == nil,
                                          False,
                                          IteBool( key(x) == k,
                                                   True,
                                                   IteBool( key(x) > k,
                                                            False,
                                                            slist_find_k(next(x)) ))))

def ukeys_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    then_case = Implies(is_nil, keys(x) == emptyset)
    else_case = Implies(Not(is_nil), keys(x) == SetAdd(keys(next(x)), key(x)))
    return And(then_case, else_case)

# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def uslist_python(x, model):
    if x == model['nil']:
        return True
    elif model['next'][x] == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slist'][next_val]

def uslist_find_k_python(x, model):
    if x == model['nil']:
        return False
    elif model['key'][x] == model['k']:
        return True
    elif model['key'][x] > model['k']:
        return False
    else:
        next_val = model['next'][x]
        return model['slist_find_k'][next_val]

def ukeys_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        next_keys = model['keys'][next_val]
        return {curr_key} | next_keys

unfold_recdefs_z3['1_int_bool'] = [uslist_z3, uslist_find_k_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_z3]
unfold_recdefs_python['1_int_bool'] = [uslist_python, uslist_find_k_python]
unfold_recdefs_python['1_int_set-int'] = [ukeys_python]
pfp_dict = {}
pfp_dict['slist'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (ite (= (next {primary_arg}) {nil})
              true
              (and (<= (key {primary_arg}) (key (next {primary_arg})))
                   (and (slist (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))))
    (lemma {primary_arg} {rest_args}))'''

pfp_dict['slist_find_k'] = '''
(=> (ite (= {primary_arg} {nil})
         false
         (ite (= (key {primary_arg}) {k})
              true
              (ite (> (key {primary_arg}) {k}) 
              false 
              (and (slist_find_k (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))))
    (lemma {primary_arg} {rest_args}))'''

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [slist, slist_find_k]
fcts_z3['recfunctions-loc_1_int_set-int'] = [keys]

############# Section 5
# Program, VC, and Instantiation

def vc(x, k):
    return Implies( slist(x),
                    Implies(k < key(x), Not(IsMember(k, keys(x)))) )

deref = [x, next(x), skolem, next(skolem)]
const = [nil, k]
verification_condition = vc(x,k)

# End of input

###########################################################################################################################
# Lemma synthesis stub 
##########################################################################################################################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'slist-find'

synth_dict = {}
skolem = Int('skolem')
# Must be added as this particular example requires one more level of instantiation than is apparent.
synth_dict['lemma_deref'] = [next(skolem)]

synth_dict['translate_lemma_addl_decls'] = {}
synth_dict['translate_lemma_replace_fcts'] = {}
synth_dict['translate_lemma_swap_fcts'] = {}
# TODO: replace all the swap and replace declarations below by having translateLemma use substituteSubformula instead of swap_fcts and replace_fcts
# Must add the declarations below in order to translate 'member' in cvc4 to 'ismember' in z3
# This is an uninterpreted function with the same signature as that of set membership
membership = Function('membership', IntSort(), SetIntSort, BoolSort())
# This is say that 'member' in cvc4 should be replaced by the uninterpreted function 'membership'
synth_dict['translate_lemma_addl_decls']['member'] = membership
# This is to say that the uninterpreted function 'membership' should be substituted away to 'IsMember' in z3
synth_dict['translate_lemma_replace_fcts'][membership] = IsMember
# Similarly for converting 'insert' in cvc4 to 'SetAdd' in z3
# The corresponding function must be placed in swap_fcts rather than replace_fcts because the order of arguments is different in cvc4 and z3 
insertion = Function('insertion', IntSort(), SetIntSort, SetIntSort)
synth_dict['translate_lemma_addl_decls']['insert'] = insertion
synth_dict['translate_lemma_swap_fcts'][insertion] = SetAdd

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, config_params, synth_dict)
