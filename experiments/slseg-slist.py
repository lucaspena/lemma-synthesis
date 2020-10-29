from z3 import *
from set_sort import *
from lemma_synthesis import *
from true_models import *

raise NotImplementedError

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
x, y, z, nil = Ints('x y z nil')
fcts_z3['0_int'] = [x, y, z, nil]

####### Section 2
# Functions
next = Function('next', IntSort(), IntSort())
next_p = Function('next_p', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axiom for next' with ite
def next_p_fct_axiom_z3(w):
    return IteBool(w == y, next_p(w) == z, next_p(w) == next(w))

# Python version for the above axiom for true model generation
def next_p_fct_axiom_python(w,model):
    if w == model['y']:
        return model['next_p'][w] == model['z']
    else:
        return model['next_p'][w] == model['next'][w]

# Axioms for next and next' of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil
next_p_nil_z3 = next_p(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

def next_p_nil_python(model):
    return model['next_p'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
fcts_z3['1_int_int'] = [next, next_p, key]
axioms_z3['0'] = [next_nil_z3, next_p_nil_z3]
axioms_z3['1_int'] = [next_p_fct_axiom_z3]
axioms_python['0'] = [next_nil_python, next_p_nil_python]
axioms_python['1_int'] = [next_p_fct_axiom_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
SetIntSort = createSetSort('int')
# slist = Function('slist', IntSort(), BoolSort())
# slseg_y = Function('slseg_y', IntSort(), BoolSort())
slist_p = Function('slist_p', IntSort(), BoolSort())
slseg_y_p = Function('slseg_y_p', IntSort(), BoolSort())
# keys = Function('keys', IntSort(), SetIntSort)
keys_p = Function('keys_p', IntSort(), SetIntSort)
# lsegkeys_y = Function('lsegkeys_y', IntSort(), SetIntSort)
lsegkeys_y_p = Function('lsegkeys_y_p', IntSort(), SetIntSort)
# max_lsegkeys_y = Function('max_lsegkeys_y', IntSort(), IntSort())
max_lsegkeys_y_p = Function('max_lsegkeys_y_p', IntSort(), IntSort())
# min_keys_y = Function('min_keys_y', IntSort(), IntSort())
min_keys_p = Function('min_keys_p', IntSort(), IntSort())

############ Section 4
# Unfolding recursive definitions
# TODO: add support for recursive functions

# Macros for unfolding recursive definitions
def uslist_p_z3(x):
    return Iff( slist_p(x), IteBool( x == nil,
                                     True,
                                     IteBool( next_p(x) == nil,
                                              True,
                                              And(key(x) <= key(next_p(x)), slist_p(next_p(x)))) ))

def uslseg_y_p_z3(x):
    return Iff( slseg_y_p(x), IteBool( x == y,
                                       True,
                                       IteBool( next_p(x) == y,
                                                True,
                                                And(key(x) <= key(next_p(x)), slseg_y_p(next_p(x)))) ))

def ukeys_p_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    then_case = Implies(is_nil, keys_p(x) == emptyset)
    else_case = Implies(Not(is_nil), keys_p(x) == SetAdd(keys_p(next_p(x)), key(x)))
    return And(then_case, else_case)

def ulsegkeys_y_p_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_y = x == y
    then_case = Implies(is_y, lsegkeys_y_p(x) == emptyset)
    else_case = Implies(Not(is_y), lsegkeys_y_p(x) == SetAdd(lsegkeys_y_p(next_p(x)), key(x)))
    return And(then_case, else_case)

def umax_lsegkeys_y_p_z3(x):
    is_nil = x == nil
    is_y = x == y
    max_rec = If(key(x) > max_lsegkeys_y_p(next_p(x)), key(x), max_lsegkeys_y_p(next_p(x)))
    then_case = Implies(Or(is_nil, is_y), max_lsegkeys_y_p(x) == key(y))
    else_case = Implies(And(Not(is_nil), Not(is_y)), max_lsegkeys_y_p(x) == max_rec)
    return And(then_case, else_case)

def umin_keys_p_z3(x):
    is_nil = x == nil
    max_rec = If(key(x) < min_keys_p(next_p(x)), key(x), min_keys_p(next_p(x)))
    then_case = Implies(is_nil, min_keys_p(x) == key(x))
    else_case = Implies(Not(is_nil), min_keys_p(x) == max_rec)
    return And(then_case, else_case)

# Python versions for finding valuation on true models
def uslist_p_python(x, model):
    if x == model['nil']:
        return True
    elif model['next_p'][x] == model['nil']:
        return True
    else:
        next_val = model['next_p'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slist_p'][next_val]

def uslseg_y_p_python(x, model):
    if x == model['y']:
        return True
    elif model['next_p'][x] == model['y']:
        return True
    else:
        next_val = model['next_p'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slseg_y_p'][next_val]

def ukeys_p_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next_p'][x]
        curr_key = model['key'][x]
        next_keys = model['keys_p'][next_val]
        return {curr_key} | next_keys

def ulsegkeys_y_p_python(x, model):
    if x == model['y']:
        return set()
    else:
        next_val = model['next_p'][x]
        curr_key = model['key'][x]
        next_lsegkeys = model['lsegkeys_y_p'][next_val]
        return {curr_key} | next_lsegkeys

def umax_lsegkeys_y_p_python(x, model):
    if x == model['nil'] or x == model['y']:
        return model['key'][model['y']]
    else:
        next_val = model['next_p'][x]
        next_max = model['max_lsegkeys_y_p'][next_val]
        if model['key'][x] > next_max:
            return model['key'][x]
        else:
            return next_max

def umin_keys_p_python(x, model):
    if x == model['nil']:
        return model['key'][model['x']]
    else:
        next_val = model['next_p'][x]
        next_min = model['min_keys_p'][next_val]
        if model['key'][x] < next_min:
            return model['key'][x]
        else:
            return next_min

unfold_recdefs_z3['1_int_bool'] = [uslist_p_z3, uslseg_y_p_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_p_z3, ulsegkeys_y_p_z3]
unfold_recdefs_z3['1_int_int'] = [umax_lsegkeys_y_p_z3, umin_keys_p_z3]
unfold_recdefs_python['1_int_bool'] = [uslist_p_python, uslseg_y_p_python]
unfold_recdefs_python['1_int_set-int'] = [ukeys_p_python, ulsegkeys_y_p_python]
unfold_recdefs_python['1_int_int'] = [umax_lsegkeys_y_p_python, umin_keys_p_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [slist_p, slseg_y_p]
fcts_z3['recfunctions-loc_1_int_int'] = [max_lsegkeys_y_p, min_keys_p]
fcts_z3['recfunctions-loc_1_int_set-int'] = [keys_p, lsegkeys_y_p]

############# Section 5
# Program, VC, and Instantiation

# lemma: slseg_p(x, y) /\ slist_p(y) /\ maxlskeys_p(x, y) <= minkeys_p(y) => slist(x)

def pgm(x, y, z):
    keys_cond = max_lsegkeys_y_p(x) <= min_keys_p(z)
    return And( slseg_y_p(x), next(y) == nil, slist_p(z), keys_cond )

def vc(x, y, z):
    return Implies( pgm(x, y, z), slist_p(x) )

deref = [x]
const = [nil, y]

elems = [*range(2)]
num_true_models = 10

fresh = Int('fresh')
# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

# continuously get valid lemmas until VC has been proven
while True:
    lemmas = getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3,
                            valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                            vc(x,y,z), 'slseg-slist')
    # print('Lemmas: {}'.format(lemmas))
    lemmas = [Implies(slseg_y_p(fresh), Implies(slist_p(y), Implies(max_lsegkeys_y_p(x) <= min_keys_p(y), slist_p(x))))]
    for lemma in lemmas:
        # insert_tmp = Function('insert_tmp', IntSort(), SetIntSort, SetIntSort)
        # addl_decls = { 'insert': insert_tmp }
        # swaps = { insert_tmp: SetAdd }
        # z3py_lemma = translateLemma(lemma, fcts_z3, addl_decls, swaps)
        z3py_lemma = lemma
        print(z3py_lemma)
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
