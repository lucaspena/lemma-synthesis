from z3 import *
from set_sort import *
from lemma_synthesis import *
from true_models import *

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
x, y, yp, nil = Ints('x y yp nil')
fcts_z3['0_int'] = [x, y, yp, nil]

####### Section 2
# Functions
next = Function('next', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and next' of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
fcts_z3['1_int_int'] = [next, key]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
SetIntSort = createSetSort('int')
slseg_y = Function('slseg_y', IntSort(), BoolSort())
slseg_yp = Function('slseg_yp', IntSort(), BoolSort())
keys = Function('keys', IntSort(), SetIntSort)
lsegkeys_y = Function('lsegkeys_y', IntSort(), SetIntSort)
lsegkeys_yp = Function('lsegkeys_yp', IntSort(), SetIntSort)
max_lsegkeys_y = Function('max_lsegkeys_y', IntSort(), IntSort())

############ Section 4
# Unfolding recursive definitions
# TODO: add support for recursive functions

# Macros for unfolding recursive definitions
def uslseg_y_z3(x):
    return Iff( slseg_y(x), IteBool( x == y,
                                     True,
                                     IteBool( next(x) == y,
                                              True,
                                              And(key(x) <= key(next(x)), slseg_y(next(x)))) ))

def uslseg_yp_z3(x):
    return Iff( slseg_y(x), IteBool( x == yp,
                                     True,
                                     IteBool( next(x) == yp,
                                              True,
                                              And(key(x) <= key(next(x)), slseg_yp(next(x)))) ))

def ukeys_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    then_case = Implies(is_nil, keys(x) == emptyset)
    else_case = Implies(Not(is_nil), keys(x) == SetAdd(keys(next(x)), key(x)))
    return And(then_case, else_case)

def ulsegkeys_y_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_y = x == y
    # in_domain = lseg_y(x)
    then_case = Implies(is_y, lsegkeys_y(x) == emptyset)
    else_case = Implies(Not(is_y), lsegkeys_y(x) == SetAdd(lsegkeys_y(next(x)), key(x)))
    return And(then_case, else_case)

def ulsegkeys_yp_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_yp = x == yp
    # in_domain = lseg_yp(x)
    then_case = Implies(is_yp, lsegkeys_yp(x) == emptyset)
    else_case = Implies(Not(is_yp), lsegkeys_yp(x) == SetAdd(lsegkeys_yp(next(x)), key(x)))
    return And(then_case, else_case)

def umax_lsegkeys_y_z3(x):
    is_nil = x == nil
    is_y = x == y
    max_rec = If(key(x) > max_lsegkeys_y(next(x)), key(x), max_lsegkeys_y(next(x)))
    then_case = Implies(Or(is_nil, is_y), max_lsegkeys_y(x) == key(y))
    else_case = Implies(And(Not(is_nil), Not(is_y)), max_lsegkeys_y(x) == max_rec)
    return And(then_case, else_case)

# Python versions for finding valuation on true models
def uslseg_y_python(x, model):
    if x == model['y']:
        return True
    elif model['next'][x] == model['y']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slseg_y'][next_val]

def uslseg_yp_python(x, model):
    if x == model['yp']:
        return True
    elif model['next'][x] == model['yp']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slseg_yp'][next_val]

def ukeys_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_keys = model['keys'][x]
        next_keys = model['keys'][next_val]
        return {curr_key} | next_keys

def ulsegkeys_y_python(x, model):
    if x == model['y']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_lsegkeys = model['lsegkeys_y'][x]
        next_lsegkeys = model['lsegkeys_y'][next_val]
        # curr_lseg = model['lseg_y'][x]
        return {curr_key} | next_lsegkeys

def ulsegkeys_yp_python(x, model):
    if x == model['yp']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_lsegkeys = model['lsegkeys_yp'][x]
        next_lsegkeys = model['lsegkeys_yp'][next_val]
        # curr_lseg = model['lseg_yp'][x]
        return {curr_key} | next_lsegkeys

def umax_lsegkeys_y_python(x, model):
    if x == model['nil'] or x == model['y']:
        return model['key'][model['y']]
    else:
        next_val = model['next'][x]
        next_max = model['max_lsegkeys_y'][next_val]
        if model['key'][x] > next_max:
            return model['key'][x]
        else:
            return next_max

unfold_recdefs_z3['1_int_bool'] = [uslseg_y_z3, uslseg_yp_z3]
unfold_recdefs_z3['1_int_int'] = [umax_lsegkeys_y_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_z3, ulsegkeys_y_z3, ulsegkeys_yp_z3]
unfold_recdefs_python['1_int_bool'] = [uslseg_y_python, uslseg_yp_python]
unfold_recdefs_python['1_int_set-int'] = [ukeys_python, ulsegkeys_y_python, ulsegkeys_yp_python]
unfold_recdefs_python['1_int_int'] = [umax_lsegkeys_y_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [slseg_y, slseg_yp]
fcts_z3['recfunctions-loc_1_int_int'] = [max_lsegkeys_y]
fcts_z3['recfunctions-loc_1_int_set-int'] = [keys, lsegkeys_y, lsegkeys_yp]

############# Section 5
# Program, VC, and Instantiation

# lemma: slsegy(x) /\ next(y) = yp => ( max(lseg-keys(x, y)) <= key(yp) => slsegyp(x)

def pgm(x, y, yp):
    precondition = And(slseg_y(x), keys(x) == SetUnion(lsegkeys_y(x), keys(y)))
    program_body = next(y) == yp
    return And(precondition, program_body)

def vc(x, y, yp):
    return Implies( pgm(x, y, yp), keys(x) == SetUnion(lsegkeys_yp(x), keys(yp)) )

deref = [x, next(x)]
const = [nil, y, yp]

elems = [*range(2)]
num_true_models = 10

# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

# continuously get valid lemmas until VC has been proven
while True:
    lemmas = getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3,
                            valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                            vc(x,y,yp), 'slseg-keys')
    print('Lemmas: {}'.format(lemmas))
    for lemma in lemmas:
        insert_tmp = Function('insert_tmp', IntSort(), SetIntSort, SetIntSort)
        addl_decls = { 'insert': insert_tmp }
        swaps = { insert_tmp: SetAdd }
        z3py_lemma = translateLemma(lemma, fcts_z3, addl_decls, swaps)
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
