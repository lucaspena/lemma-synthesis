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
x, ret, nil = Ints('x ret nil')
fcts_z3['0_int'] = [x, nil]

####### Section 2
# Functions
left = Function('left', IntSort(), IntSort())
right = Function('right', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for left, right, and key of nil
left_nil_z3 = left(nil) == nil
right_nil_z3 = right(nil) == nil
key_nil_z3 = key(nil) == -1

fcts_z3['1_int_int'] = [left, right, key]
axioms_z3['0'] = [left_nil_z3, right_nil_z3, key_nil_z3]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
maxheap = Function('maxheap', IntSort(), BoolSort())
tree = Function('tree', IntSort(), BoolSort())

def umaxheap_z3(x):
    return Iff( maxheap(x), IteBool( x == nil,
                                     True,
                                     And( 0 < key(x), key(x) < 100,
                                          maxheap(left(x)), maxheap(right(x)),
                                          key(left(x)) <= key(x),
                                          key(right(x)) <= key(x) ) ) )

def utree_z3(x):
    return Iff( tree(x), IteBool( x == nil,
                                 True,
                                 And( 0 < key(x), key(x) < 100,
                                      tree(left(x)), tree(right(x)) ) ) )

def umaxheap_python(x, model):
    if x == model['nil']:
        return True
    else:
        key = model['key'][x]
        left = model['left'][x]
        right = model['right'][x]
        key_bound_cond = 0 < key and key < 100
        rec_cond = model['maxheap'][left] and model['maxheap'][right]
        maxheap_cond = model['key'][left] <= key and model['key'][right] <= key
        return key_bound_cond and rec_cond and maxheap_cond

def utree_python(x, model):
    if x == model['nil']:
        return True
    else:
        key = model['key'][x]
        left = model['left'][x]
        right = model['right'][x]
        key_bound_cond = 0 < key and key < 100
        rec_cond = model['tree'][left] and model['tree'][right]
        return key_bound_cond and rec_cond

unfold_recdefs_z3['1_int_bool'] = [umaxheap_z3, utree_z3]
unfold_recdefs_python['1_int_bool'] = [umaxheap_python, utree_python]
fcts_z3['recpreds-loc_1_int_bool'] = [maxheap, tree]

pfp_dict = {}
pfp_dict['maxheap'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (and (< 0 (key {primary_arg})) (< (key {primary_arg}) 100)
              (and (maxheap (left {primary_arg})) (lemma (left {primary_arg}) {rest_args}))
              (and (maxheap (right {primary_arg})) (lemma (right {primary_arg}) {rest_args}))
              (<= (key (left {primary_arg})) (key {primary_arg}))
              (<= (key (right {primary_arg})) (key {primary_arg}))
         )
    )
    (lemma {primary_arg} {rest_args})
)
'''
pfp_dict['tree'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (and (< 0 (key {primary_arg})) (< (key {primary_arg}) 100)
              (and (tree (left {primary_arg})) (lemma (left {primary_arg}) {rest_args}))
              (and (tree (right {primary_arg})) (lemma (right {primary_arg}) {rest_args}))
         )
    )
    (lemma {primary_arg} {rest_args})
)
'''

############# Section 5
# Program, VC, and Instantiation

def pgm(x, ret):
    return IteBool(x == nil, ret == nil, ret == right(x))

def vc(x, ret):
    return Implies( maxheap(x),
                    Implies(pgm(x, ret), tree(ret)))

deref = [x, left(x), right(x)]
const = [nil]
verification_condition = vc(x, ret)

# End of input

######################
# Lemma synthesis stub 
######################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'maxheap-tree'

synth_dict = {}

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, config_params, synth_dict)

