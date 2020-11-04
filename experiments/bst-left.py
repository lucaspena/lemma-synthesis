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

def min3(x, y, z):
    return If(And(x <= y, x <= z), x, If(And(y <= x, y <= z), y, z))

def max3(x, y, z):
    return If(And(x >= y, x >= z), x, If(And(y >= x, y >= z), y, z))

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
x, y, nil = Ints('x y nil')
fcts_z3['0_int'] = [x, y, nil]

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
SetIntSort = createSetSort('int')
bst = Function('bst', IntSort(), BoolSort())
minr = Function('minr', IntSort(), IntSort())
maxr = Function('maxr', IntSort(), IntSort())
keys = Function('keys', IntSort(), SetIntSort)

def ubst_z3(x):
    return Iff( bst(x), IteBool( x == nil,
                                 True,
                                 And( 0 < key(x), key(x) < 100,
                                      bst(left(x)), bst(right(x)),
                                      maxr(left(x)) <= key(x),
                                      key(x) <= minr(right(x)) ) ) )

def uminr_z3(x):
    is_nil = x == nil
    then_case = Implies(is_nil, minr(x) == -1)
    else_case = Implies(Not(is_nil), minr(x) == min3(key(x), minr(left(x)), minr(right(x))))
    return And(then_case, else_case)

def umaxr_z3(x):
    is_nil = x == nil
    then_case = Implies(is_nil, maxr(x) == 101)
    else_case = Implies(Not(is_nil), maxr(x) == max3(key(x), minr(left(x)), minr(right(x))))
    return And(then_case, else_case)

def ukeys_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    in_domain = bst(x)
    then_case = Implies(is_nil, keys(x) == emptyset)
    else_case = Implies(Not(is_nil), keys(x) == SetAdd(SetUnion(keys(left(x)), keys(right(x))),
                                                       key(x)))
    return And(then_case, else_case)

# No true models so no need for python versions

unfold_recdefs_z3['1_int_bool'] = [ubst_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_z3]
unfold_recdefs_z3['1_int_int'] = [uminr_z3, umaxr_z3]

fcts_z3['recpreds-loc_1_int_bool'] = [bst]
fcts_z3['recfunctions-loc_1_int_set-int'] = [keys]
fcts_z3['recfunctions-loc_1_int_int'] = [minr, maxr]

pfp_dict = {}
pfp_dict['bst'] = '''
(=> (ite (= {primary_arg} {nil})
         true
         (and (< 0 (key {primary_arg})) (< (key {primary_arg}) 100)
              (and (bst (left {primary_arg})) (lemma (left {primary_arg}) {rest_args}))
              (and (bst (right {primary_arg})) (lemma (right {primary_arg}) {rest_args}))
              (<= (maxr (left {primary_arg})) (key {primary_arg}))
              (<= (key {primary_arg}) (minr (right {primary_arg})))
         )
    )
    (lemma {primary_arg} {rest_args})
)
'''

############# Section 5
# Program, VC, and Instantiation

def vc(x, y):
    rec = bst(x)
    lhs = And( IsMember(key(y), keys(x)), key(y) < key(x) )
    rhs = IsMember(key(y), keys(left(x)))
    return Implies( rec, Implies ( lhs, rhs ) )

deref = [x, left(x), right(x)]
const = [nil, y]
verification_condition = vc(x, y)

# End of input

######################
# Lemma synthesis stub 
######################

config_params = {'mode': 'random', 'num_true_models':0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True

name = 'bst-left'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

synth_dict = {}
synth_dict['translate_lemma_addl_decls'] = {}
synth_dict['translate_lemma_replace_fcts'] = {}
synth_dict['translate_lemma_swap_fcts'] = {}
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

solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, verification_condition, name, grammar_string, config_params, synth_dict)
