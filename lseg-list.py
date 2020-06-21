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

def IteSet(b, l, r):
    return If(b, l, r)

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
fcts_z3['1_int_int'] = [next, next_p]
axioms_z3['0'] = [next_nil_z3, next_p_nil_z3]
axioms_z3['1_int'] = [next_p_fct_axiom_z3]
axioms_python['0'] = [next_nil_python, next_p_nil_python]
axioms_python['1_int'] = [next_p_fct_axiom_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
list = Function('list', IntSort(), BoolSort())
lsegy = Function('lsegy', IntSort(), BoolSort())
list_p = Function('list_p', IntSort(), BoolSort())
lsegy_p = Function('lsegy_p', IntSort(), BoolSort())


SetIntSort = createSetSort('int')
hlist = Function('hlist', IntSort(), SetIntSort)
hlsegy = Function('hlsegy', IntSort(), SetIntSort)
hlist_p = Function('hlist_p', IntSort(), SetIntSort)
hlsegy_p = Function('hlsegy_p', IntSort(), SetIntSort)

# Creating such pairs without a signature is fine.
# This implementation only supports unary recursive definitions over the foreground sort for the forseeable future
# The relationship is obviously systematic. The frame definitions are named by appending an 'h' to the name of the original definition
# The primed definitions are named by appending a '_p' to the end of the name of the original definition
recdef_frame_prime_triples = [(list, hlist, list_p), (lsegy, hlsegy, lsegy_p)]

# Axioms about recdefs
lsegy_nil_z3 = lsegy(nil) == False
lsegy_p_nil_z3 = lsegy_p(nil) == False # Obviously not needed, and wrong unless y != nil. But we seem to get by without it. Ignoring for now.

# Python versions of axioms
def lsegy_nil_python(model):
    return model['lsegy'][model['nil']] == False
def lsegy_p_nil_python(model):
    return model['lsegy_p'][model['nil']] == False

axioms_z3['0'] = axioms_z3['0'] + [lsegy_nil_z3, lsegy_p_nil_z3]
axioms_python['0'] = axioms_python['0'] + [lsegy_nil_python, lsegy_p_nil_python]

############ Section 4
# Unfolding recursive definitions
# TODO: add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))) )

def ulsegy_z3(x):
    return Iff( lsegy(x), IteBool(x == y, True, lsegy(next(x))) )

def ulist_p_z3(x):
    return Iff( list_p(x), IteBool(x == nil, True, list_p(next_p(x))) )

def ulsegy_p_z3(x):
    return Iff( lsegy_p(x), IteBool(x == y, True, lsegy_p(next_p(x))) )

# Heaplet definitions
def uhlist_z3(x):
    emptyset_intsort = getSortEmptySet(SetIntSort)
    return hlist(x) == IteSet(x == nil, emptyset_intsort, SetAdd(hlist(next(x)),x) )

def uhlsegy_z3(x):
    emptyset_intsort = getSortEmptySet(SetIntSort)
    return hlsegy(x) == IteSet(x == y, emptyset_intsort, SetAdd(hlsegy(next(x)),x) )

def uhlist_p_z3(x):
    emptyset_intsort = getSortEmptySet(SetIntSort)
    return hlist_p(x) == IteSet(x == nil, emptyset_intsort, SetAdd(hlist_p(next_p(x)),x) )

def uhlsegy_p_z3(x):
    emptyset_intsort = getSortEmptySet(SetIntSort)
    return hlsegy_p(x) == IteSet(x == y, emptyset_intsort, SetAdd(hlsegy_p(next_p(x)),x) )


# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def ulsegy_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next'][x]
        return model['lsegy'][next_val]

def ulist_p_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next_p'][x]
        return model['list_p'][next_val]

def ulsegy_p_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next_p'][x]
        return model['lsegy_p'][next_val]

# Heaplet definitions
def uhlist_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next'][x]
        return {x} | model['hlist'][next_val] # | is shorthand for set union

def uhlsegy_python(x, model):
    if x == model['y']:
        return set()
    else:
        next_val = model['next'][x]
        return {x} | model['hlsegy'][next_val]

def uhlist_p_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next_p'][x]
        return {x} | model['hlist_p'][next_val] # | is shorthand for set union

def uhlsegy_p_python(x, model):
    if x == model['y']:
        return set()
    else:
        next_val = model['next_p'][x]
        return {x} | model['hlsegy_p'][next_val]

unfold_recdefs_z3['1_int_bool'] = [ulist_z3, ulsegy_z3, ulist_p_z3, ulsegy_p_z3]
unfold_recdefs_z3['1_int_set-int'] = [uhlist_z3, uhlsegy_z3, uhlist_p_z3, uhlsegy_p_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, ulsegy_python, ulist_p_python, ulsegy_p_python]
unfold_recdefs_python['1_int_set-int'] = [uhlist_python, uhlsegy_python, uhlist_p_python, uhlsegy_p_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [list, lsegy, list_p, lsegy_p]
fcts_z3['recfunctions-loc_1_int_set-int'] = [hlist, hlsegy, hlist_p, hlsegy_p]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, y, z):
    emptyset_intsort = getSortEmptySet(SetIntSort)
    lsegxy_star_listy = SetIntersect(hlsegy(x),hlist(y)) == emptyset_intsort
    listy_star_listz = SetIntersect(hlist(y),hlist(z)) == emptyset_intsort
    #lsegxy_star_listz = SetIntersect(hlsegy(x),hlist(z)) == emptyset_intsort
    lsegxy_star_listy_star_listz = And(lsegxy_star_listy,listy_star_listz) #,lsegxy_star_listz)
    return And( lsegy(x), next(y) == nil, Not(y == nil), list(z), lsegxy_star_listy_star_listz)

def vc(x, y, z):
    return Implies( pgm(x, y, z), list_p(x) )

deref = [x, next(x), z]
const = [nil, y]
modified_set = {y} # Note that this is a python set with the elements themselves
# being z3 terms. This is weird and needs to cleaned up.

# Must have some sort of general treatment for converting the modified set to Z3
# regardless of whether it is a finite set or represented by a recursive
# definition, or a mix of both
modified_set_z3 = getSortEmptySet(SetIntSort)
for elem in modified_set:
    modified_set_z3 = SetAdd(modified_set_z3, elem)

# Frame rules
# TODO: generate these in a 'more automatic' way
# Currently the rules are completely instantiated and given along with the VC as 'nullary' axioms_z3
for term in deref + const:
    for recdef_frame_prime_triple in recdef_frame_prime_triples:
        (recdef, hrecdef, recdef_p) = recdef_frame_prime_triple
        emptyset_intsort = getSortEmptySet(SetIntSort)
        non_intersection = SetIntersect(hrecdef(term), modified_set_z3) == emptyset_intsort
        frame_rule = Implies(And(recdef(term), non_intersection), recdef_p(term))
        # Add frame rule axioms_z3['0']
        axioms_z3['0'] = axioms_z3['0'] + [frame_rule]

elems = [*range(3)]
num_true_models = 10

# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

# continuously get valid lemmas until VC has been proven
while True:
    lemmas = getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3,
                            valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                            vc(x,y,z), 'lseg-list')
    #lemmas = lemmas + ['(define-fun lemma ((x Int) (nil Int) (y Int)) Bool (=> (lsegy_p x) (=> (list_p y) (list_p x))))']
    print('Lemmas: {}'.format(lemmas))
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
