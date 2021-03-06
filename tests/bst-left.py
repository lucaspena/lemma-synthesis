import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x = Var('x', fgsort)
nil = Const('nil', fgsort)
k = Const('k', intsort)
key = Function('key', fgsort, intsort)
keys = Function('keys', fgsort, intsetsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
minr = Function('minr', fgsort, intsort)
maxr = Function('maxr', fgsort, intsort)
bst = RecFunction('bst', fgsort, boolsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
AddRecDefinition(bst, x, If(x == nil, True,
                            And(0 < key(x),
                                And(key(x) < 100,
                                    And(bst(lft(x)),
                                        And(bst(rght(x)),
                                            And(maxr(lft(x)) <= key(x),
                                                key(x) <= minr(rght(x)))))))))
AddRecDefinition(keys, x, If(x == nil, fgsetsort.lattice_bottom,
                             SetAdd(SetUnion(keys(lft(x)), keys(rght(x))), key(x))))
AddAxiom((), lft(nil) == nil)
AddAxiom((), rght(nil) == nil)

# Problem parameters
goal = Implies(bst(x), Implies(And(IsMember(k, keys(x)), k < key(x)), IsMember(k, keys(lft(x)))))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v = Var('v', fgsort)
lemma_grammar_args = [v, k, nil]
lemma_grammar_terms = {lft(v), rght(v), nil, rght(rght(nil)), rght(nil), v, rght(rght(v)), rght(lft(v)), lft(lft(v)), rght(rght(v)), lft(rght(v))}

name = 'bst-left'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
