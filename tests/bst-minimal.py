import importlib_resources

import z3
import itertools

from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom


from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y = Vars('x y', fgsort)
z, nil = Consts('z nil', fgsort)
k = Const('k', intsort)
key = Function('key', fgsort, intsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
minr = Function('minr', fgsort, intsort)
maxr = Function('maxr', fgsort, intsort)
bst = RecFunction('bst', fgsort, boolsort)
hbst = RecFunction('hbst', fgsort, fgsetsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
AddRecDefinition(bst, x, If(x == nil, True,
                            And(0 < key(x),
                                And(key(x) < 100,
                                    And(bst(lft(x)),
                                        And(bst(rght(x)),
                                            And(maxr(lft(x)) <= key(x),
                                                key(x) <= minr(rght(x)))))))))
AddRecDefinition(hbst, x, If(x == nil, fgsetsort.lattice_bottom,
                             SetAdd(SetUnion(hbst(lft(x)), hbst(rght(x))), x)))
AddAxiom((), lft(nil) == nil)
AddAxiom((), rght(nil) == nil)

# AddAxiom((x,), Implies(bst(x), minr(lft(x)) <= minr(x)))
# Problem parameters
# goal = Implies(bst(x), Implies(And(x != nil,
#                                    And(IsMember(y, hbst(x)),
#                                        And(k == minr(x),
#                                            And(k == minr(y), y != nil)))),
#                                k == minr(lft(y))))


#AddAxiom(x, Implies(bst(lft(x)), Implies(IsMember(y, hbst(lft(x))), And(key(y) <= maxr(lft(x)), minr(lft(x)) <= key(y)))))
#AddAxiom(x, Implies(bst(rght(x)), Implies(IsMember(z, hbst(rght(x))), And(key(z) <= maxr(rght(x)), minr(rght(x)) <= key(z)))))
goal = Implies(bst(x), Implies(And(x != nil, And(IsMember(y, hbst(lft(x))), IsMember(z, hbst(rght(x))))), key(y) <= key(z)))


# goal = Implies(bst(x), Implies(IsMember(y, hbst(x)), And(key(y) <= maxr(x), minr(x) <= key(y))))
#goal = Implies(bst(x), minr(lft(x)) <= minr(x))
# goal = Implies(And(bst(x), x != nil), minr(x) <= maxr(x))
# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2]
lemma_grammar_terms = {v1, v2}

name = 'bst-minimal'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))


def read_lembools(lembools):
    loc1, loc2, loc3, loc4, loc5, loc6 = tuple([v1 if lembool else v2 for lembool in lembools])
    return Implies(bst(v1), Implies(IsMember(loc1, hbst(loc2)), And(key(loc3) <= maxr(loc4), minr(loc5) <= key(loc6))))


config_params = dict()
config_params['solution'] = read_lembools

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string, config_params=config_params)



# (define-fun lemma ((x Int) (y Int)) Bool
# (=> (member (Loc1 x y) (hbst (Loc2 x y))) 
#      (and (<= (key (Loc3 x y)) (maxr (Loc4 x y)))
#           (<= (minr (Loc5 x y)) (key (Loc6 x y)))
#      )
# ))


# var = Vars('x1 x2 x3 x4 x5 x6 x7', fgsort)
# var_axiom = Implies(bst(var[0]), Implies(IsMember(var[1], hbst(var[2])), And(key(var[3]) <= maxr(var[4]), minr(var[5]) <= key(var[6]))))
# args = list(itertools.product([x, y], repeat=7))
# for i in range(len(args)):
#     arg = args[i]
#     actual_axiom = z3.substitute(var_axiom, list(zip(var, list(arg))))
#     bound_axiom = {((x, y), actual_axiom)}
#     npsolver = NPSolver()
#     goal = Implies(bst(x), Implies(And(x != nil, And(IsMember(y, hbst(lft(x))), IsMember(z, hbst(rght(x))))), key(y) <= key(z)))
#     npsolution = npsolver.solve(goal, bound_axiom)
# 
#     if not npsolution.if_sat:
#         print('s', end='')
#     else:
#         print('n', end='')
