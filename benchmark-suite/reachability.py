import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.prover import NPSolver
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

# declarations
x = Var('x', fgsort)
c, s, nil = Consts('c s nil', fgsort)
v1 = Function('v1', fgsort, fgsort)
v2 = Function('v2', fgsort, fgsort)
p = Function('p', fgsort, fgsort)
n = Function('n', fgsort, fgsort)

reach = RecFunction('reach', fgsort, boolsort)

# precondition
AddAxiom((), v1(s) == v2(s))

cond = v1(p(x)) != nil
assign1 = v1(x) == n(v1(p(x)))
assign2 = If( v2(p(x)) != c,
              v2(x) == n(v2(p(x))),
              v2(x) == v2(p(x)) )
assign = And(assign1, assign2)
AddRecDefinition(reach, x, If(x == s, True, And(reach(p(x)), And(cond, assign))))

# vc
lhs = v1(x) == nil
rhs = Or(v2(x) == nil, v2(x) == c)
goal = Implies(reach(x), Implies(lhs, rhs))

# check validity with natural proof solver and no hardcoded lemmas
np_solver = NPSolver()
solution = np_solver.solve(make_pfp_formula(goal))
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')

# hardcoded lemma
lemma_params = (x,)
lemma_body = Implies(reach(x), Or(v1(x) == v2(x), v2(x) == c))
lemmas = {(lemma_params, lemma_body)}

# check validity of lemmas
solution = np_solver.solve(make_pfp_formula(lemma_body))
if not solution.if_sat:
    print('lemma is valid')
else:
    print('lemma is invalid')

# check validity with natural proof solver and hardcoded lemmas
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal (with lemmas) is valid')
else:
    print('goal (with lemmas) is invalid')
