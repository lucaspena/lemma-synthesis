import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If, Exists
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

x, y, nx, ny = Vars('x y nx ny', fgsort)

# ADT definition of nats
zero = Const('zero', fgsort)
succ = Function('succ', fgsort, fgsort)

# projection function - analogous to tail of list
pred = Function('pred', fgsort, fgsort)

# rec defs
plus = RecFunction('plus', fgsort, fgsort, fgsort)
AddRecDefinition(plus, (x, y), If(x == zero, y, succ(plus(pred(x), y))))

# axioms
AddAxiom(x, pred(succ(x)) == x)
AddAxiom(x, succ(x) != zero)

goal = plus(x, y) == plus(y, x)

# adt pfp of goal
base_case = plus(zero, y) == plus(y, zero)
induction_hypothesis = plus(nx, y) == plus(y, nx)
induction_step = plus(succ(nx), y) == plus(y, succ(nx))

pfp_goal = Implies(induction_hypothesis, induction_step)
orig_np_solver = NPSolver()
orig_solution = orig_np_solver.solve(pfp_goal)
print('Commutativity of addition: no lemma')
if not orig_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')

# adt pfp of inductive case lemma: zero + x = x
base_case = plus(zero, zero) == plus(zero, zero)
induction_hypothesis = plus(zero, ny) == plus(ny, zero)
induction_step = plus(zero, succ(ny)) == plus(succ(ny), zero)

pfp_goal = Implies(induction_hypothesis, induction_step)
base_np_solver = NPSolver()
base_solution = base_np_solver.solve(pfp_goal)
print('Lemma for base case: zero + x = x')
if not base_solution.if_sat:
    print(' -- lemma is valid')
else:
    print(' -- lemma is invalid')

# adt pfp of inductive case lemma: x + S y = S (x + y)
base_case = plus(zero, succ(y)) == succ(plus(zero, y))
induction_hypothesis = plus(nx, succ(y)) == succ(plus(nx, y))
induction_step = plus(succ(nx), succ(y)) == succ(plus(succ(nx), y))

pfp_goal = Implies(induction_hypothesis, induction_step)
ind_np_solver = NPSolver()
ind_solution = ind_np_solver.solve(pfp_goal)
print('Lemma for inductive case: x + S y = S (x + y)')
if not ind_solution.if_sat:
    print(' -- lemma is valid')
else:
    print(' -- lemma is invalid')

# adding lemmas to solver
base_lemma_params = (y,)
base_lemma_body = plus(zero, y) == plus(y, zero)

ind_lemma_params = (x, y)
ind_lemma_body = plus(x, succ(y)) == succ(plus(x, y))

lemmas = {(base_lemma_params, base_lemma_body), (ind_lemma_params, ind_lemma_body)}
final_np_solver = NPSolver()
final_solution = final_np_solver.solve(goal, lemmas)
print('Original goal with lemmas assumed:')
if not ind_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')
