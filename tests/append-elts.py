import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If, Exists
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

x, y, tx = Vars('x y tx', fgsort)
hx = Var('hx', intsort)

# ADT definition of lists
nil = Const('nil', fgsort)
cons = Function('cons', intsort, fgsort, fgsort)

# projections for cons
head = Function('head', fgsort, intsort)
tail = Function('tail', fgsort, fgsort)

# rec defs
append = RecFunction('append', fgsort, fgsort, fgsort)
length = RecFunction('length', fgsort, intsort)
AddRecDefinition(append, (x, y), If(x == nil, y, cons(head(x), append(tail(x), y))))
AddRecDefinition(length, x, If(x == nil, 0, length(tail(x)) + 1))

# axioms
AddAxiom(x, head(cons(hx, x)) == hx)
AddAxiom(x, tail(cons(hx, x)) == x)
AddAxiom(x, cons(hx, x) != nil)

# len(append(x, y)) = len(x) + len(y)
goal = length(append(x, y)) == length(x) + length(y)

# adt pfp of goal
base_case = length(append(nil, y)) == length(nil) + length(y)
induction_hypothesis = length(append(tx, y)) == length(tx) + length(y)
induction_step = length(append(cons(hx, tx), y)) == length(cons(hx, tx)) + length(y)

pfp_goal = Implies(induction_hypothesis, induction_step)

np_solver = NPSolver()
solution = np_solver.solve(pfp_goal)
print(solution.if_sat)

