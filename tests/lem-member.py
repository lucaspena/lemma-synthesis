import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If, Exists
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

l, tl = Vars('l tl', fgsort)
k, h = Consts('k h', intsort)
x = Var('x', intsort)

# ADT definition of lists
nil = Const('nil', fgsort)
cons = Function('cons', intsort, fgsort, fgsort)

# projections for cons
head = Function('head', fgsort, intsort)
tail = Function('tail', fgsort, fgsort)

# rec defs
slst = RecFunction('slst', fgsort, boolsort)
elems = RecFunction('elems', fgsort, fgsetsort)
member = RecFunction('member', fgsort, boolsort)
AddRecDefinition(slst, l, If(l == nil, True,
                             If(tail(l) == nil, True,
                                And(head(l) <= head(tail(l)), slst(tail(l))))))
AddRecDefinition(elems, l, If(l == nil, fgsetsort.lattice_bottom,
                              SetAdd(elems(tail(l)), head(l))))
AddRecDefinition(member, l, If(l == nil, False,
                               If(k == head(l), True,
                                  If(k < head(l), False,
                                     member(tail(l))))))

# axioms
AddAxiom(l, head(cons(h, l)) == h)
AddAxiom(l, tail(cons(h, l)) == l)
AddAxiom(l, cons(h, l) != nil)

goal = Implies(And(slst(l), IsMember(k, elems(l))), member(l))

# adt pfp of goal
base_case = Implies(And(slst(nil), IsMember(k, elems(nil))), member(nil))
induction_hypothesis = Implies(And(slst(tl), IsMember(k, elems(tl))), member(tl))
induction_step = Implies(And(slst(cons(h, tl)), IsMember(k, elems(cons(h, tl)))),
                         member(cons(h, tl)))

pfp_goal = And(base_case, Implies(induction_hypothesis, induction_step))

np_solver = NPSolver()
solution = np_solver.solve(pfp_goal)
print('No lemma: ' + str(solution.if_sat))

# adt pfp of lemma
base_case = Implies(And(slst(nil), k < head(nil)), Not(IsMember(k, elems(nil))))
induction_hypothesis = Implies(And(slst(tl), k < head(tl)), Not(IsMember(k, elems(tl))))
induction_step = Implies(And(slst(cons(h, tl)), k < head(cons(h, tl))), Not(IsMember(k, elems(cons(h, tl)))))

pfp_goal = And(base_case, Implies(induction_hypothesis, induction_step))
new_np_solver = NPSolver()
solution = new_np_solver.solve(pfp_goal)
print('Lemma: ' + str(solution.if_sat))

