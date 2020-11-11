from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.naturalproofs import NPSolver
import naturalproofs.proveroptions as proveroptions

# Declarations
x, y, nil = Consts('x y nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
ls = RecFunction('ls', fgsort, fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(ls, (x, y), If(x == nil, True, ls(nxt(x), y)))
# Problem parameters
goal = Implies(ls(x, nil), lst(x))
lemma1_params = (x)
lemma1_body = Implies(And(ls(x, y), lst(y)), lst(x))
lemmas = {(lemma1_params, lemma1_body)}
# Call a natural proofs solver
npsolver = NPSolver()
# Configure the solver
npsolver.options.instantiation_mode = proveroptions.manual_instantiation
npsolver.options.terms_to_instantiate = [x, y, nil]
# Ask for proof
npsolution = npsolver.solve(goal, lemmas)
print(npsolution.if_sat)
