import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.naturalproofs import NPSolver
import naturalproofs.proveroptions as proveroptions

# Declarations
x, nil = Consts('x nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
prv = Function('prv', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
dlst = RecFunction('dlst', fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(dlst, x, If(x == nil, True,
                             If(nxt(x) == nil, True,
                                And(prv(nxt(x)) == x, dlst(nxt(x))))))

# Problem parameters
goal = Implies(dlst(x), lst(x))
lemma1_params = (x,)
lemma1_body = z3.BoolVal(True)
lemmas = {(lemma1_params, lemma1_body)}
# Call a natural proofs solver
npsolver = NPSolver()
# Configure the solver
npsolver.options.instantiation_mode = proveroptions.manual_instantiation
npsolver.options.terms_to_instantiate = [x, nil]
# Ask for proof
npsolution = npsolver.solve(goal, lemmas)
if npsolution.if_sat:
    print('sat')
else:
    print('unsat')
