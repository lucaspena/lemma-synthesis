# Only importing this for writing this file as a test
import unittest

import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from naturalproofs.lemma_synthesis import solveProblem

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
goal = Implies(dlst(x), Implies(x == 0, lst(x)))
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

axioms_python = []
unfold_recdefs_python = []

# must change name of bound variables in lemma arguments
v = Const('v', fgsort)
lemma_args = [v, nil]

name = 'dlist-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

config_params = {}
config_params['use_cex_models'] = False

solveProblem(axioms_python, unfold_recdefs_python, lemma_args, goal, name, grammar_string, config_params)

class DlistListTest(unittest.TestCase):
    def test1(self):
        self.assertTrue(npsolution.if_sat)


if __name__ == '__main__':
    unittest.main()
