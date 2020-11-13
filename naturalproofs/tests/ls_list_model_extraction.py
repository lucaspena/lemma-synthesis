"""
Basic example showing how extract a finite model on a finite sub-universe of the foreground sort given a satisfying 
smt model.    
"""

# Only importing this for writing this file as a test
import unittest

from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.extensions.finitemodel import extract_finite_model

# Declarations
x, y, nil = Consts('x y nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
ls = RecFunction('ls', fgsort, fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(ls, (x, y), If(x == nil, True, ls(nxt(x), y)))
# Problem parameters
goal = Implies(ls(x, nil), lst(x))
lemma1_params = (x, y)
lemma1_body = Implies(And(ls(x, y), lst(y)), lst(x))
lemmas = {(lemma1_params, lemma1_body)}
# Call a natural proofs solver
npsolver = NPSolver()
# Configure the solver
npsolver.options.instantiation_mode = proveroptions.manual_instantiation
npsolver.options.terms_to_instantiate = {x, y, nil}


def without_lemma():
    npsolution = npsolver.solve(goal)
    smtmodel = npsolution.model
    terms = npsolution.fg_terms
    finite_model = extract_finite_model(smtmodel, terms)
    return finite_model
# Uncomment the statement below to see the extracted model
# print(without_lemma())


class LsListModelExtractionTest(unittest.TestCase):
    def test_without_lemma(self):
        try:
            # without_lemma does not raise any exceptions
            finite_model = without_lemma()
        except Exception:
            self.fail('Finite model extraction failed.')

    def test_with_lemma(self):
        npsolution = npsolver.solve(goal, lemmas)
        self.assertFalse(npsolution.if_sat)


if __name__ == '__main__':
    unittest.main()

