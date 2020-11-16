import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y = Vars('x y', fgsort)
c = Const('c', fgsort)
nxt = Function('nxt', fgsort, fgsort)
prv = Function('prv', fgsort, fgsort)
dlseg = RecFunction('dlseg', fgsort, fgsort, boolsort)
AddRecDefinition(dlseg, (x, y), If(x == y, True,
                                   And(prv(nxt(x)) == x, dlseg(nxt(x), y))))

# Problem parameters
goal = Implies(dlseg(x, y), Implies(And(x != y, x != c), dlseg(x, prv(y))))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2]
lemma_grammar_terms = {nxt(nxt(v1)), nxt(prv(nxt(v1))), prv(prv(nxt(v1))), prv(v1), prv(v2), nxt(prv(v2)), prv(prv(v2)), nxt(v2)}

name = 'dlseg-prev'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
