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
nil, c = Consts('nil c', fgsort)
nxt = Function('nxt', fgsort, fgsort)
prv = Function('prv', fgsort, fgsort)
lsegprev = RecFunction('lsegprev', fgsort, fgsort, boolsort)
dlseg = RecFunction('dlseg', fgsort, fgsort, boolsort)
AddRecDefinition(lsegprev, (x, y) , If(x == y, True, lsegprev(x, nxt(y))))
AddRecDefinition(dlseg, (x, y) , If(x == y, True,
                                    And(prv(nxt(x)) == x, dlseg(nxt(x), y))))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
goal = Implies(dlseg(x, y), Implies(x != c, lsegprev(y, x)))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v1, v2, prv(nxt(v1)), prv(nxt(nxt(v1))), nil, prv(nxt(v2)), nxt(nil), nxt(v1), prv(nxt(prv(nxt(v1)))), nxt(prv(nxt(v1))), nxt(v2), nxt(nxt(v1))}

name = 'dlseg-lsegprev'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
