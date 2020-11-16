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
key = Function('key', fgsort, intsort)
dlseg = RecFunction('dlseg', fgsort, fgsort, boolsort)
slseg = RecFunction('slseg', fgsort, fgsort, boolsort)
sdlseg = RecFunction('sdlseg', fgsort, fgsort, boolsort)
AddRecDefinition(dlseg, (x, y) , If(x == y, True,
                                    And(prv(nxt(x)) == x, dlseg(nxt(x), y))))
AddRecDefinition(slseg, (x, y) , If(x == y, True,
                                    And(key(x) < key(nxt(x)), slseg(nxt(x), y))))
AddRecDefinition(sdlseg, (x, y) , If(x == y, True,
                                    And(prv(nxt(x)) == x,
                                        And(key(x) < key(nxt(x)), sdlseg(nxt(x), y)))))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
goal = Implies(sdlseg(x, y), Implies(x != c, And(dlseg(x, y), slseg(x, y))))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v2, prv(nxt(v1)), prv(nxt(nxt(v1))), nil, prv(nxt(v2)), prv(nxt(nil)), nxt(nil), nxt(v1), prv(nxt(prv(nxt(v1)))), nxt(prv(nxt(v1))), nxt(v2), v1, nxt(nxt(v1))}

name = 'sdlseg-dlseg-and-slseg'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
