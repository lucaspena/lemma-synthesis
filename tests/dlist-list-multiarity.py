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
nil = Const('nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
prv = Function('prv', fgsort, fgsort)
lst = RecFunction('lst', fgsort, fgsort, boolsort)
dlst = RecFunction('dlst', fgsort, fgsort, boolsort)
AddRecDefinition(lst, (x, y), If(x == nil, True, lst(nxt(x), y)))
AddRecDefinition(dlst, (x, y), If(x == nil, True,
                                  If(nxt(x) == nil, True,
                                     And(prv(nxt(x)) == x, dlst(nxt(x), y)))))

# Problem parameters
goal = Implies(dlst(x, y), Implies(x == 0, lst(x, y)))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {prv(nxt(v1)), prv(nxt(nxt(v1))), prv(nxt(prv(v1))), v2, nxt(v2), prv(v2), nil, nxt(nil), prv(nil)}

name = 'dlist-list-multiarity'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
