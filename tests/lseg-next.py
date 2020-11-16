import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y, z = Vars('x y z', fgsort)
c = Consts('c', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
AddRecDefinition(lseg, (x, y), If(x == y, True, lseg(nxt(x), y)))

# Problem parameters
goal = Implies(lseg(x, y), Implies(x != c, Implies(nxt(y) == z, lseg(x, z))))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2, v3 = Vars('v1 v2 v3', fgsort)
lemma_grammar_args = [v1, v2, v3]
lemma_grammar_terms = {nxt(v1), nxt(nxt(v1)), nxt(v2), nxt(nxt(v2)), nxt(v3), nxt(nxt(v3))}

name = 'lseg-next'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
