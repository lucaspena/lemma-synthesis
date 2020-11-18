import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y = Vars('x y', fgsort)
c, nil = Consts('c nil', fgsort)
key = Function('key', fgsort, intsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
keys = RecFunction('keys', fgsort, intsetsort)
lsegkeys = RecFunction('lsegkeys', fgsort, fgsort, intsetsort)

AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lseg, (x, y) , If(x == y, True, lseg(nxt(x), y)))

AddRecDefinition(keys, x, If(x == nil, intsetsort.lattice_bottom, SetAdd(keys(nxt(x)), key(x))))
AddRecDefinition(lsegkeys, (x, y), If(x == y, intsetsort.lattice_bottom,
                                      SetAdd(lsegkeys(nxt(x), y), key(x))))

AddAxiom((), nxt(nil) == nil)

# Problem parameters
pre = And(lst(y), x != c)
goal = Implies(lseg(x, y), Implies(pre, keys(x) == SetUnion(lsegkeys(x, y), keys(y))))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v1, nil, nxt(nil), v2, nxt(v2), nxt(v1), nxt(nxt(v1)), nxt(nxt(nxt(v1)))}

name = 'lseg-list-keys'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
