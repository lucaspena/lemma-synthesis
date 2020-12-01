import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

x = Var('x', fgsort)
nil = Const('nil', fgsort)
k = Const('k', intsort)
nxt = Function('nxt', fgsort, fgsort)
key = Function('key', fgsort, intsort)
slst = RecFunction('slst', fgsort, boolsort)
keys = RecFunction('keys', fgsort, intsetsort)
AddRecDefinition(slst, x, If(x == nil, True,
                             If(nxt(x) == nil, True,
                                And(key(x) <= key(nxt(x)), slst(nxt(x))))))
AddRecDefinition(keys, x, If(x == nil, intsetsort.lattice_bottom, SetAdd(keys(nxt(x)), key(x))))
AddAxiom((), nxt(nil) == nil)

goal = Implies(slst(x), Implies(k < key(x), Not(IsMember(k, keys(x)))))

name = 'lem-member'

# leave all things related to grammar as empty, just using natural proof engine
lemma_grammar_args = []
lemma_grammar_terms = {}

grammar_string = ''

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
