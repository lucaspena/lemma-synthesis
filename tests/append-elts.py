import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If, Exists
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

x, y, z, z1 = Vars('x y z z1', fgsort)

# ADT definition of lists
nil = Const('nil', fgsort)
cons = Function('cons', fgsort, fgsort)
tail = Function('tail', fgsort, fgsort)

append = RecFunction('append', fgsort, fgsort, fgsort, boolsort)
length = RecFunction('length', fgsort, intsort)

AddRecDefinition(append, (x, y, z), If(x == nil, z == y,
                                       Exists(z1, z == cons(append(tail(x), y, z1)))))
AddRecDefinition(length, x, If(x == nil, 0, length(tail(x)) + 1))

AddAxiom((), tail(nil) == nil)
# need axiom relating tail and cons

# len(append(x, y)) = len(x) + len(y)
goal = Implies(append(x, y, z), length(z) == length(x) + length(y))

name = 'append-elts'

# leave all things related to grammar as empty, just using natural proof engine
lemma_grammar_args = []
lemma_grammar_terms = {}

grammar_string = ''

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
