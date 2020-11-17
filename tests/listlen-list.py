import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from lemsynth.lemsynth_engine import solveProblem

# Declarations
x = Var('x', fgsort)
l = Var('l', intsort)
nil, ret = Consts('nil ret', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
lstlen = RecFunction('lstlen', fgsort, intsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lstlen, (x, l), If(x == nil, l == 0, lstlen(nxt(x), l - 1)))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
pgm = If(x == nil, ret == nil, ret == nxt(x))
goal = Implies(lstlen(x, l), Implies(pgm, lst(ret)))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v = Var('v', fgsort)
m = Var('m', intsort)
lemma_grammar_args = [v, m, nil]
lemma_grammar_terms = {v, m, nil}

name = 'dlist-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
