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
lstlen_bool = RecFunction('lstlen_bool', fgsort, boolsort)
lstlen_int = RecFunction('lstlen_int', fgsort, intsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lstlen_bool, x, If(x == nil, True, lstlen_bool(nxt(x))))
AddRecDefinition(lstlen_int, x, If(x == nil, 0, lstlen_int(nxt(x)) + 1))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
pgm = If(lstlen_int(x) == 1, ret == x, ret == nxt(x))
goal = Implies(lstlen_bool(x), Implies(pgm, lst(ret)))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v = Var('v', fgsort)
lemma_grammar_args = [v, nil]
lemma_grammar_terms = {v, nil}

name = 'listlen-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
