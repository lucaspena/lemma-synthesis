import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from lemsynth.lemsynth_engine import solveProblem

# Declarations
x = Var('x', fgsort)
c, s, nil = Consts('c s nil', fgsort)
v1 = Function('v1', fgsort, fgsort)
v2 = Function('v2', fgsort, fgsort)
p = Function('p', fgsort, fgsort)
n = Function('n', fgsort, fgsort)

reach = RecFunction('reach', fgsort, boolsort)

# precondition
AddAxiom((), v1(s) == v2(s))

cond = v1(p(x)) != nil
assign1 = v1(x) == n(v1(p(x)))
assign2 = v2(x) == n(v2(p(x)))
assign = And(assign1, assign2)
AddRecDefinition(reach, x, If(x == s, True, And(reach(p(x)), And(cond, assign))))

lhs = v1(x) == nil
rhs = v2(x) == nil
goal = Implies(reach(x), Implies(lhs, rhs))

z = Var('z', fgsort)
lemma_grammar_args = [z, nil, s, c]
lemma_grammar_terms = {z, nil, s, c, v1(z), v1(p(z)), p(z), v2(z), v2(p(z)), n(v2(p(z))), n(v1(p(z))), n(c), n(nil), n(n(nil)), v1(z), n(v2(z)), n(n(c)), n(v1(z)), n(n(n(nil))), n(n(n(c)))}

name = 'reachability'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
