import z3

from naturalproofs.uct import *
from naturalproofs.decl_api import *
from naturalproofs.pfp import *

x, y, nil = Consts('x y nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
AddRecDefinition(lst, x, z3.If(x == nil, True, lst(nxt(x))))
inductive_claim = z3.Implies(lst(y), y == nxt(y))
pfpformula = make_pfp_formula(inductive_claim)
print(pfpformula)
