# Module containing some utlities for converting between difference in syntax between z3 and cvc4.

import z3
from naturalproofs.utils import transform_expression


def cvc4_complicant_formula_sexpr(formula):
    # Replace z3's select with cvc4's member
    # Order of arguments is reverse
    member = z3.Function('member', z3.IntSort(), z3.SetSort(z3.IntSort()))
    cond = lambda expr: z3.is_select(expr)
    op = lambda expr: member(expr.arg(1), expr.arg(0))
    trans_expr = transform_expression(formula, [(cond, op)])
    formula_sexpr = trans_expr.sexpr()
    # Replace occurrences of string corresponding to the emptyset in z3 with the one in cvc4 
    z3_emptyset_str = '((as const (Array Int Bool)) false)'
    cvc4_emptyset_str = '(as emptyset (Set Int) )'
    formula_sexpr.replace(z3_emptyset_str, cvc4_emptyset_str)
    return formula_sexpr
