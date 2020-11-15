from z3 import *
# model.compact should be turned off to get uncompressed models
z3.set_param('model.compact', False)

import naturalproofs.uct as uct
import naturalproofs.pfp as pfp
import naturalproofs.utils as nputils
import naturalproofs.extensions.finitemodel as finitemodel


def generate_pfp_constraint(rec_funcdeclref, lemma_args, finite_model, smt_simplify=False):
    lemma_arity = len(lemma_args)
    # Assuming that all arguments of the lemma are of the foreground sort
    lemma_rhs_macro = Function('lemma', *([IntSort()]*lemma_arity), BoolSort())
    # Assuming that the arguments for the recursive deifnition on the lhs are the first 'k' variables in lemma_args
    lhs_args = lemma_args[:rec_funcdeclref.arity()]
    lemma = Implies(rec_funcdeclref(*lhs_args), lemma_rhs_macro(*lemma_args))
    lemma_pfp = pfp.make_pfp_formula(lemma)
    # 'Evaluate' the pfp formula on the given finite model
    lemma_pfp_eval = _eval_vars(lemma_pfp, finite_model)
    if smt_simplify:
        lemma_pfp_eval = simplify(lemma_pfp_eval)
    return lemma_pfp_eval


def _eval_vars(formula, finite_model):
    # Construct transformation condition/operation pairs for variables of different sorts
    # Handling all sorts uniformly for now
    cond = lambda expr: expr.decl().arity() == 0 and uct.get_uct_sort(expr) is not None
    op = lambda expr: finitemodel.recover_value(finite_model[finitemodel.model_key_repr(expr.decl())][()], uct.get_uct_sort(expr))
    return nputils.transform_expression(formula, [(cond, op)])
