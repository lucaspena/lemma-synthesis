from z3 import *
# model.compact should be turned off to get uncompressed models
z3.set_param('model.compact', False)

import naturalproofs.uct as uct
import naturalproofs.pfp as pfp
import naturalproofs.utils as nputils #transform_expression, apply_bound_formula
import naturalproofs.extensions.finitemodel as finitemodel #model_key_repr


def generate_pfp_constraint(rec_funcdeclref, lemma_args, finite_model, smt_simplify=False):
    lemma_arity = len(lemma_args)
    # Assuming that all arguments of the lemma are of the foreground sort
    lemma_rhs_macro = Function('lemma', *([IntSort()]*lemma_arity), BoolSort())
    # Assuming that the arguments for the recursive deifnition on the lhs are the first 'k' variables in lemma_args
    lhs_args = lemma_args[:rec_funcdeclref.arity()]
    lemma = Implies(rec_funcdeclref(*lhs_args), lemma_rhs_macro)
    lemma_pfp = pfp.make_pfp_formula(lemma)
    # 'Evaluate' the pfp formula on the given finite model
    lemma_pfp_eval = _finitemodel_eval(lemma_pfp, finite_model)
    if smt_simplify:
        lemma_pfp_eval = simplify(lemma_pfp_eval)
        


def _finitemodel_eval(formula, finite_model):
    # Construct transformation condition/operation pairs for each sort
    # fgsort and intsort
    cond_fgsort_intsort = lambda expr: expr.decl().arity() == 0 and uct.get_uct_sort(expr) in {uct.fgsort, uct.intsort}
    op_fgsort_intsort = lambda expr: IntVal(finite_model[finitemodel.model_key_repr(expr.decl())][()])
    # fgsetsort and intsetsort
    return None