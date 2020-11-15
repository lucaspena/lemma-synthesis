from z3 import *

from lemsynth.lemma_synthesis import getSygusOutput
from lemsynth.utils import translateLemma 
import lemsynth.options as options

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.decl_api import is_var_decl, get_recursive_definition
from naturalproofs.pfp import make_pfp_formula
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.extensions.finitemodel import FiniteModel


def solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string, config_params={}, annctx=default_annctx):
    # Extract relevant parameters for running the verification-synthesis engine from config_params
    valid_lemmas = set()
    invalid_lemmas = []
    use_cex_models = config_params.get('use_cex_models', True)
    cex_models = config_params.get('cex_models', [])

    # check if goal is provable on its own using induction
    pfp_of_goal = make_pfp_formula(goal)
    vcsolver = NPSolver()
    vcsolver.options.instantiation_mode = proveroptions.depth_one_untracked_lemma_instantiation
    vc_npsolution = vcsolver.solve(pfp_of_goal)

    if vc_npsolution.if_sat:
        print('vc cannot be proved using induction.')
    else:
        print('vc is provable using induction.')
        exit(0)

    # continuously get valid lemmas until VC has been proven
    while True:
        lemma = getSygusOutput(valid_lemmas, lemma_grammar_args, goal, name, grammar_string, config_params, annctx)
        if lemma is None:
            exit('Instance failed.')

        # convert CVC4 versions of membership, insertion to z3py versions
        SetIntSort = SetSort(IntSort())
        membership = Function('membership', IntSort(), SetIntSort, BoolSort())
        insertion = Function('insertion', IntSort(), SetIntSort, SetIntSort)
        addl_decls = {'member': membership, 'insert': insertion}
        swap_fcts = {insertion: SetAdd}
        replace_fcts = {membership: IsMember}

        # testing translation of lemma
        rhs_lemma = translateLemma(lemma[0], lemma_grammar_args, addl_decls, swap_fcts, replace_fcts, annctx)
        index = int(lemma[1][-2])
        recs = get_recursive_definition(None, True)
        lhs = sorted(recs, key=lambda x: x[0].name())[index][0]
        lhs_arity = lhs.arity()
        lhs_lemma_args = tuple(lemma_grammar_args[:lhs_arity])
        lhs_lemma = lhs(lhs_lemma_args)
        z3py_lemma = Implies(lhs_lemma, rhs_lemma)

        print('proposed lemma: ' + str(z3py_lemma))
        if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
            print('lemma has already been proposed')
            if use_cex_models:
                if z3py_lemma in invalid_lemmas:
                    print('Something is wrong. Lemmas should not be re-proposed in the presence of countermodels. '
                          'Exiting.') 
                if z3py_lemma in valid_lemmas:
                    print('This is a currently known limitation of the tool. Consider restricting your grammar to '
                          'have terms of lesser height.') 
                exit('Instance failed.')
            else:
                # Using bag-of-lemmas + prefetching formulation, or the re-proposed lemma is a valid one.
                # Continue and hope for the best.
                print('Countermodels not enabled. Retrying lemma synthesis.')
                continue
        pfp_lemma = make_pfp_formula(z3py_lemma)
        lemmaprover = NPSolver()
        # Default configuration: bounded depth, depth bound = 1
        lemma_npsolution = lemmaprover.solve(pfp_lemma)
        if lemma_npsolution.if_sat:
            print('proposed lemma cannot be proved.')
            if options.debug:
                # Check that the ground terms do not exceed lemma_terms, or finite model extraction will not work
                lemma_terms = lemma_npsolution.fg_terms
                if not lemma_terms.issubset(lemma_grammar_terms):
                    raise ValueError(
                        'lemma_terms is too small.\nLemma: {}\nTerms: {}'.format(str(z3py_lemma), lemma_terms))
            invalid_lemmas = invalid_lemmas + [z3py_lemma]
            if use_cex_models:
                cex_model = FiniteModel(lemma_npsolution.model, lemma_grammar_terms, annctx=annctx)
                cex_models = cex_models + [cex_model]
        else:
            valid_lemmas.add((tuple([arg for arg in lemma_grammar_args if is_var_decl(arg)]), z3py_lemma))
            # Reset countermodels and invalid lemmas to [] because we have additional information to retry those proofs.
            cex_models = []
            invalid_lemmas = []
        # Update countermodels before next round of synthesis
        config_params['cex_models'] = cex_models
