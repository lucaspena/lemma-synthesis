from z3 import *

import lemsynth.grammar_utils as grammar
from lemsynth.lemma_synthesis import getSygusOutput
from lemsynth.utils import translateLemma 
import lemsynth.options as options

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.decl_api import is_var_decl, get_boolean_recursive_definitions
from naturalproofs.pfp import make_pfp_formula
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.prover_utils import get_foreground_terms
from naturalproofs.utils import get_all_subterms
from naturalproofs.extensions.finitemodel import FiniteModel


def solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string, config_params=None, annctx=default_annctx):
    if options.aggressive_debug:
        # Only try simple solver strategy for lemmas
        answerlist = config_params.get('answer', None)
        if answerlist is not None:
            # Check if answer is provable on its own and proves the goal.
            answer_solver = NPSolver()
            answer_solver.options.instantiation_mode = proveroptions.bounded_depth
            answer_solver.options.depth = 1
            for i in range(len(answerlist)):
                answer_i_solution = answer_solver.solve(make_pfp_formula(answerlist[i][1], annctx), set(answerlist[:i]))
                if answer_i_solution.if_sat:
                    raise ValueError('The answer you have given is wrong. Check lemma number {}'.format(str(i+1)))
            goal_answer_solver = NPSolver()
            goal_answer_solver.options.instantiation_mode = proveroptions.depth_one_untracked_lemma_instantiation
            goal_answer_solution = goal_answer_solver.solve(goal, set(answerlist))
            if goal_answer_solution.if_sat:
                raise ValueError('Cannot prove goal with given lemmas.')

    # Extract relevant parameters for running the verification-synthesis engine from config_params
    if config_params is None:
        config_params = {}
    lemma_grammar_terms = get_all_subterms(lemma_grammar_terms)
    valid_lemmas = set()
    invalid_lemmas = []
    use_cex_models = config_params.get('use_cex_models', True)
    cex_models = config_params.get('cex_models', [])

    # check if goal is fo provable
    goal_fo_solver = NPSolver()
    goal_fo_solver.options.instantiation_mode = proveroptions.depth_one_untracked_lemma_instantiation
    goal_fo_npsolution = goal_fo_solver.solve(goal)
    if goal_fo_npsolution.if_sat:
        print('goal is not first-order provable.')
    else:
        print('goal is first-order provable.')
        exit(0)

    # check if goal is fo provable using its own pfp
    pfp_of_goal = make_pfp_formula(goal)
    goal_pfp_solver = NPSolver()
    goal_pfp_npsolution = goal_pfp_solver.solve(pfp_of_goal)
    if goal_pfp_npsolution.if_sat:
        print('goal cannot be proved using induction.')
    else:
        print('goal is provable using induction.')
        exit(0)

    # Extract relevant instantiation/extraction terms given the grammar
    lemma_instantiation_terms = grammar.lemma_instantiation_terms(lemma_grammar_args, lemma_grammar_terms, annctx)
    # Extraction terms for goal must be computed from all instantiations of recursive definitions/axioms with goal terms
    # Specific to depth_one_untracked_lemma_instantitation_mode because it can be reused
    goal_npsolution_instantiation_terms = goal_fo_npsolution.extraction_terms
    config_params['goal_npsolution_instantiation_terms'] = goal_npsolution_instantiation_terms
    goal_extraction_terms = grammar.goal_extraction_terms(goal_npsolution_instantiation_terms, lemma_grammar_args, lemma_grammar_terms, annctx)
    config_params['goal_extraction_terms'] = goal_extraction_terms

    # continuously get valid lemmas until goal has been proven
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
        recs = get_boolean_recursive_definitions()
        lhs = recs[index]
        lhs_arity = lhs.arity()
        lhs_lemma_args = tuple(lemma_grammar_args[:lhs_arity])
        lhs_lemma = lhs(lhs_lemma_args)
        z3py_lemma_body = Implies(lhs_lemma, rhs_lemma)
        z3py_lemma_params = tuple([arg for arg in lemma_grammar_args if is_var_decl(arg)])
        z3py_lemma = (z3py_lemma_params, z3py_lemma_body)

        print('proposed lemma: {}'.format(str(z3py_lemma_body)))
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
        pfp_lemma = make_pfp_formula(z3py_lemma_body)
        lemmaprover = NPSolver()
        lemmaprover.options.instantiation_mode = proveroptions.manual_instantiation
        lemmaprover.options.terms_to_instantiate = lemma_instantiation_terms
        lemma_npsolution = lemmaprover.solve(pfp_lemma, valid_lemmas)
        if lemma_npsolution.if_sat:
            print('proposed lemma cannot be proved.')
            if options.debug:
                # Check that the terms needed from the pfp of the proposed lemma do not exceed lemma_grammar_terms.
                # Otherwise finite model extraction will not work.
                needed_instantiation_terms = get_foreground_terms(pfp_lemma, annctx)
                remaining_terms = needed_instantiation_terms - lemma_instantiation_terms
                if remaining_terms != set():
                    raise ValueError('lemma_terms is too small.\n'
                                     'Lemma: {}\n'
                                     'Terms needed after pfp computation: {}'
                                     ''.format(str(z3py_lemma_body), remaining_terms))
            invalid_lemmas = invalid_lemmas + [z3py_lemma]
            if use_cex_models:
                extraction_terms = lemma_npsolution.extraction_terms
                cex_model = FiniteModel(lemma_npsolution.model, extraction_terms, annctx=annctx)
                cex_models = cex_models + [cex_model]
        else:
            valid_lemmas.add(z3py_lemma)
            # Reset countermodels and invalid lemmas to [] because we have additional information to retry those proofs.
            cex_models = []
            invalid_lemmas = []
        # Update countermodels before next round of synthesis
        config_params['cex_models'] = cex_models
