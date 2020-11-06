from z3 import *

from lemsynth.lemma_synthesis import *
from lemsynth.false_models import *
from lemsynth.lemsynth_utils import *

def solveProblem(fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, vc, name, grammar_string, config_params, synth_dict):
    # Extract relevant parameters for running the verification-synthesis engine from synth_dict
    valid_lemmas = synth_dict.get('valid_lemmas',[])
    invalid_lemmas = synth_dict.get('invalid_lemmas',[])
    use_cex_models = config_params.get('use_cex_models', False)
    cex_models = config_params.get('cex_models',[])

    # check if lemma is provable on its own using induction
    fresh = Int('fresh', ann_ctx)
    x = Int('x', ann_ctx)
    vc_fresh = (substitute(vc, (x, fresh)))
    lemma_deref = synth_dict.get('lemma_deref',[])
    # print(vc_fresh)
    (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, valid_lemmas, unfold_recdefs_z3, lemma_deref, const, vc_fresh, True)
    if false_model_z3 != None:
        print('vc cannot be proved using induction.')
    else:
        print('vc is provable using induction.')
        exit(0)
    
    # continuously get valid lemmas until VC has been proven
    while True:
        lemma = getSygusOutput(fcts_z3, axioms_python, axioms_z3,
                           valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                           vc, name, grammar_string, config_params)
        if lemma is None:
            print('CVC4 SyGuS returns unknown. Exiting.')
            exit('Instance failed.')

        addl_decls = synth_dict.get('translate_lemma_addl_decls',{})
        swap_fcts = synth_dict.get('translate_lemma_swap_fcts',{})
        replace_fcts = synth_dict.get('translate_lemma_replace_fcts',{})
        rhs_lemma = translateLemma(lemma[0], fcts_z3, addl_decls, swap_fcts, replace_fcts)
        index = int(lemma[1][-2])
        lhs_lemma = fcts_z3['recpreds-loc_1_int_bool'][index](fresh)
        z3py_lemma = Implies(lhs_lemma, rhs_lemma)

        print('proposed lemma: ' + str(z3py_lemma))
        if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
            print('lemma has already been proposed')
            if use_cex_models:
                if z3py_lemma in invalid_lemmas:
                    print('Something is wrong. Lemmas should not be reproposed in the presence of countermodels. Exiting.')
                if z3py_lemma in valid_lemmas:
                    print('This is a currently known limitation of the tool. Consider restricting your grammar to have terms of lesser height.')
                exit('Instance failed.')
            else:
                # Using bag-of-lemmas + prefetching formulation, or the reproposed lemma is a valid one. Continue and hope for the best.
                continue
        (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, valid_lemmas, unfold_recdefs_z3, lemma_deref, const, z3py_lemma, True)
        if false_model_z3 != None:
            print('proposed lemma cannot be proved.')
            invalid_lemmas = invalid_lemmas + [ z3py_lemma ]
            if use_cex_models:
                cex_models = cex_models + [false_model_dict]
        else:
            valid_lemmas = valid_lemmas + [ z3py_lemma ]
            # Reset countermodels and invalid lemmas to empty because we have additional information to retry those proofs.
            cex_models = []
            invalid_lemmas = []
        # Update countermodels before next round of synthesis
        config_params['cex_models'] = cex_models
