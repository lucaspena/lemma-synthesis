import subprocess
import itertools

from z3 import *
set_param('model.compact', False)

import lemsynth.options as options
import lemsynth.true_models
from lemsynth.induction_constraints import generate_pfp_constraint
from lemsynth.cvc4_compliance import cvc4_complicant_formula_sexpr

from naturalproofs.decl_api import get_uct_signature, get_recursive_definition
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.extensions.finitemodel import recover_value
from naturalproofs.extensions.finitemodel import FiniteModel
from naturalproofs.decl_api import get_vocabulary, is_var_decl


# Add constraints from each model into the given solver
# Look through model's function entries and adds each input-output constraint
def modelToSolver(model, vocab, sol, annctx):
    for fct in vocab:
        arity = fct.arity()
        if arity == 0:
            # TODO: handle constant symbols
            # constant symbol
            continue
        else:
            fct_name = fct.name()
            uct_signature = get_uct_signature(fct, annctx)
            for input_arg in model[fct_name].keys():
                output_value = model[fct_name][input_arg]
                if isinstance(output_value, set):
                    output_value_converted = recover_value(output_value, uct_signature[-1])
                else:
                    output_value_converted = output_value

                if isinstance(input_arg, tuple):
                    # arg must be unpacked as *arg before constructing the Z3 term
                    sol.add(fct(*input_arg) == output_value_converted)
                else:
                    sol.add(fct(input_arg) == output_value_converted)

def translateSet(s, fct_range):
    out = ''
    for i in s:
        out += '(insert ' + str(i) + ' '
    out += '(as emptyset (' + fct_range + '))'
    for i in s:
        out += ')'
    return out

# translate tuple of args to conjunction of equalities in smt format
def translateArgs(elt):
    out = ''
    for i in range(len(elt)):
        out += '(= x!' + str(i) + ' ' + str(elt[i]) + ') '
    return out[:-1]

# get header of set function
def getHeader(fct, fct_range):
    out = '(define-fun ' + fct.name() + ' ('
    for i in range(0, fct.arity()):
        out += '(x!' + str(i) + ' ' + str(fct.domain(i)) + ') '
    out = out[:-1] + ') '
    out += '(' + fct_range + ')'
    return out

# translate models of fully evaluated sets to smtlib format
def translateModelsSets(models, set_defs):
    out = ''
    for fct in set_defs:
        fct_name = fct.name()
        fct_range = 'Set ' + str(fct.range().domain())
        curr_fct = getHeader(fct, fct_range) + '\n'
        body = ''
        for model in models:
            curr_model_body = ''
            for elt in model[fct_name]:
                args = translateArgs(elt)
                set_translate = translateSet(model[fct_name][elt], fct_range)
                curr_model_body += '  (ite (and ' + args + ') ' + set_translate + '\n'
            body += curr_model_body
        body += '  (as emptyset (' + fct_range + '))'
        for model in models:
            for elt in model[fct_name]:
                body += ')'
        curr_fct += body + ')\n\n'
        out += curr_fct
    return out


# Generate single model from a given list of models
# Returns the definitions for functions and recdefs.
# TODO: consider not using z3 for this and just generating the definitions using python code
def sygusBigModelEncoding(models, vocab, set_defs, annctx):
    sol = Solver()
    for model in models:
        modelToSolver(model, vocab, sol, annctx)
    sol.check()
    m = sol.model()
    set_encodings = translateModelsSets(models, set_defs)
    return set_encodings + m.sexpr()


# Generate constraints corresponding to false model for SyGuS
def generateFalseConstraints(model, lemma_args, terms, annctx):
    const = [arg for arg in lemma_args if not is_var_decl(arg, annctx)]
    const_values = ' '.join([str(model.smtmodel.eval(cs, model_completion=True).as_long() + model.offset) for cs in const])
    constraints = ''
    lemma_arity = len(lemma_args) - len(const)
    eval_terms = {model.smtmodel.eval(term, model_completion=True).as_long() + model.offset for term in terms}
    args = itertools.product(eval_terms, repeat=lemma_arity)
    for arg in args:
        curr = ''
        recs = set(map(lambda x: x[0], get_recursive_definition(None, True, annctx)))
        recs = sorted(recs, key=lambda x: x.name())
        arg_str = [str(elt) for elt in arg]
        for i in range(len(recs)):
            if recs[i].range().name() != 'Bool':
                continue
            rec_arity = recs[i].arity()
            rswitch = '(= rswitch {})'.format(i)
            # Assuming first 'arity' arguments of lemma variables are arguments for recursive definition
            lhs = '({} {})'.format(recs[i].name(), ' '.join(arg_str[:rec_arity]))
            rhs = '(lemma {} {})'.format(' '.join(arg_str), const_values)
            curr_constraint = '(=> {} (not (=> {} {})))\n'.format(rswitch, lhs, rhs)
            curr = curr + curr_constraint
        constraints = constraints + '(and {})\n'.format(curr)
    out = '(constraint (or {}))'.format(constraints)
    return out


# # Generate constraints corresponding to one true model for SyGuS
# def generateTrueConstraints(model, const, fcts_z3):
#     constraints = ''
#     const_values = ' '.join([str(modelDictEval(model, constant_symbol)) for constant_symbol in const])
#     elems = model['elems']
#     for elem in elems:
#         # TODO: only one universally quantified variable in desired lemma for now
#         recs = fcts_z3['recpreds-loc_1_int_bool']
#         for i in range(len(recs)):
#             curr_constraint = '(=> (= rswitch {0}) (=> ({1} {2}) (lemma {2} {3})))\n'.format(i, str(recs[i]), elem, const_values)
#             constraints = constraints + curr_constraint
#     out = '(constraint (and {0}))\n'.format(constraints)
#     return out
# 
# # Generate constraints corresponding to all true models for SyGuS
# def generateAllTrueConstraints(models, const, fcts_z3):
#     out = ''
#     for model in models:
#         out = out + generateTrueConstraints(model, const, fcts_z3)
#     return out


def generateCexConstraints(model, lemma_args, annctx):
    constraints = ''
    recs = set(x[0] for x in get_recursive_definition(None, True, annctx))
    recs = sorted(recs, key=lambda x: x.name())
    # TODO: NOTE: only one universally quantified variable in desired lemma for now
    for i in range(len(recs)):
        if recs[i].range().name() != 'Bool':
            continue
        pfp_formula = generate_pfp_constraint(recs[i], lemma_args, model, annctx)
        pfp_formula_sexpr = cvc4_complicant_formula_sexpr(pfp_formula)
        curr_constraint = '(=> (= rswitch {0}) {1})'.format(i, pfp_formula_sexpr)
        constraints = constraints + curr_constraint
    out = '(constraint (and {0}))\n'.format(constraints)
    return out


# Generate constraints corresponding to counterexample models
def generateAllCexConstraints(models, lemma_args, annctx):
    out = ''
    for model in models:
        out = out + generateCexConstraints(model, lemma_args, annctx)
    return out


# write output to a file that can be parsed by CVC4 SyGuS
def getSygusOutput(lemmas, lemma_args, vc, problem_instance_name, grammar_string, config_params, annctx):
    # Make log folder if it does not exist already
    os.makedirs(options.log_file_path, exist_ok=True)

    out_file = '{}/out_{}.sy'.format(options.log_file_path, problem_instance_name)

    vcsolver = NPSolver()
    vcsolver.options.instantiation_mode = proveroptions.depth_one_untracked_lemma_instantiation
    vc_npsolution = vcsolver.solve(vc, lemmas)
    if not vc_npsolution.if_sat:
        # Lemmas generated up to this point are useful. Exit.
        print('VC has been proven. Lemmas used to prove original vc:')
        for lemma in lemmas:
            print(lemma[1])
        exit(0)

    vc_extraction_terms = vc_npsolution.extraction_terms
    vc_instantiation_terms = vc_npsolution.instantiation_terms
    false_finitemodel = FiniteModel(vc_npsolution.model, vc_extraction_terms, annctx=annctx)

    use_cex_models = config_params.get('use_cex_models', True)
    cex_models = config_params.get('cex_models', [])

    # Adding offsets to make sure: (i) all elements in all models are positive (ii) models do not overlap
    # Making the universe of the false model positive
    false_model_fg_universe = false_finitemodel.get_fg_elements()
    non_negative_offset = min(false_model_fg_universe)
    if non_negative_offset >= 0:
        non_negative_offset = 0
    else:
        false_finitemodel.recompute_offset = True
        false_finitemodel.add_fg_element_offset(abs(non_negative_offset))
    false_model_relative_offset = max(false_model_fg_universe) + abs(non_negative_offset) + 1

    # Add counterexample models to true models if use_cex_models is True
    accumulated_offset = false_model_relative_offset
    if use_cex_models:
        cex_models_with_offset = []
        for cex_model in cex_models:
            # Deepcopy the countermodels so the originals are not affected
            cex_offset_model = cex_model.copy()
            # Make the universe of the model positive and shift the model by accumulated offset
            cex_model_universe = cex_offset_model.get_fg_elements()
            non_negative_offset = min(cex_model_universe)
            if non_negative_offset >= 0:
                non_negative_offset = 0
            cex_offset_model.add_fg_element_offset(abs(non_negative_offset) + accumulated_offset)
            # Compute new accumulated offset
            accumulated_offset = max(cex_model_universe) + abs(non_negative_offset) + accumulated_offset + 1
            # Add model to cex_models_with_offset
            cex_models_with_offset = cex_models_with_offset + [cex_offset_model]
        cex_models = cex_models_with_offset
    # true_model_offset = accumulated_offset

    # elems = config_params.get('elems', [])

    all_models = [cex_model.finitemodel for cex_model in cex_models] + [false_finitemodel.finitemodel]

    vocab = get_vocabulary(annctx)
    if options.exclude_set_type_definitions_switch == 'on':
        # To assess whether removing set type definitions will help in cases 
        # where the lemma does not feature set reasoning.
        set_defs = {}
    else:
        set_defs = {func for func in vocab if 'Array' in str(func.range())}
    vocab = vocab.difference(set_defs)

    sygus_model_definitions = sygusBigModelEncoding(all_models, vocab, set_defs, annctx)
    with open(out_file, 'w') as out:
        out.write('(set-logic ALL)')
        out.write('\n')
        out.write(';; combination of true models and false model\n')
        out.write(sygus_model_definitions)
        out.write('\n\n')
        # Must modify grammar string to include arguments based on problem parameters.
        # Or generate the grammar file based on problem parameters.
        out.write(grammar_string)
        out.write('\n')
        out.write(';; pfp constraints from counterexample models\n')
        if use_cex_models:
            cex_pfp_constraints = generateAllCexConstraints(cex_models, lemma_args, annctx)
            out.write(cex_pfp_constraints)
            out.write('\n')
        out.write('\n')
        out.write(';; constraints from false model\n')
        false_constraints = generateFalseConstraints(false_finitemodel, lemma_args, vc_instantiation_terms, annctx)
        out.write(false_constraints)
        out.write('\n')
        out.write('\n')
        out.write(';; constraints from true models\n')
        true_constraints = ''
        # true_constraints = generateAllTrueConstraints(true_models, lemma_args, fcts_z3)
        out.write(true_constraints)
        out.write('\n')
        out.write('(check-synth)')
        out.close()
    # Optionally prefetching a bunch of lemmas to check each one rather than iterating through each one.
    # DO NOT use prefetching. Code is not updated to handle current sygus output.
    if options.experimental_prefetching_switch == 'on':
        # Must include a parameter in the overall call for number of lemmas to be prefetched
        # Currently hardcoded
        prefetch_count = config_params.get('prefetch_count', 1)
        k_lemmas_file = '{}{}_KLemmas.txt'.format(options.log_file_path, problem_instance_name)
        sygus_proc = subprocess.Popen(['cvc4', '--lang=sygus2', '--sygus-stream', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        prefetch_proc = subprocess.Popen(['python3', 'prefetch_lemmas.py', k_lemmas_file, str(prefetch_count)], stdin=sygus_proc.stdout, stdout=subprocess.PIPE, universal_newlines=True)
        try:
            # Timeout given is given in seconds.
            # Currently hardcoded. Must make it a parameter
            standard_out, standard_err = prefetch_proc.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            prefetch_proc.kill()
        sygus_proc.kill()
        with open(k_lemmas_file, 'r') as k_lemmas:
            lemmas = k_lemmas.readlines()
            # Lemmas are returned as strings. Possibly terminated by '\n'
            # Removing possible '\n' before returning
            lemmas = [lemma[:-1] if lemma[-1] == '\n' else lemma for lemma in lemmas]
            # List of lemmas returned in string format
            return lemmas
    else:
        proc = subprocess.Popen(['cvc4', '--lang=sygus2', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        cvc4_out, err = proc.communicate()
        if cvc4_out == '':
            print(err)
            return None
        elif cvc4_out == 'unknown\n':
            print('CVC4 SyGuS returns unknown. Exiting.')
            return None
        else:
            lemma = str(cvc4_out).split('\n')[1:][:-1]
            return lemma
