import subprocess

from z3 import *
set_param('model.compact', False)
from true_models import *
from false_models import *
from lemsynth_utils import *
from set_sort import *

# Add constraints from each model into the given solver
# Look through model's function entries and adds each input-output constraint
def modelToSolver(model, fcts_z3, sol):
    for key in fcts_z3.keys():
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            # TODO: handle constant symbols
            # constant symbol
            continue
        else:
            for fct in fcts_z3[key]:
                # no need to distinguish by signature as models are organised by
                # dictionaries pointing from input to output
                fct_name = getZ3FctName(fct)
                for input_arg in model[fct_name].keys():
                    output_value = model[fct_name][input_arg]
                    if isinstance(output_value, set):
                        # This step is slightly wrong. We do not know what the intended sort of the output value set's elements is.
                        # We are assuming integers by default, because that is the only thing being supported. Perhaps booleans. Nothing that cannot be distinguished.
                        # This is taking the implementation deeper into a territory where it will be hard to distinguish sorts implemented by the same python type.
                        output_value_converted = getZ3SetConstEncoding('int', output_value)
                    else:
                        output_value_converted = output_value

                    if isinstance(input_arg, tuple):
                        # arg must be unpacked as *arg before constructing the Z3 term
                        sol.add(fct(*input_arg) == output_value_converted)
                    else:
                        sol.add(fct(input_arg) == output_value_converted)

def translateSet(s):
    out = ''
    for i in s:
        out += '(insert ' + str(i) + ' '
    out += '(as emptyset (Set Int))'
    for i in s:
        out += ')'
    return out

def translateModelsSets(models, set_defs):
    out = ''
    for key in set_defs:
        for fct in set_defs[key]:
            curr_fct = '(define-fun ' + str(fct) + ' ((x!0 Int)) (Set Int)\n'
            body = ''
            for model in models:
                fct_name = getZ3FctName(fct)
                curr_model_body = ''
                for elt in model[fct_name]:
                    curr_model_body += '  (ite (= x!0 ' + str(elt) + ') ' + translateSet(model[fct_name][elt]) + '\n'
                body += curr_model_body
            body += '  (as emptyset (Set Int))'
            for model in models:
                for elt in model[fct_name]:
                    body += ')'
            curr_fct += body + ')\n\n'
            out += curr_fct
    return out

# Generate single model from a given list of models
# Returns the definitions for functions and recdefs.
# TODO: consider not using z3 for this and just generating the definitions using python code
# TODO - VERY IMPORTANT: subtle issue here. The true models' entries are
#  actually integers, whereas the false model's entries are Z3 types like
#  IntNumRef, etc. Must fix this during false model dict generation.
def sygusBigModelEncoding(models, fcts_z3, set_defs):
    sol = Solver()
    for model in models:
        modelToSolver(model, fcts_z3, sol)
    sol.check()
    # print(sol.check())
    # print(sol.sexpr())
    m = sol.model()
    set_encodings = translateModelsSets(models, set_defs)
    return set_encodings + m.sexpr()

# Generate constraints corresponding to false model for SyGuS
def generateFalseConstraints(model_dict, deref, const, fcts_z3):
    constraints = ''
    const_values = ' '.join([ str(model_dict[getZ3FctName(constant_symbol)]) for constant_symbol in const])
    for arg in const + deref:
        # In general, arg will range over the tuples of instantiated terms
        # TODO: check if this part generalises to k-ary terms. modelDictEval takes k-ary terms
        arg_value = modelDictEval(model_dict, arg)
        curr = ''
        recs = fcts_z3['recpreds-loc_1_int_bool']
        for i in range(len(recs)):
            curr_constraint = '(=> (= rswitch {0}) (not (=> ({1} {2}) (lemma {2} {3}))))\n'.format(i, str(recs[i]), arg_value, const_values)
            curr = curr + curr_constraint
        constraints = constraints + '(and {0})\n'.format(curr)
    out = '(constraint (or {0}))'.format(constraints)
    return out

# Old implementation that uses false_model_z3 instead of false_model_dict
# def generateFalseConstraints(model_dict, deref, const):
#     constraints = ''
#     # Must convert result of model.eval using as_string() because returned value is a Z3 type like IntNumRef
#     const_values = ' '.join([model_z3.eval(constant_symbol, model_completion=True).as_string() for constant_symbol in const])
#     for arg in const + deref:
#         # In general, arg will range over the tuples of instantiated terms
#         arg_value = model_z3.eval(arg, model_completion=True)
#         constraints = constraints + '(not (lemma {0} {1}))\n'.format(arg_value, const_values)
#     out = '(constraint (or {0}))'.format(constraints)
#     return out

# Generate constraints corresponding to one true model for SyGuS
def generateTrueConstraints(model, const, fcts_z3):
    constraints = ''
    const_values = ' '.join([str(model[getZ3FctName(constant_symbol)]) for constant_symbol in const])
    elems = model['elems']
    for elem in elems:
        # TODO: only one universally quantified variable in desired lemma for now
        recs = fcts_z3['recpreds-loc_1_int_bool']
        for i in range(len(recs)):
            curr_constraint = '(=> (= rswitch {0}) (=> ({1} {2}) (lemma {2} {3})))\n'.format(i, str(recs[i]), elem, const_values)
            constraints = constraints + curr_constraint
    out = '(constraint (and {0}))\n'.format(constraints)
    return out

# Generate constraints corresponding to all true models for SyGuS
def generateAllTrueConstraints(models, const, fcts_z3):
    out = ''
    for model in models:
        out = out + generateTrueConstraints(model, const, fcts_z3)
    return out

###############################################################################
# Setting lemma synthesis options here. DO NOT MODIFY.
experimental_prefetching_switch = 'off'
exclude_set_type_definitions_switch = 'off'
###############################################################################
# write output to a file that can be parsed by CVC4 SyGuS
def getSygusOutput(elems, config_params, fcts_z3, axioms_python, axioms_z3, lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const, vc, problem_instance_name):
    grammar_file = 'grammar_{0}.sy'.format(problem_instance_name)
    out_file = 'out_{0}.sy'.format(problem_instance_name)

    # TODO: false model currently does not have an 'elems' entry. It is not complete either.
    # However, it works because we only need the false model to provide us with valuations of the dereferenced terms.
    # Also works because the lemma for the current class of examples is not going to use any terms that have not already been explicitly computed.
    # One fix is to evalaute all terms within the false model into itself. Hopefully that can be done easily.
    (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc)
    if false_model_z3 == None:
        # Lemmas generated up to this point are useful. Exit.
        print('Lemmas used to prove original vc:')
        for lemma in lemmas:
            print(lemma)
        exit(0)
    
    # Adding offsets to make sure: (i) all elements in all models are positive (ii) true and false models do not overlap
    # Making the universe of the false model positive
    false_model_dict = makeModelUniverseNonNegative(false_model_dict)
    false_model_relative_offset = getRelativeModelOffset(false_model_dict)

    # Add counterexample models to true models if use_cex_models is True
    use_cex_models = config_params.get('use_cex_models', False)
    cex_models = config_params.get('cex_models', [])
    accumulated_offset = false_model_relative_offset
    if use_cex_models:
        cex_models_with_offset = []
        for cex_model in cex_models:
            # Make the universe of the model positive
            cex_model_positive_universe = makeModelUniverseNonNegative(cex_model)
            # Shift the model by accumulated offset
            cex_model_with_offset = addOffset(cex_model_positive_universe, lambda x: accumulated_offset + x)
            # Compute new accumulated offset
            accumulated_offset = getRelativeModelOffset(cex_model_with_offset)
            # Add model to cex_models_with_offset
            cex_models_with_offset = cex_models_with_offset + [cex_model_with_offset]
        cex_models = cex_models_with_offset
    true_model_offset = accumulated_offset

    true_models = getNTrueModels(elems, fcts_z3, unfold_recdefs_python, axioms_python, true_model_offset, config_params)
    true_models = cex_models + true_models

    all_models = true_models + [false_model_dict]
    if exclude_set_type_definitions_switch == 'on':
        # To assess whether removing set type definitions will help in cases where the lemma does not feature set reasoning.
        set_defs = {}
    else:
        set_defs = {key: fcts_z3[key] for key in fcts_z3.keys() if 'set' in key}
    fcts_z3 = {key: fcts_z3[key] for key in fcts_z3.keys() if 'set' not in key}

    sygus_model_definitions = sygusBigModelEncoding(all_models, fcts_z3, set_defs)
    with open(out_file, 'w') as out, open(grammar_file, 'r') as grammar:
        out.write('(set-logic ALL)')
        out.write('\n')
        out.write(';; combination of true models and false model\n')
        out.write(sygus_model_definitions)
        out.write('\n\n')
        grammar_string = grammar.read()
        # Must modify grammar string to include arguments based on problem parameters.
        # Or generate the grammar file based on problem parameters.
        out.write(grammar_string)
        out.write('\n')
        out.write(';; constraints from false model\n')
        false_constraints = generateFalseConstraints(false_model_dict, deref, const, fcts_z3)
        out.write(false_constraints)
        out.write('\n')
        out.write('\n')
        out.write(';; constraints from true models\n')
        true_constraints = generateAllTrueConstraints(true_models, const, fcts_z3)
        out.write(true_constraints)
        out.write('\n')
        out.write('(check-synth)')
        out.close()
    # Optionally prefetching a bunch of lemmas to check each one rather than iterating through each one.
    if experimental_prefetching_switch == 'on':
        # Must include a parameter in the overall call for number of lemmas to be prefetched
        # Currently hardcoded
        prefetch_count = config_params.get('prefetch_count',1)
        klemmas_filename = problem_instance_name + '_KLemmas.txt'
        sygus_proc = subprocess.Popen(['cvc4', '--lang=sygus2', '--sygus-stream', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        prefetch_proc = subprocess.Popen(['python3', 'prefetch_lemmas.py', klemmas_filename, str(prefetch_count)], stdin=sygus_proc.stdout, stdout=subprocess.PIPE, universal_newlines=True)
        #Timeout is given in seconds
        try:
            # Timeout given is given in seconds.
            # Currently hardcoded. Must make it a parameter
            standard_out, standard_err = prefetch_proc.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            prefetch_proc.kill()
        sygus_proc.kill()
        with open(klemmas_filename, 'r') as klemmas:
            lemmas = klemmas.readlines()
            # Lemmas are returned as strings. Possibly terminated by '\n'
            # Removing possible '\n' before returning
            lemmas = [lemma[:-1] if lemma[-1] == '\n' else lemma for lemma in lemmas]
            # List of lemmas returned in string format
            return lemmas
    else:
        proc = subprocess.Popen(['cvc4', '--lang=sygus2', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        cvc4_out, err = proc.communicate()
        if cvc4_out == 'unknown\n':
            return None
        else:
            lemma = str(cvc4_out).split('\n')[1:][:-1]
            return lemma
