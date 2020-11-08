from z3 import *
z3.set_param('model.compact', False)
from lemsynth.lemsynth_utils import *


def makePFP(vc, recdefs, fcts_z3, insts):
    op = vc.decl()
    if getZ3FctName(op) != '=>':
        raise ValueError('Cannot compute pfp formula if given theorem is not in implication form.')
    lhs = vc.arg(0)
    rhs = vc.arg(1)

    fresh = Int('fresh')
    skolem = Int('skolem')
    lhs_decl = lhs.decl()
    if str(lhs.arg(0)) != 'fresh':
        return BoolVal(True)
    lhs_decl_name = str(lhs_decl)
    udef = getUnfoldRecdefFct(lhs_decl_name, recdefs)
    rec_rho = udef(skolem).arg(0).arg(1)
    subst_pairs = []
    for key in fcts_z3.keys():
        if 'recpreds' in key or 'recfunctions' in key:
            continue
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            # constant symbols
            for fct in fcts_z3[key]:
                subst_rhs = substitute(rhs, (fresh, fct))
                subst_pairs = subst_pairs + [ (lhs_decl(fct), And(lhs_decl(fct), subst_rhs)) ]
        else:
        # only supporting unary functions
            for fct in fcts_z3[key]:
                # TODO: add support for n-ary symbols
                for inst in insts + [skolem]:
                    subst_rhs = substitute(rhs, (fresh, fct(inst)))
                    new_pair = (lhs_decl(fct(inst)), And(lhs_decl(fct(inst)), subst_rhs))
                    subst_pairs = subst_pairs + [ new_pair ]
    subst_rho = substitute(rec_rho, subst_pairs)
    pfp = Implies(subst_rho, substitute(rhs, (fresh, skolem)))
    return pfp

# Get false model - model where VC is false deref is a list of terms that are
# derefenced. This must be computed prior depending on the depth of instantiation.
# Only unary recursive predicates and axioms supported
def getFalseModel(axioms_z3, fcts_z3, lemmas, unfold_recdefs_z3, deref, const, vc, ip = False):
    sol = Solver()

    # add skolem variable to instantiations
    skolem = Int('skolem')
    instantiations = const + deref + ([skolem] if ip and skolem not in deref else [])
    for key in axioms_z3.keys():
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            for ax in axioms_z3[key]:
                # add axioms like next(nil) = nil, prev(nil) = nil
                sol.add(ax)
        else:
            # Currently not distinguishing by signature
            for ax in axioms_z3[key]:
                for inst in instantiations:
                    sol.add(ax(inst))

    # instantiate lemmas
    fresh = Int('fresh')
    for lemma in lemmas:
        sol.add(lemma)
        for inst in instantiations:
            new_inst = substitute(lemma, (fresh, inst))
            sol.add(new_inst)

    # unfold recursive definitions on instantiations
    for key in unfold_recdefs_z3:
        recdefs = unfold_recdefs_z3[key]
        for recdef in recdefs:
            for inst in instantiations:
                sol.add(recdef(inst))
    
    if ip:
        # Doing a proof by induction is the same as proving the corresponding PFP formula.
        # NOTE: if sat, the model produced negates the PFP, not the given theorem.
        pfp = makePFP(vc, unfold_recdefs_z3, fcts_z3, const + deref)
        sol.add(Not(pfp))
    else:
        # Not proof by induction. Simply negate the given vc. 
        sol.add(Not(vc))

    # check satisfiability
    if (sol.check() == sat):
        m = sol.model()
        return m

    else:
        print("No model available. Given theorem was proved.")
        return None


# Get false model in dictionary representation. Only need values of
# dereferenced variables and constants, nothing else will be used in SyGuS file
# generation.
# def getFalseModelDict(fcts_z3, axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc, ip = False):
#     false_model_z3 = getFalseModel(axioms_z3, fcts_z3, lemmas, unfold_recdefs_z3, deref, const, vc, ip)
#
#     if false_model_z3 == None:
#         return (None, None)
#
#     false_model_dict = {}
#
#     # Add as elements to the model the instantiated terms (and constants).
#     # These act the same way as the 'elems' field in the true models (modulo the proving power of natural proofs).
#     # NOTE: Add the skolem variable(s) as well for proofs using the induction principle.
#     # Currently this is just the variable named 'skolem'. Must make the implementation more principled.
#     pfp = makePFP(vc, unfold_recdefs_z3, fcts_z3, const + deref)
#     # Get formula-driven instantiations to include in the finite partial model extracted from the z3 model
#     # This ensures that the queries given to the solver can be replayed on the finite model with the same results.
#     formula_driven_instantiations = getFgTerms(pfp)
#     instantiations = formula_driven_instantiations + const + deref
#     # Sort instantiated terms by height as they can then be added to the model dictionary from smaller to larger terms
#     instantiations.sort(key=getExprHeight)
#
#     elems = []
#     for inst in instantiations:
#         inst_value = false_model_z3.eval(inst, model_completion=True)
#         elems = elems + [convertZ3ValueTypetoPython(inst_value)]
#     false_model_dict['elems'] = elems
#
#     for key in fcts_z3.keys():
#         signature = getFctSignature(key)
#         arity = signature[0]
#         if arity == 0:
#             # constant symbols
#             for fct in fcts_z3[key]:
#                 fct_name = getZ3FctName(fct)
#                 constant_value = false_model_z3.eval(fct,model_completion=True)
#                 false_model_dict[fct_name] = convertZ3ValueTypetoPython(constant_value)
#         else:
#             # only supporting unary functions/recursive definitions
#             for fct in fcts_z3[key]:
#                 fct_name = getZ3FctName(fct)
#                 false_model_dict[fct_name] = {}
#                 # TODO: add support for n-ary symbols
#                 for inst in instantiations:
#                     inst_value = false_model_z3.eval(inst, model_completion=True)
#                     # model_compress has been enabled (see at the top of this file). Should return arrays rather than lambdas
#                     # Store values of functions under instantiated terms in the model
#                     fct_of_inst_value = false_model_z3.eval(fct(inst), model_completion=True)
#                     inst_value_python = convertZ3ValueTypetoPython(inst_value)
#                     fct_of_inst_value_python = convertZ3ValueTypetoPython(fct_of_inst_value)
#                     false_model_dict[fct_name][inst_value_python] = fct_of_inst_value_python
#     # Update false_model_dict with instantiated terms
#     for inst in instantiations:
#         inst_value = false_model_z3.eval(inst, model_completion=True)
#         false_model_dict = modelDictUpdate(false_model_dict,inst,inst_value)
#     # Return false model: both the z3 model and the dictionary.
#     return (false_model_z3, false_model_dict)
