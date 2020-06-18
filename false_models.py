from z3 import *
z3.set_param('model.compact', False)

from lemsynth_utils import *

def makeIP(lhs, rhs, recdefs, fcts_z3, insts):
    fresh = Int('fresh')
    skolem = Int('skolem')
    lhs_decl = lhs.decl()
    if str(lhs.arg(0)) != 'fresh':
        return True
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
                subst_pairs = subst_pairs + [ (lhs_decl(fct), subst_rhs) ]
        else:
        # only supporting unary functions
            for fct in fcts_z3[key]:
                # TODO: add support for n-ary symbols
                for inst in insts + [skolem]:
                    subst_rhs = substitute(rhs, (fresh, fct(inst)))
                    subst_pairs = subst_pairs + [ (lhs_decl(fct(inst)), subst_rhs) ]
    subst_rho = substitute(rec_rho, subst_pairs)
    pfp = Implies(subst_rho, substitute(rhs, (fresh, skolem)))
    induction_principle = Implies(pfp, ForAll(fresh, Implies(lhs, rhs)))
    return induction_principle

# Get false model - model where VC is false deref is a list of terms that are
# derefenced. This must be computed prior depending on the depth of instantiation.
# Only unary recursive predicates and axioms supported
def getFalseModel(axioms_z3, fcts_z3, lemmas, unfold_recdefs_z3, deref, const, vc, ip = False):
    sol = Solver()

    # only useful for current implementation. must be distinguished by signature in general
    instantiations = const + deref
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
        for inst in instantiations:
            inst = substitute(lemma, (fresh, inst))
            sol.add(inst)

    # generate induction principle
    if ip:
        lhs = vc.arg(0)
        rhs = vc.arg(1)
        def_name = lhs.decl()
        induction_principle = makeIP(lhs, rhs, unfold_recdefs_z3, fcts_z3, const + deref)
        sol.add(induction_principle)

    # unfold recursive definitions on instantiations
    for key in unfold_recdefs_z3:
        recdefs = unfold_recdefs_z3[key]
        for recdef in recdefs:
            for inst in instantiations:
                sol.add(recdef(inst))
                # unfold on skolemized variable from generated induction principle
                if ip:
                    skolem = Int('skolem')
                    sol.add(recdef(skolem))

    # negate VC
    sol.add(Not(vc))

    # check satisfiability and print model in format CVC4 can handle
    if (sol.check() == sat):
        m = sol.model()
        return m

    else:
        print("No model available. Lemma was proved.")
        return None

def convertZ3ValueTypetoPython(value):
    if type(value) == BoolRef:
        return bool(value)
    elif type(value) == IntNumRef:
        # NOTE: returns a bignum
        return value.as_long()
    elif type(value) == ArrayRef:
        # Only sets of integers supported
        # Convert to a python set recursively
        declaration = value.decl()
        if str(declaration) == 'K':
            if bool(value.children()[0]) == True:
                # K(Int, True) is the set of all natural numbers
                raise ValueError('Infinite set obtained. Something is wrong.')
            else:
                # K(Int, False) is the empty set
                return set()
        elif str(declaration) == 'Store':
            # Recursively construct the set
            expr_children = value.children()
            sub_set = convertZ3ValueTypetoPython(expr_children[0])
            element = convertZ3ValueTypetoPython(expr_children[1])
            membership = convertZ3ValueTypetoPython(expr_children[2])
            if membership == True:
                return sub_set | {element}
            elif membership == False:
                return sub_set
            else:
                raise ValueError('Store expression asssigns element to neither True nor False')
        else:
            # Cannot handle this case, if it exists
            raise ValueError('ArrayRef object is neither a constant array nor a Store expression. Something is wrong.')
    else:
        raise ValueError('Model entry is neither IntNumRef, BoolRef, nor ArrayRef. Type unsupported.')

# Get false model in dictionary representation. Only need values of
# dereferenced variables and constants, nothing else will be used in SyGuS file
# generation.
# TODO - VERY IMPORTANT: the dictionaries' entries are not integers, but Z3 types
#  like IntNumRef and such. Must fix to avoid subtle issues
def getFalseModelDict(fcts_z3, axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc, ip = False):
    false_model_z3 = getFalseModel(axioms_z3, fcts_z3, lemmas, unfold_recdefs_z3, deref, const, vc)

    if false_model_z3 == None:
        # Lemmas generated up to this point are useful. Exit.
        print('Lemmas used to prove original vc:')
        for lemma in lemmas:
            print(lemma)
        exit(0)

    false_model_dict = {}
    for key in fcts_z3.keys():
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            # constant symbols
            for fct in fcts_z3[key]:
                fct_name = getZ3FctName(fct)
                constant_value = false_model_z3.eval(fct,model_completion=True)
                false_model_dict[fct_name] = convertZ3ValueTypetoPython(constant_value)
        else:
            # only supporting unary functions/recursive definitions
            for fct in fcts_z3[key]:
                fct_name = getZ3FctName(fct)
                false_model_dict[fct_name] = {}
                # TODO: add support for n-ary symbols
                instantiations = const + deref
                for inst in instantiations:
                    inst_value = false_model_z3.eval(inst, model_completion=True)
                    # model_compress has been enabled (see at the top of this file). Should return arrays rather than lambdas
                    fct_of_inst_value = false_model_z3.eval(fct(inst), model_completion=True)
                    inst_value_python = convertZ3ValueTypetoPython(inst_value)
                    fct_of_inst_value_python = convertZ3ValueTypetoPython(fct_of_inst_value)
                    false_model_dict[fct_name][inst_value_python] = fct_of_inst_value_python
    return (false_model_z3, false_model_dict)
