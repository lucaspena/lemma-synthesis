#############################

# Experimental features: DO NOT USE OR ALTER


############################

from z3 import *
z3.set_param('model.compact', False)
from lemsynth_utils import *
from true_models import *
from false_models import *

import itertools

def collectRecdefRecursiveCallArgs(recdef_name, expression):
    # Searches for the occurrences of the recdef in the body and returns a list of args it is applied on
    declaration = expression.decl()
    declaration_name = getZ3FctName(declaration)
    args = expression.children()
    if declaration_name == recdef_name:
        return [tuple(args)]
    else:
        recursive_call_args = []
        for arg in args:
            recursive_call_args = recursive_call_args + collectRecdefRecursiveCallArgs(recdef_name, arg)
        return recursive_call_args

# Obtains \bot for given sort so the base case condition can be generated
# TODO: LONG TERM: VERY IMPORTANT: make this less hacky by generalising sorts to option types or having an extra bottom element acting as \bot
def getBottomElementAndComparisonZ3(key):
    ret_type = getFctSignature(key)[2]
    if ret_type == 'bool':
        return (BoolVal(False), lambda x: x)
    elif ret_type == 'int':
        # Very large negative number
        return (IntVal(-1000), lambda x: x > 0)
    elif ret_type == 'set-int':
        # Set containing negative number
        # This is ok because this function will only ever be called on models with positive numbers as elements
        return (SetAdd(EmptySet(IntSort()), IntVal(-1)), lambda x: Not(IsMember(IntVal(-1),x)))
    else:
        raise ValueError('Sort name ' + ret_type + 'is not supported')

def collectRankConstraints(recdef_class, unfold_expr):
    # Assuming defs are either of the form recdef == unfolded_body or recdef <=> unfolded body where <=> is sugar for And(=>,<=)
    declaration = unfold_expr.decl()
    declaration_name = getZ3FctName(declaration)
    if declaration_name == 'and':
        recdef_implies_body = unfold_expr.arg(0)
        recdef_with_args = recdef_implies_body.arg(0)
        recdef_body = recdef_implies_body.arg(1)
    elif declaration_name == '=':
        recdef_with_args = unfold_expr.arg(0)
        recdef_body = unfold_expr.arg(1)
    else:
        raise ValueError('Unfold recdef expression must either be a == expression (for functions) or <=> expression')
    # Process recdef to collect rank constraints
    recdef_fct = recdef_with_args.decl()
    recdef_name = getZ3FctName(recdef_fct)
    recdef_call_args = recdef_with_args.children()
    recdef_arity = len(recdef_call_args)
    # Base case condition will be in terms of the call args
    # To get base case condition subsitute all occurrences of recdef in the body with false (or more generally the bottom element)
    # Hacky way of handling
    # TODO: VERY IMPORTANT: LONG TERM: make this less hacky
    (bottom_elt_z3, if_not_bot) = getBottomElementAndComparisonZ3(recdef_class)
    base_case_expression = substituteSubformula(recdef_body, [(recdef_name, lambda recdef, arg_tuple: bottom_elt_z3)])
    base_case_condition = if_not_bot(base_case_expression)

    recdef_recursive_call_args = collectRecdefRecursiveCallArgs(recdef_name, recdef_body)
    # Assuming recdef is only over foreground sort, and that sort is represented by integers
    rank_function_signature = [IntSort()]* (recdef_arity + 1)
    rank_function = Function('rank_'+recdef_name, *rank_function_signature)
    if len(recdef_recursive_call_args) == 1:
        # Special case: only one recursive call. Rank can be given as exactly one more than the recursive call.
        recursive_call_arg = recdef_recursive_call_args[0]
        increasing_rank_condition = rank_function(*recdef_call_args) == rank_function(*recursive_call_arg) + 1
    else:
        # Multiple recursive calls. Rank must be generally increasing.
        increasing_rank_condition = And([rank_function(*recdef_call_args) > rank_function(*recursive_call_arg) for recursive_call_arg in recdef_recursive_call_args])

    rank_constraint = If(base_case_condition, rank_function(*recdef_call_args) == 0, increasing_rank_condition)
    if_recdef_then_rank_constraint = Implies(if_not_bot(recdef_with_args), rank_constraint)
    return if_recdef_then_rank_constraint


def getNTrueLfpModelsSMT(elems, fcts_z3, axioms_z3, unfold_recdefs_z3, num_true_lfp_models = 1):
    # Assuming elems to be integers
    # Assuming fcts, recdefs, and axioms are only on the foreground sort
    z3_elems = [IntVal(elem) for elem in elems]

    sol = Solver()

    # Closed universe assumptions
    for fct_class in fcts_z3.keys():
        signature = getFctSignature(fct_class)
        if signature[3] == True:
            # Recursive definition. Continue.
            continue
        elif signature[2] != 'int':
            # Output type is not integer. Continue.
            continue
        arity = signature[0]
        if arity == 0:
            # Constant symbols
            closed_constraint = Or([fct == elem for elem in elems])
            sol.add(closed_constraint)
        else:
            if arity == 1:
                input_values = z3_elems
            else:
                input_values = [tuple(x) for x in itertools.product(z3_elems, repeat=arity)]
            fcts =  fcts_z3[fct_class]
            for fct in fcts:
                for input_value in input_values:
                    # Universe is closed
                    if arity == 1:
                        closed_constraint = Or([fct(input_value) == elem for elem in z3_elems])
                    else:
                        # Must unpack before function application as z3 functions cannot be fed tuples
                        closed_constraint = Or([fct(*input_value) == elem for elem in z3_elems])
                    sol.add(closed_constraint)

    # Recursive definitions must be evaluated correctly
    for recdef_class in unfold_recdefs_z3:
        signature = getFctSignature(recdef_class)
        arity = signature[0]
        # Arity is atleast 1 for recdefs
        if arity == 1:
            input_values = z3_elems
        else:
            input_values = [tuple(x) for x in itertools.product(z3_elems, repeat=arity)]
        unfolded_recdefs = unfold_recdefs_z3[recdef_class]
        for unfolded_recdef in unfolded_recdefs:
            # Assuming recdefs are only on foreground sort
            temp_vars = Ints(' '.join(['tmp' + str(i) for i in range(arity)]))
            temp_args = temp_vars[0] if arity == 1 else tuple(temp_vars)
            unfold_recdef_on_args = unfolded_recdef(temp_args)
            rank_constraint = collectRankConstraints(recdef_class, unfold_recdef_on_args)
            for input_value in input_values:
                # Add rank constraints to solver so recdefs are evaluated correctly
                arg_substitution = (temp_args,input_value) if arity == 1 else [(temp_args[i], input_values[i]) for i in range(arity)]
                sol.add(substitute(rank_constraint, arg_substitution))
                # Add unfolding of recdef on given input value
                sol.add(unfolded_recdef(input_value))

    # Model must satisfy axioms
    for axiom_class in axioms_z3:
        signature = getFctSignature(axiom_class)
        arity = signature[0]
        if arity == 0:
            for axiom in axioms_z3[axiom_class]:
                sol.add(axiom)
        else:
            if arity == 1:
                input_values = z3_elems
            else:
                input_values = [tuple(x) for x in itertools.product(z3_elems, repeat=arity)]
            axioms = axioms_z3[axiom_class]
            for axiom in axioms:
                for input_value in input_values:
                    sol.add(axiom(input_value))

    # Get the model that satisfies these constraints
    sat_status = sol.check()
    # print(sol.check())
    if sat_status == sat:
        m = sol.model()
        # print(m.sexpr())
        return m
    else:
        print("No true lfp model satisfying constraints was found.")
        return None



#############################################################
# Demo showing use of main function in file

# def Iff(b1, b2):
#     return And(Implies(b1, b2), Implies(b2, b1))
# x, nil = Ints('x nil')
# next = Function('next', IntSort(), IntSort())
# list = Function('list', IntSort(), BoolSort())
# hlist = Function('hlist', IntSort(), SetSort(IntSort()))
# def ulist_z3(x):
#     return Iff( list(x), If(x == nil, True, list(next(x))) )
# def uhlist_z3(x):
#     emptyset_intsort = EmptySet(IntSort())
#     return hlist(x) == If(x == nil, emptyset_intsort, SetAdd(hlist(next(x)),x) )
# model = getNTrueModelsSMT([1,2,3], {'1_int_int': [next]}, {'0':[next(1) == 2, next(2) == 2, nil == 3, next(nil) == nil]}, {'1_int_bool': [ulist_z3], '1_int_set-int': [uhlist_z3]})
# model.sexpr()