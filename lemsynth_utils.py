from z3 import *
set_param('model.compact', False)
import re

############################
# Support for python models

# Implementing a copy function because dictionary with dictionary entries is not
# copied as expected. The inner dictionaries are stll passed by reference
# Consider doing a more general and systematic deepcopy implementation
def deepcopyModel(model):
    new_model = {}
    for key in model.keys():
        entry = model[key]
        if isinstance(entry,list) or isinstance(entry,dict):
            new_model[key] = entry.copy()
        else:
            new_model[key] = model[key]
    return new_model

# Returns the model's universe of elements
def modelUniverse(value):
    if isinstance(value, str):
        # Names of functions. No need to return these
        return set()
    elif isinstance(value, bool):
        return {value}
    elif isinstance(value, int):
        return {value}
    elif isinstance(value, set):
        return value
    elif isinstance(value, dict):
        universe = set()
        for key in value.keys():
            if key == 'elems':
                # The value is going to be a list. Simply add the elements to the universe set
                universe = universe | set(value[key])
            else:
                universe = universe | modelUniverse(key)
                universe = universe | modelUniverse(value[key])
        return universe
    else:
        raise ValueError('Entry type {} not supported'.format(str(type(value))))

# Returns the highest absolute value among the integers in the model to act as an offset for further models
def getRelativeModelOffset(model):
    # TODO: handle cases where the model universe has objects other than booleans or integers
    model_values = modelUniverse(model)
    model_integer_values = [val for val in model_values if isinstance(val, int)]
    model_offset = max(abs(max(model_integer_values)), abs(min(model_integer_values))) + 1
    return model_offset

def makeModelUniverseNonNegative(model):
    # TODO: handle cases where the model universe has objects other than booleans or integers
    model_values = modelUniverse(model)
    model_integer_values = [val for val in model_values if isinstance(val, int)]
    min_val = min(model_integer_values)
    max_val = max(model_integer_values)
    if min_val >= 0:
        return model
    else:
        model_offset = getRelativeModelOffset(model)
        new_model = addOffset(model, lambda x : x + model_offset)
    return new_model

# Adds offset to true models to avoid non-unique keys
# TODO: replace this function by one that substitutes values with new ones. More general.
def addOffset(model, f):
    newModel = deepcopyModel(model)
    for key in model.keys():
        if not isinstance(model[key],dict):
            # For entries corresponding to constants
            value = model[key]
            if isinstance(value, list):
                # For 'elems' entry
               new_out = [f(i) for i in value]
            elif isinstance(value, bool):
                new_out = value
            elif isinstance(value, set):
                # Assuming that the elements are intergers
                new_out = {f(elem) for elem in value}
            else:
                new_out = f(value)
            newModel[key] = new_out
        else:
            newDict = {}
            for fctkey in model[key].keys():
                new_in = f(fctkey)
                if isinstance(model[key][fctkey], bool):
                    new_out = model[key][fctkey]
                elif isinstance(model[key][fctkey], set):
                    # Assuming that the elements are integers
                    old_out = model[key][fctkey]
                    new_out = {f(value) for value in old_out}
                else:
                    new_out = f(model[key][fctkey])
                newDict[new_in] = new_out
            newModel[key] = newDict
    return newModel


def modelDictEval(model_dict, z3_term_or_python_string):
    if isinstance(z3_term_or_python_string, str):
        raise ValueError('Cannot give strings to lookup. Must be a z3py term.')
    else:
        z3_term = z3_term_or_python_string
        # Given argument is a z3 term
        # Assuming that z3_term does not have anything other than integer or boolean constants in it outside of z3 terms
        if isinstance(z3_term, IntNumRef) or isinstance(z3_term, BoolRef):
            return convertZ3ValueTypetoPython(z3_term)

        declaration = z3_term.decl()
        children = z3_term.children()
        if children == []:
            return model_dict[getZ3FctName(z3_term)]
        else:
            arity = len(children)
            if arity == 1:
                return model_dict[getZ3FctName(declaration)][modelDictEval(model_dict, children[0])]
            else:
                # In a model dictionary arguments are represented as tuples
                arg = tuple([modelDictEval(model_dict, child) for child in children])
                return model_dict[getZ3FctName(declaration)][arg]


##################################
# General unclassified utilities

# Cartesian product of two lists of elements, with a given function applied to
# the pair Default is a + function which will work if defined for the sort of
# list elements
def listProduct(ll1, ll2, combine_func = lambda x,y: x + y):
    return [ combine_func(x,y) for x in ll1 for y in ll2 ]

# Function/Predicate signatures are of the form
# input-arity_input-tuple-type_output-type. Optionally, the class name might
# begin with 'rec<something>_' for recursive functions/predicates
# Returns (arity,input-tuple-type,output-type,recursive_or_not)
def getFctSignature(fct_class):
    s = fct_class.split('_')
    if s[0].startswith('rec'):
        return (int(s[1]),tuple(s[2:-2]),s[-1],True)
    else:
        #Not a recursive definition
        if s[0] == '0':
            return (0,None,None,False)
        else:
            return (int(s[0]),tuple(s[1:-2]),s[-1],False)

# Currently the symbols are returning the variable name as a string under the
# str() operator.
# TODO: Might need to distinguish them by their Z3 types for a more reliable way
def getZ3FctName(z3_fct_variable):
    if isinstance(z3_fct_variable, FuncDeclRef):
        return z3_fct_variable.name()
    else:
        return str(z3_fct_variable)

# Extract name of recdef from the python function name.
def getRecdefName(recdef_python_function):
    # It is usually u + <name> + _python
    # TODO: Make this more systematic
    recdef_name = recdef_python_function.__name__
    return '_'.join(recdef_name[1:].split('_')[:-1])

# Extract declaration dictionary for converting cvc4 output to z3Py
def extractDecls(fcts_z3):
    z3_str = {}
    # not distinguishing by signatures
    for key in fcts_z3.keys():
        for fct in fcts_z3[key]:
            z3_str[getZ3FctName(fct)] = fct
    return z3_str

def getLemmaHeader(lemma):
    result = re.search('lemma (.*) Bool', lemma)
    params = result.group(1)[1:][:-1]
    params_list = [ i.split(' ')[0] for i in re.findall('\(([^)]+)', params) ]
    header = ''
    for p in params_list:
        header += p + ' '
    return '(lemma ' + header[:-1] + ')'

# replace arguments of all instances of any function in replace_fcts
def replaceArgs(lemma, replace_fcts):
    if lemma.children() == [] or replace_fcts == {}:
        return lemma
    elif lemma.decl() in replace_fcts:
        arg0 = replaceArgs(lemma.arg(0), replace_fcts)
        arg1 = replaceArgs(lemma.arg(1), replace_fcts)
        return replace_fcts[lemma.decl()](arg0, arg1)
    else:
        new_args = []
        for i in range(len(lemma.children())):
            new_arg = replaceArgs(lemma.arg(i), replace_fcts)
            new_args += [ new_arg ]
        return lemma.decl()(new_args)

# swap arguments of all instances of any function in swap_fcts
def swapArgs(lemma, swap_fcts):
    if lemma.children() == [] or swap_fcts == {}:
        return lemma
    elif lemma.decl() in swap_fcts:
        arg0 = swapArgs(lemma.arg(0), swap_fcts)
        arg1 = swapArgs(lemma.arg(1), swap_fcts)
        return swap_fcts[lemma.decl()](arg1, arg0)
    else:
        new_args = []
        for i in range(len(lemma.children())):
            new_arg = swapArgs(lemma.arg(i), swap_fcts)
            new_args += [ new_arg ]
        return lemma.decl()(new_args)

# translate output of cvc4 into z3py form
# TODO: abstract this out as general function, not specific to each input
def translateLemma(lemma, fcts_z3, addl_decls = {}, swap_fcts = {}, replace_fcts = {}):
    const_decls = '(declare-const fresh Int)' # exactly one free variable assumed
    header = getLemmaHeader(lemma).replace('x', 'fresh')
    assertion = '(assert ' + header + ')'
    smt_string = const_decls + '\n' + lemma + '\n' + assertion
    z3_str = extractDecls(fcts_z3)
    z3_str.update(addl_decls)
    z3py_lemma = parse_smt2_string(smt_string, decls=z3_str)[0]
    z3py_lemma_replaced = replaceArgs(z3py_lemma, replace_fcts)
    z3py_lemma_fixed = swapArgs(z3py_lemma_replaced, swap_fcts)
    print('proposed lemma: ' + str(z3py_lemma_fixed))
    return z3py_lemma_fixed

# Given the name of a recursive predicate/function name and a list of unfolded recdefs
# Returns the function object corresponding to the name
def getUnfoldRecdefFct(recdef_name, unfold_recdefs_dict):
    # unfolding function objects have the name 'u' + <recdef-name> + '_z3'/'_python'
    for key in unfold_recdefs_dict.keys():
        for fct in unfold_recdefs_dict[key]:
            func_name = fct.__name__
            if func_name.startswith('u' + recdef_name):
                return fct
    # Default case. Recdef not found. Return none.
    return None

def substituteSubformula(expression, substitution_pairs):
    # Recursively substitute subformulae bottom up
    # The first substitution matching the operator's name is applied
    declaration = expression.decl()
    args = expression.children()
    arity = len(args)
    if arity == 1:
        arg = args[0]
        substituted_args = substituteSubformula(arg, substitution_pairs)
    else:
        substituted_args = tuple([substituteSubformula(arg, substitution_pairs) for arg in args])

    for substitution_pair in substitution_pairs:
        (decl_name, substitution_lambda) = substitution_pair
        declaration_name = getZ3FctName(declaration)
        if decl_name == declaration_name:
            new_expression = substitution_lambda(declaration,substituted_args)
            return new_expression
    # Default case. None of the substitutions apply. Return the original declaration with substituted args
    if arity == 1:
        return declaration(substituted_args)
    else:
        return declaration(*substituted_args)

####################
# Support for sorts. Particularly used for background sorts

# Given the name of a primitive sort as a string, returns the appropriate sort
# Must add support for set types as well
def getSortFromName(sort_name):
    if sort_name == 'int':
        return IntSort()
    elif sort_name == 'bool':
        return BoolSort()
    else:
        return ValueError('Sort name not supported in current conversion scheme')

# Creates a z3py variable with the given name and sort
# Z3Py already provides an API for this. If it stops being there or doesn't work for some sorts, might have to replace this
def createSortVar(name, sort):
    return Const(name, sort)

# Returns the bottom element of the corresponding lattice in order to enable fixpoint computation
# The returned value is a native python value that will be used to populate elements in the true models, which are themseleves python dictionaries
def getBottomElement(key):
    ret_type = getFctSignature(key)[2]
    if ret_type == 'bool':
        return False
    elif ret_type == 'int':
        # UNDESIRABLE: this path will only be triggered by length predicates currently, which are always non-negative so using -1 as a bottom element is ok
        # TODO: must fix this by distinguishing sorts
        return -1
    elif ret_type == 'set-int':
        return set()
    else:
        raise ValueError('Sort name' + ret_type + 'is not supported')

def convertZ3ValueTypetoPython(value):
    if isinstance(value, BoolRef):
        return bool(value)
    elif isinstance(value, IntNumRef):
        # NOTE: returns a bignum
        return value.as_long()
    elif isinstance(value, ArrayRef):
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
