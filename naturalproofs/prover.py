# This module is the main module of the naturalproofs package. It defines a natural proofs solver and various
# configuration options, as well as the structure that the solver returns.

import z3

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.decl_api import get_recursive_definition, get_all_axioms
import naturalproofs.proveroptions as proveroptions
from naturalproofs.prover_utils import make_recdef_unfoldings, get_foreground_terms, instantiate


class NPSolution:
    """
    Class for representing solutions discovered by NPSolver instances.  
    Such a representation is necessary because logging information can be attached to the NPSolution object, along with
    default outputs like a satisfying model.  
    """
    def __init__(self, if_sat=None, model=None, fg_terms=None, depth=None, options=None):
        """
        Explanation of attributes:  
        - if_sat (bool): if there exists a satisfying model under the given configuration.  
        - model (z3.ModelRef or None): satisfying model if exists.  
        - fg_terms (set of z3.ExprRef): logging attribute. Set of foreground terms in the formula given to the smt
                                        solver. A finite model can be extracted over these terms that preserves
                                        satisfiablity/unsatisfiability.  
        - depth (int): depth at which the solution object was created. Applicable when instantiation mode is bounded depth.  
        - options (proveroptions.Options): logging attribute. Options used to configure the solver.  
        """
        self.if_sat = if_sat
        self.model = model
        self.fg_terms = fg_terms
        self.depth = depth
        self.options = options


class NPSolver:
    """
    Class for creating Natural Proofs solvers.  
    Can be configured using the 'options' attribute, an instance of the naturalproofs.Options class.  
    """
    def __init__(self, annctx=default_annctx):
        """
        Each solver instance must be created with an AnnotatedContext that stores the vocabulary, recursive definitions,
         and axioms --- essentially defining a theory for the solver.  
        :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext  
        """
        self.annctx = annctx
        self.options = proveroptions.Options()

    def solve(self, goal, lemmas=None):
        """
        Primary function of the NPSolver class. Attempts to prove the goal with respect to given lemmas and the theory
        defined by the AnnotatedContext in self.annctx.  
        :param goal: z3.BoolRef  
        :param lemmas: set of z3.BoolRef  
        :return: NPSolution  
        """
        # TODO: check that the given lemmas are legitimate bound formula instances with their formal parameters from
        #  the foreground sort.
        options = self.options
        # Make recursive definition unfoldings
        recdefs = get_recursive_definition(None, alldefs=True, annctx=self.annctx)
        recdef_unfoldings = make_recdef_unfoldings(recdefs)
        # Add them to the set of axioms and lemmas to instantiate
        axioms = get_all_axioms(self.annctx)
        fo_abstractions = axioms | recdef_unfoldings | (lemmas if lemmas is not None else set())
        # Negate the goal
        neg_goal = z3.Not(goal)
        # Create a solver object and add the goal negation to it
        z3solver = z3.Solver()
        z3solver.add(neg_goal)
        # Keep track of terms in the quantifier-free problem given to the solver
        terms = get_foreground_terms(neg_goal, annctx=self.annctx)
        # Instantiate and check for provability according to options
        # Handle manual instantiation mode first
        if options.instantiation_mode == proveroptions.manual_instantiation:
            terms_for_instantiation = options.terms_to_instantiate
            instantiations = instantiate(fo_abstractions, terms_for_instantiation)
            z3solver.add(instantiations)
            if_sat = _solver_check(z3solver)
            model = z3solver.model() if if_sat else None
            terms = get_foreground_terms(instantiations, annctx=self.annctx)
            return NPSolution(if_sat=if_sat, model=model, fg_terms=terms, options=options)
        # Automatic instantiation modes
        # Set up initial values of variables
        depth_counter = 0
        # Keep track of formulae produced by instantiation
        instantiations = set()
        target_depth = -1 if options.instantiation_mode == proveroptions.infinite_depth else options.depth
        while depth_counter < target_depth:
            # Try to prove with available instantiations
            z3solver.add(instantiations)
            if_continue = _solver_check(z3solver) if options.instantiation_mode == proveroptions.bounded_depth else True
            if not if_continue:
                # bounded_depth mode and Unsat achieved at this depth
                return NPSolution(if_sat=if_continue, fg_terms=terms, depth=depth_counter, options=options)
            else:
                # bounded_depth mode with sat or fixed_depth mode with target depth not reached.
                # Do another round of instantiations.
                instantiations = instantiate(fo_abstractions, terms)
                depth_counter = depth_counter + 1
                terms = get_foreground_terms(instantiations, annctx=self.annctx)
        # Reach this case when depth_counter = target depth, either in fixed_depth or bounded_depth mode.
        # Final attempt at proving goal
        z3solver.add(instantiations)
        if_sat = _solver_check(z3solver)
        model = z3solver.model() if if_sat else None
        return NPSolution(if_sat=if_sat, model=model, fg_terms=terms, depth=depth_counter, options=options)


# Helper function to check the satisfiability and throw exception if solver returns unknown
def _solver_check(z3solver):
    z3solution = z3solver.check()
    if z3solution == z3.sat:
        return True
    elif z3solution == z3.unsat:
        return False
    elif z3solution == z3.unknown:
        raise ValueError('Solver returned unknown. Something is wrong. Exiting.')
