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
    def __init__(self, if_sat=None, model=None, extraction_terms=None, instantiation_terms=None, depth=None, options=None):
        """
        Explanation of attributes:  
        - if_sat (bool): if there exists a satisfying model under the given configuration.  
        - model (z3.ModelRef or None): satisfying model if exists.  
        - extraction_terms (set of z3.ExprRef): logging attribute. Set of foreground terms in the formula 
        given to the smt solver. A finite model can be extracted over these terms that preserves the failure of 
        the proof attempt. Usually this is the set of all foreground terms in the quantifier-free formula given 
        to the solver at the end of all instantiations.  
        - instantiation_terms: the set of terms that were used for instantiating all axioms and recursive 
        definitions. Only applicable when the instantiation is uniform for all axioms. Not applicable when 
        instantiation mode is depth_one_untracked_lemma_instantiation.  
        - depth (int): depth at which the solution object was created. Applicable when instantiation mode is 
        bounded depth.  
        - options (proveroptions.Options): logging attribute. Options used to configure the solver.  
        """
        self.if_sat = if_sat
        self.model = model
        self.extraction_terms = extraction_terms
        self.instantiation_terms = instantiation_terms
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
        if lemmas is None:
            lemmas = set()
        fo_abstractions = axioms | recdef_unfoldings | lemmas
        # Negate the goal
        neg_goal = z3.Not(goal)
        # Create a solver object and add the goal negation to it
        z3solver = z3.Solver()
        z3solver.add(neg_goal)
        # Keep track of terms in the quantifier-free problem given to the solver
        initial_terms = get_foreground_terms(neg_goal, annctx=self.annctx)
        extraction_terms = initial_terms
        instantiation_terms = set()
        # Instantiate and check for provability according to options
        # Handle manual instantiation mode first
        if options.instantiation_mode == proveroptions.manual_instantiation:
            terms_to_instantiate = options.terms_to_instantiate
            instantiations = instantiate(fo_abstractions, terms_to_instantiate)
            if instantiations != set():
                instantiation_terms = terms_to_instantiate
                extraction_terms = extraction_terms.union(get_foreground_terms(instantiations, annctx=self.annctx))
            z3solver.add(instantiations)
            if_sat = _solver_check(z3solver)
            model = z3solver.model() if if_sat else None
            return NPSolution(if_sat=if_sat, model=model, extraction_terms=extraction_terms, 
                              instantiation_terms=instantiation_terms, options=options)
        # Automatic instantiation modes
        # Untracked lemma instantiation strategy
        if options.instantiation_mode == proveroptions.depth_one_untracked_lemma_instantiation:
            conservative_fo_abstractions = axioms | recdef_unfoldings
            tracked_instantiations = instantiate(conservative_fo_abstractions, initial_terms)
            if tracked_instantiations != set():
                instantiation_terms = initial_terms
                tracked_terms = get_foreground_terms(tracked_instantiations, annctx=self.annctx)
                extraction_terms = extraction_terms.union(tracked_terms)
            z3solver.add(tracked_instantiations)
            untracked_instantiations = instantiate(lemmas, extraction_terms)
            if untracked_instantiations != set():
                instantiation_terms = instantiation_terms.union(extraction_terms)
                untracked_terms = get_foreground_terms(untracked_instantiations, annctx=self.annctx)
                extraction_terms = extraction_terms.union(untracked_terms)
            z3solver.add(untracked_instantiations)
            if_sat = _solver_check(z3solver)
            model = z3solver.model() if if_sat else None
            return NPSolution(if_sat=if_sat, model=model, extraction_terms=extraction_terms, 
                              instantiation_terms=instantiation_terms, options=options)
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
                return NPSolution(if_sat=if_continue, extraction_terms=extraction_terms, 
                                  instantiation_terms=instantiation_terms, depth=depth_counter, options=options)
            else:
                # bounded_depth mode with sat or fixed_depth mode with target depth not reached.
                # Do another round of instantiations.
                # TODO: optimise instantiations so repeated instantiation is not done. Currently all instantiations 
                #  are done in every round. But optimisation is difficult in the presence of multiple arities.
                instantiation_terms = extraction_terms
                instantiations = instantiate(fo_abstractions, instantiation_terms)
                if instantiations == set():
                    instantiation_terms = set()
                    break
                depth_counter = depth_counter + 1
                new_terms = get_foreground_terms(instantiations, annctx=self.annctx)
                extraction_terms = extraction_terms.union(new_terms)
        # Reach this case when depth_counter = target depth, either in fixed_depth or bounded_depth mode.
        # Final attempt at proving goal
        z3solver.add(instantiations)
        if_sat = _solver_check(z3solver)
        model = z3solver.model() if if_sat else None
        return NPSolution(if_sat=if_sat, model=model, extraction_terms=extraction_terms, 
                          instantiation_terms=instantiation_terms, depth=depth_counter, options=options)


# Helper function to check the satisfiability and throw exception if solver returns unknown
def _solver_check(z3solver):
    z3solution = z3solver.check()
    if z3solution == z3.sat:
        return True
    elif z3solution == z3.unsat:
        return False
    elif z3solution == z3.unknown:
        raise ValueError('Solver returned unknown. Something is wrong. Exiting.')
