# This module defines an options class that will be used to configure a natural proofs solver.


class Options:
    """
    Class for options and default values to configure a natural proofs solver.  
    Explanation of options:  
    - instantiation_mode: generic instantiation config given as a defined constant  
    --- fixed_depth: instantiate for 'depth' number of rounds  
    --- bounded_depth: instantiate until 'depth' number of rounds, checking each time for provability  
    --- infinite_depth: start at depth=1 and proceed to increase depth until proven  
    --- manual_instantiation: specify what terms to instantiate with separately using the 'terms_to_instantiate' option  
    - depth: number of rounds for which quantifier instantiation is performed  
    - terms_to_instantiate: when mode=manual, use only this set of terms to do instantiations  
    """
    def __init__(self):
        self.instantiation_mode = fixed_depth
        self.depth = 1
        self.terms_to_instantiate = None


# Defined constants for options
# instantiation_mode
fixed_depth = 0
bounded_depth = 1
infinite_depth = 2
manual_instantiation = 3
