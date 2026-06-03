# Sullivan_MM/__init__.py

"""
Sullivan Minimal Models (Sullivan_MM) Module.

This module provides tools for working with discrete Hodge complexes,
piecewise-linear differential forms (A_PL), simplicial objects based on A_PL,
cochain algebras over simplicial complexes, and Whitney forms complexes,
primarily intended for computations related to Sullivan minimal models in
rational homotopy theory.

Primary Classes/Objects:
- AplN: Commutative Differential Graded Algebra A_PL(n).
- SimplicialAPL: Simplicial object of A_PL(n) algebras.
- DiscreteHodgeComplex: Discrete Hodge decomposition for simplicial complexes.
- CochainAlgebraSComplex: Cochain algebra associated with a simplicial complex.
- WhitneyFormsComplex: Whitney forms complex associated with a simplicial complex.

Dependencies:
- SageMath (sage)
"""

# Import key components from each submodule
# Adjust class/function names as needed based on the actual public API
# These imports make the classes/functions directly available when importing Sullivan_MM


from .AlgebraPL import AplN

from .SimplicialAPL import SimplicialAPL

from .hodge import Hodge

from .utils import *

from .cochain_algebra_scomplex import CochainAlgebraComplex, CochainAlgebraElementComplex, MorphismFromQQToCA

from .cochain_algebra_scomplex import MinimalModel as MMCA

from .AplK import APLK, APLKElement, MorphismFromQQToAPLK, CohomologyClass

from .AplK import MinimalModel as MMWC


