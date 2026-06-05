# Sullivan_MM

A Python package for computations related to Sullivan models, minimal models, APL (Piecewise Linear) forms, Whitney forms, and Hodge theory on simplicial sets and complexes, likely built on top of SageMath.

## Installation

### Prerequisites

*   Python 3.x
*   [SageMath](https://www.sagemath.org/) (This package relies heavily on SageMath functionality)

Ensure SageMath is installed and its environment is active before installing `Sullivan_MM`.

You can run `pip` through Sage's shell (e.g., `sage -pip install ...`) or activate Sage's environment manually depending on your installation.

### Install inside the Sage environment

If you have Sage installed, and you want to make this package available for Sage, use the following command:

```bash
sage -pip install git+https://github.com/calquezar/sullivanmm.git
````
# Examples
After the installation, you can check that it works inside your sage session, for example, computing, the minimal model of the wedge of two sphere:

```python
sage: from Sullivan_MM import *
sage: S2 = simplicial_sets.Sphere(2)
sage: K = S2.wedge(S2)
sage: W = APLK(K)
sage: M = W.minimal_model(i=3)
sage: M.domain()
Commutative Differential Graded Algebra with generators ('x2_0', 'x2_1', 'y3_0', 'y3_1', 'y3_2') in degrees (2, 2, 3, 3, 3) over Rational Field with differential:
   x2_0 --> 0
   x2_1 --> 0
   y3_0 --> x2_0^2
   y3_1 --> x2_0*x2_1
   y3_2 --> x2_1^2
````

# Documentation
The complete documentation of the Sullvan Minimal Models package together with more examples is available at https://riemann.unizar.es/~calquezar/sullivan/index.html.
