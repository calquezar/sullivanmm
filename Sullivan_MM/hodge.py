r"""
The Combinatorial Laplacian and the Discrete Hodge Decomposition
for simplicial complexes, simplicial sets, Delta complexes and Cubical complexes.

The Algebraic Topological Model
=================================================

For such objects, this implementation uses the
method ``algebraic_topological_model`` available at SAGEMATH_. The specification of the method
for the case of a finite simplicial complex (see SS_, DC_ and CC_ for the implementation in other
simplicial structures) is the following:

.. _SAGEMATH: https://doc.sagemath.org/html/en/reference/topology/sage/topology/simplicial_complex.html#sage.topology.simplicial_complex.SimplicialComplex.algebraic_topological_model

    Algebraic topological model for this simplicial complex with
    coefficients in ``base_ring``.

    The term "algebraic topological model" is defined by Pilarczyk
    and Réal :cite:`pawereal2015`.

    INPUT:

    - ``base_ring`` -- coefficient ring (default: ``QQ``); must be a field

    Denote by :math:`C` the chain complex associated to this simplicial
    complex. The algebraic topological model is a chain complex
    :math:`M` with zero differential, with the same homology as :math:`C`,
    along with chain maps :math:`\pi: C \to M` and :math:`\iota: M \to C`
    satisfying :math:`\iota \circ \pi = 1_M` and :math:`\pi \circ \iota` chain homotopic
    to :math:`1_C`. The chain homotopy :math:`\phi` must satisfy

    - :math:`\phi \circ \phi = 0`,
    - :math:`\pi \circ \phi = 0`,
    - :math:`\phi \circ \iota = 0`.

    Such a chain homotopy is called a *chain contraction*.

    OUTPUT: a pair consisting of

    - chain contraction :math:`\phi` associated to :math:`C`, :math:`M`, :math:`\pi`, and
      :math:`\iota`
    - the chain complex :math:`M`

    Note that from the chain contraction :math:`\phi`, one can recover the
    chain maps :math:`\pi` and :math:`\iota` via ``phi.pi()`` and
    ``phi.iota()``. Then one can recover :math:`C` and :math:`M` from, for
    example, ``phi.pi().domain()`` and ``phi.pi().codomain()``,
    respectively.

An alternative definition for cochain complexes is given in :cite:`cheng2008transferring`:

    Given two cochain complexes :math:`C` and :math:`M`, a contraction :math:`(\pi, \iota, \phi)`
    from :math:`C` to :math:`M` consists of chain maps:

    .. math::

        \begin{array}{cc}
            \pi:& C \rightarrow M     ,\\
            \iota:& M \rightarrow C ,
        \end{array}

    and a chain homotopy

    .. math::

        \phi: C^{*} \rightarrow C^{*-1},

    such that

    .. math::

        \pi \circ \iota = \mathrm{1}_M

    and

    .. math::

        \iota \circ \pi - \mathrm{1}_C = d_C \circ \phi + \phi \circ d_C.

Such a chain homotopy provides a strong relation between the chain complexes :math:`C` and :math:`M`;
for example, their homology groups are isomorphic.


.. _def:combinatorial_laplacian:

The Combinatorial Laplacian and the Discrete Hodge Decomposition
=========================================================

This definitions come from :cite:`dodziuk1976finite,goldberg2002combinatorial`.

Let :math:`K` be a finite oriented simplicial complex, :math:`d \geq 0` be an
integer, and :math:`\partial_d: C_d(K) \rightarrow C_{d-1}(K)`, the `boundary operator`. Then,

    *Definition:* The :math:`d`-th *combinatorial Laplacian* is the linear operator
    :math:`\Delta_d : C_d \longrightarrow C_d` given by

    .. math::

        \Delta_d = \partial_{d+1} \circ \partial_{d+1}^* + \partial_d^* \circ \partial_d.

For convenience, we use the notations

.. math::
    \Delta_d^{\mathrm{up}} = \partial_{d+1} \circ \partial_{d+1}^*

and

.. math::

    \Delta_d^{\mathrm{down}} = \partial_d^* \circ \partial_d,

so that

.. math::

    \Delta_d = \Delta_d^{\mathrm{up}} + \Delta_d^{\mathrm{down}}.

Now, let :math:`B_{d}` be the adjacenty matrix of dimension `d` defined by the simplicial structure of `K`.

    The :math:`d`-th *Laplacian matrix* of :math:`K`, denoted :math:`L_d`, relative to some orderings of the
    standard bases for :math:`C_d` and :math:`C_{d-1}` of :math:`K`, is the matrix representation
    of :math:`\Delta_d`.

    Observe that

    .. math::

        L_d = B_{d+1} B_{d+1}^T + B_d^T B_d.

As above, for convenience, we use the notations

.. math::

    L_d^{\mathrm{up}} = B_{d+1} B_{d+1}^T

and

.. math::

    L_d^{\mathrm{down}} = B_d^T B_d,

so that

.. math::

    L_d = L_d^{\mathrm{up}} + L_d^{\mathrm{down}}.

Relation between the `AT-model` and the combinatorial laplacian
=========================================================

Let

.. math::
   :nowrap:

    \[
    \begin{array}{rcl}
        H_d & := & \ker{(L_d^{up})} \cap \ker{(L_d^{down})} \\
        E_d & := & \ker{(L_d^{up})} \cap \text{Im}({L_d^{down}}) \\
        C_d & := & \text{Im}({L_d^{up}}) \cap \ker{(L_d^{down})}
    \end{array}
    \]


It is easy to see that :math:`H_d = \ker{L_d}`. The fundamental theo of discrete Hodge theory states:

    For any finite simplicial complex :math:`K`, we have the orthogonal decomposition:

    .. math::

        C^k(K;\mathbb{K}) = H_d \oplus E_d \oplus C_d

    and

    .. math::
       :nowrap:

        \[
        \begin{array}{rcl}
            H_d & \perp &  E_d \\
            E_d & \perp & C_d \\
            C_d & \perp & H_d
        \end{array}
        \]


    Furthermore, :math:`\ker{(L_k)} \cong H^k(K; \mathbb{K})` via the natural projection.

Taking into account the `AT-model`:

    **Theorem:**

    .. math::
       :nowrap:

        \[
        \begin{array}{rcl}
            H_d & \cong & \text{Im}(\iota \circ \pi) \\
            E_d & \cong & \text{Im}{(d_C \circ \phi)}  \\
            C_d & \cong & \text{Im}{(\phi \circ d_C)}
        \end{array}
        \]

    and

    .. math::
       :nowrap:

        \[
        \begin{array}{rcl}
            \text{Im}(\iota \circ \pi) & \perp &  \text{Im}{(d_C \circ \phi)} \\
            \text{Im}{(d_C \circ \phi)} & \perp & \text{Im}{(\phi \circ d_C)} \\
            \text{Im}{(\phi \circ d_C)} & \perp & \text{Im}(\iota \circ \pi)
        \end{array}
        \]

    and

    .. math::

        C^k(K) =  \text{Im}(\iota \circ \pi) \oplus \text{Im}{(d_C \circ \phi)}  \oplus \text{Im}{(\phi \circ d_C)}

.. SEEALSO::

    - Finite simplicial complexes: SC_.

    - Simplicial sets: SS_.

    - Finite Delta-complexes: DC_.

    - Finite cubical complexes: CC_.

    .. _SC: https://doc.sagemath.org/html/en/reference/topology/sage/topology/simplicial_complex.html

    .. _SS: https://doc.sagemath.org/html/en/reference/topology/sage/topology/simplicial_set.html

    .. _DC: https://doc.sagemath.org/html/en/reference/topology/sage/topology/delta_complex.html

    .. _CC: https://doc.sagemath.org/html/en/reference/topology/sage/topology/cubical_complex.html


.. NOTE::

    References:

    - :cite:`dodziuk1976finite`

    - :cite:`dodziuk1976remark`

    - :cite:`duval2002shifted`

    - :cite:`friedberg1997linear`

    - :cite:`goldberg2002combinatorial`

    - :cite:`Torres_2020`

"""

from sage.structure.unique_representation import UniqueRepresentation, CachedRepresentation
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import matrix, zero_matrix, identity_matrix
from sage.modules.free_module import span
from sage.modules.free_module_element import vector, zero_vector
from sage.rings.rational_field import QQ
from collections import defaultdict


class Hodge(SageObject, UniqueRepresentation, CachedRepresentation):
    r"""
    This class implements the Combinatorial Laplacian and the Discrete Hodge Decomposition
    of the cochain complex of a simplicial structure. For such decomposition, this class makes use
    of the ``AT_model`` implementation  available at SAGEMATH.

    """

    def __init__(self, S, base_ring=QQ):
        r"""
        Initialization of "self".

        INPUT:

        - ``S`` -- a simplicial complex, simplicial set, delta complex or cubical complex.

        - ``base_ring`` -- the base ring of "self (default: QQ)

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: H
                The Discrete Hodge structure of Minimal triangulation of the 2-sphere over the base ring Rational Field

        """
        self.K = S
        self._base_ring = base_ring
        self.dimension = S.dimension()
        self._laplacians = {}
        self._harmonic_basis = {}
        self._exact_basis = {}
        self._coexact_basis = {}

    def _repr_(self):
        r"""
        Default method for string representation.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: H
                The Discrete Hodge structure of Minimal triangulation of the 2-sphere over the base ring Rational Field

        """
        return f"The Discrete Hodge structure of {self.K} over the base ring {self._base_ring}"

    def base_ring(self):
        r"""
        Return the base ring of "self".
        """
        return self._base_ring

    @cached_method(do_pickle=True)
    def boundary_operator(self, dim):
        r"""
        The differentials which make up the chain complex.

        INPUT:

        - ``dim`` -- element of the grading group (optional, default "None");


        OUTPUT:

        The differential starting in dimension ``dim`` as a sparse matrix.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: H.boundary_operator(1)
                [-1 -1 -1  0  0  0]
                [ 1  0  0 -1 -1  0]
                [ 0  1  0  1  0 -1]
                [ 0  0  1  0  1  1]
                sage: H.boundary_operator(1) == K.chain_complex().differential(1)
                True

        """
        ch = self.K.chain_complex(base_ring=self._base_ring)
        return ch.differential(dim).sparse_matrix()

    @cached_method(do_pickle=True)
    def coboundary_operator(self, dim):
        r"""
        The differentials which make up the cochain complex.

        INPUT:

        - ``dim`` -- element of the grading group (optional, default "None");


        OUTPUT:

        The differential starting in dimension ``dim`` as a sparse matrix.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: H
                The Discrete Hodge structure of Minimal triangulation of the 2-sphere over the base ring Rational Field
                sage: H.coboundary_operator(1)
                [ 1 -1  0  1  0  0]
                [ 1  0 -1  0  1  0]
                [ 0  1 -1  0  0  1]
                [ 0  0  0  1 -1  1]
                sage: H.coboundary_operator(1) == K.chain_complex().dual().differential(1)
                True

        """
        ch = self.K.chain_complex(base_ring=self._base_ring).dual()
        return ch.differential(dim).sparse_matrix()

    @cached_method(do_pickle=True)
    def coexact_basis(self, d):
        r"""
        The basis of the coexact (non-closed) cochain subspace of :math:`C^d(K)`.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: H.coexact_basis(1)
                [(1, 0, -1, 0, 1, 0), (0, 1, -1, 0, 0, 1), (0, 0, 0, 1, -1, 1)]

        """
        if (d in self._coexact_basis):
            return self._coexact_basis[d]
        else:
            coexact_matrix = self.coexact_matrix(d)
            self._coexact_basis[d] = coexact_matrix.rows()
            return self._coexact_basis[d]

    @cached_method(do_pickle=True)
    def coexact_matrix(self, d):
        r"""
        The coexact (non-closed) cochain subspace of :math:`C^d(K)` as a sparse matrix
        with rows the basis of the vector subspace.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: H.coexact_basis(1)
                [(1, 0, -1, 0, 1, 0), (0, 1, -1, 0, 0, 1), (0, 0, 0, 1, -1, 1)]
                sage: H.coexact_matrix(1)
                [ 1  0 -1  0  1  0]
                [ 0  1 -1  0  0  1]
                [ 0  0  0  1 -1  1]

        """

        if (d in self._coexact_basis):
            basis = self.coexact_basis(d)
            if len(basis):
                return matrix(self._base_ring, len(basis), basis, sparse=True).echelon_form().sparse_matrix()
            else:
                ncells = len(self.K.n_cells(d))
                return zero_matrix(self._base_ring, 0, ncells)
        elif (d == self.K.dimension()):
            ncells = len(self.K.n_cells(d))
            return zero_matrix(self._base_ring, 0, ncells)
        else:
            # dif_matrix = self.coboundary_operator(d)
            # if (not dif_matrix):
            #     ncells = len(self.K.n_cells(d))
            #     return zero_matrix(self._base_ring, 0, ncells)
            (phi, M) = self.K.algebraic_topological_model()
            #phi_matrix = phi.in_degree(d).sparse_matrix()
            #coexacts = (phi_matrix * dif_matrix).column_space().matrix().sparse_matrix()
            coexacts = phi.in_degree(d).row_space().matrix().sparse_matrix()
            return coexacts

            """
            harmonic_basis = self.harmonic_basis(d)
            if len(harmonic_basis):
                complement_matrix = span(
                    harmonic_basis).complement().basis_matrix().sparse_matrix()
            else:
                complement_matrix = identity_matrix(self._base_ring, 
                                    len(self.K.n_cells(d)), sparse=True)
            coex_mat = ((complement_matrix * dif.T) *
                        dif).row_space().basis_matrix().sparse_matrix()
            return coex_mat.echelon_form().sparse_matrix()
            """

    @cached_method(do_pickle=True)
    def exact_basis(self, d):
        r"""
        The basis of the exact cochain subspace of :math:`C^d(K)`.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_sets.Torus()
                sage: H = Hodge(K)
                sage: H.harmonic_basis(1)
                [
                (1, 0, 1),
                (0, 1, 1)
                ]
                sage: H.exact_basis(1)
                []
                sage: H.coexact_basis(1)
                [(1, 1, -1)]

        """

        # (phi,M) = K.algebraic_topological_model()
        #sage: d1 = ch.differential(1)
        #sage: d1*phi.dual().in_degree(2)
        if (d in self._exact_basis):
            return self._exact_basis[d]
        else:
            if (d == 0):
                ncells = len(self.K.n_cells(d))
                basis = [zero_vector(self._base_ring, ncells)]
            else:
                basis = self.exact_matrix(d).rows()
                """
                coexact_matrix_prev = self.coexact_matrix((d - 1))
                d_prev = self.coboundary_operator((d - 1))
                exact_matrix = (coexact_matrix_prev * d_prev.T)
                basis = exact_matrix.echelon_form().sparse_matrix().rows()
                """
            self._exact_basis[d] = basis
            return basis

    @cached_method(do_pickle=True)
    def exact_matrix(self, d):
        r"""
        The exact cochain subspace of :math:`C^d(K)` as a sparse matrix
        with rows the basis of the vector subspace.

        .. tab:: Sage

            EXAMPLES::

                sage: K = delta_complexes.KleinBottle()
                sage: H = Hodge(K)
                sage: [H2,E2,C2] = H.hodge_decomposition(2)
                sage: H2
                [0 0]
                sage: E2
                [ 1  1]
                [ 1 -1]
                sage: C2
                []
                sage: K.dimension()
                2
                sage: [H1,E1,C1] = H.hodge_decomposition(1)
                sage: H1
                [0 0 1]
                sage: E1
                []
                sage: C1
                [1 0 0]
                [0 1 0]
                sage: d1 = H.coboundary_operator(1)
                sage: (d1*C1.T).T == E2
                True

        .. tab:: Raw code

            EXAMPLES::

                K = delta_complexes.KleinBottle()
                H = Hodge(K)
                [H2,E2,C2] = H.hodge_decomposition(2)
                print("K.dimension()")
                [H1,E1,C1] = H.hodge_decomposition(1)
                d1 = H.coboundary_operator(1)
                print((d1*C1.T).T == E2)
        """


        dif_matrix = self.coboundary_operator(d-1)
        if (not dif_matrix):
            ncells = len(self.K.n_cells(d))
            return zero_matrix(self._base_ring, 0, ncells)
        """
        (phi, M) = self.K.algebraic_topological_model()
        phi_matrix = phi.dual().in_degree(d).sparse_matrix()
        exacts = (dif_matrix * phi_matrix).column_space().matrix().sparse_matrix()
        return exacts
        """

        C = self.coexact_matrix(d-1)
        return C*(dif_matrix.T) # actually, (dif_matrix * C.T).T but in this way we save a transposition

        """
        basis = self.exact_basis(d)
        if len(basis):
            return matrix(self._base_ring, len(basis), basis, sparse=True).echelon_form().sparse_matrix()
        else:
            ncells = len(self.K.n_cells(d))
            return zero_matrix(self._base_ring, 1, ncells)
        """

    @cached_method(do_pickle=True)
    def harmonic_basis(self, d):
        r"""
        The basis of the harmonic cochain subspace of :math:`C^d(K)`.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_sets.Torus()
                sage: H = Hodge(K)
                sage: H.harmonic_basis(1)
                [
                (1, 0, 1),
                (0, 1, 1)
                ]
                sage: H.exact_basis(1)
                []
                sage: H.coexact_basis(1)
                [(1, 1, -1)]

        """
        if (d in self._harmonic_basis):
            return self._harmonic_basis[d]
        else:
            (phi, M) = self.K.algebraic_topological_model()
            mat = (phi.iota().in_degree(d).sparse_matrix()
                   * phi.pi().in_degree(d).sparse_matrix())
            basis = mat.row_space().basis()
            self._harmonic_basis[d] = basis
            return basis

    @cached_method(do_pickle=True)
    def harmonic_matrix(self, d):
        r"""
        The harmonic cochain subspace of :math:`C^d(K)` as a sparse matrix
        with rows the basis of the vector subspace.

        .. tab:: Sage

            EXAMPLES::

                sage: K = simplicial_sets.Torus()
                sage: H = Hodge(K)
                sage: H.harmonic_matrix(1)
                [1 0 1]
                [0 1 1]
                sage: H.exact_matrix(1)
                [0 0 0]
                sage: H.coexact_matrix(1)
                [ 1  1 -1]

        """
        basis = self.harmonic_basis(d)
        if len(basis):
            return matrix(self._base_ring, len(basis), basis, sparse=True)
        else:
            ncells = len(self.K.n_cells(d))
            return zero_matrix(self._base_ring, 1, ncells)

    def hodge_cochain_decomposition(self, cochain, degree):
        r"""
        Returns the hodge decomposition of the cochain `c` as a sum of three components

        .. math::

            cochain = h + e + c

        where `h` is the harmonic component, `e` is the exact component and `c` is the coexact component.

        INPUT:

        - ``cochain`` -- a cochain of :math:`C^d(K)` represented as a vector over the base ring.

        - ``degree`` -- the degree of the cochain.

        OUTPUT: a tuple `(h,e,c)` of elements of :math:`C^d(K)`

        .. tab:: Sage

            EXAMPLES::

                sage: K = cubical_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: v = random_vector(QQ, len(K.n_cells(2)))
                sage: v
                (-1/15, 1, 1/449, 1/3, -2/5, 0)
                sage: (h,e,c) = H.hodge_cochain_decomposition(v,2)
                sage: v == h+c+e
                True
                sage: h
                (0, 0, 0, 0, 0, 4036/2245)
                sage: e
                (-1/15, 1, 1/449, 1/3, -2/5, -4036/2245)
                sage: c
                (0, 0, 0, 0, 0, 0)


        """
        [H, X, Y] = self.hodge_decomposition(degree)
        linear_system = H.stack(X.stack(Y)).T
        coords = linear_system.solve_right(cochain)
        hcoords = coords[:H.nrows()]
        xcoords = coords[H.nrows():(H.nrows() + X.nrows())]
        ycoords = coords[(- Y.nrows()):]
        if (hcoords and H.nrows()):
            harmonic = H.linear_combination_of_rows(hcoords)
        else:
            harmonic = zero_vector(self._base_ring, len(cochain))
        if (xcoords and X.nrows()):
            exact = X.linear_combination_of_rows(xcoords)
        else:
            exact = zero_vector(self._base_ring, len(cochain))
        if (ycoords and Y.nrows()):
            coexact = Y.linear_combination_of_rows(ycoords)
        else:
            coexact = zero_vector(self._base_ring, len(cochain))
        assert (harmonic in H.row_space())
        assert (exact in X.row_space())
        assert (coexact in Y.row_space())
        assert (((harmonic + exact) + coexact) == cochain)
        return (harmonic, exact, coexact)

    @cached_method(do_pickle=True)
    def hodge_decomposition(self, dim):
        r"""

        Returns the hodge decomposition of :math:`C^dim(K)`.

        INPUT:

        - ``dim`` -- the degree of the cochain module.

        OUTPUT: a tuple of matrices `(H,E,C)` corresponding with the harmonic, exact and coexact matrices.

        .. SEEALSO::

            :meth:`harmonic_matrix`

            :meth:`exact_matrix`

            :meth:`coexact_matrix`

        .. tab:: Sage

            EXAMPLES::

            The hodge decomposition of the simplicial cochain complex of the 2-Sphere at degree 2:

                sage: K = cubical_complexes.Sphere(2)
                sage: H = Hodge(K)
                sage: (H,E,C) = H.hodge_decomposition(2)
                sage: H
                [0 0 0 0 0 1]
                sage: E
                [ 1  0  0  0  0  1]
                [ 0  1  0  0  0 -1]
                [ 0  0  1  0  0  1]
                [ 0  0  0  1  0 -1]
                [ 0  0  0  0  1  1]
                sage: C
                []
                sage: len(K.n_cells(2))
                6

            (TO UPDATE) Example that ilustrates the orthogonality of the decomposition:

                sage: S2 = simplicial_sets.Sphere(2)
                sage: T = simplicial_sets.Torus()
                sage: K = S2.product(S2).product(T)
                sage: K
                S^2 x S^2 x Torus
                sage: W = APLK(K)
                sage: W
                Algebra of Whitney Forms on S^2 x S^2 x Torus
                sage: hodge = W.hodge()


        .. tab:: Raw code

            S2 = simplicial_sets.Sphere(2)
            T = simplicial_sets.Torus()
            K = S2.product(S2).product(T)
            ch = K.chain_complex(base_ring=QQ).dual()
            (phi,M) = K.algebraic_topological_model()
            d1 = ch.differential(1)
            d2 = ch.differential(2)
            C = phi.dual().in_degree(3)*d2
            E = d1*phi.dual().in_degree(2)
            H = phi.dual().iota().in_degree(2)*phi.dual().pi().in_degree(2)
            H*E == 0
            H*C == 0
            C*E == 0
            E*C == 0

        """
        H = self.harmonic_matrix(dim)
        X = self.exact_matrix(dim)
        Y = self.coexact_matrix(dim)
        return (H, X, Y)

    @cached_method(do_pickle=True)
    def laplacian(self, dim):
        r"""
        Returns the discrete laplacian of dimension ``dim``.

        INPUT:

        - ``dim`` -- the dimension of the cochain module.

        OUTPUT: a tuple of sparse matrices `(L, Ldown, Lup)` corresponding with the laplacian, the
        down laplacian and the up laplacian matrices.

        .. tab:: Sage

            EXAMPLES::

                sage: K = delta_complexes.KleinBottle()
                sage: K
                Delta complex with 1 vertex and 7 simplices
                sage: H = Hodge(K)
                sage: H
                The Discrete Hodge structure of Delta complex with 1 vertex and 7 simplices over the base ring Rational Field
                sage: (L, Ldown, Lup) = H.laplacian(1)
                sage: L
                [ 2  0  0]
                [ 0  2 -2]
                [ 0 -2  2]
                sage: Ldown
                [0 0 0]
                [0 0 0]
                [0 0 0]
                sage: Lup
                [ 2  0  0]
                [ 0  2 -2]
                [ 0 -2  2]
                sage: L.right_kernel().dimension() == len(H.harmonic_basis(1))
                True

        """
        if (dim in self._laplacians):
            return self._laplacians[dim]
        else:
            d_curr = self.coboundary_operator(dim)
            d_prev = self.coboundary_operator((dim - 1))
            L_down = (d_prev * d_prev.T)
            L_up = (d_curr.T * d_curr)
            L = (L_down + L_up)
            self._laplacians[dim] = (L, L_down, L_up)
            return (L, L_down, L_up)

    def preimage(self, cochain, degree):
        r"""
        Returns the coexact cochain of ``degree-1`` whose differential correspond with the
        exact component of the given cochain.

        INPUT:

        - ``cochain`` -- a cochain vector

        - ``degree`` -- the degree of the cochain.

        OUTPUT: a cochain vector of degree ``degree-1`` whose differential corresponds with the exact component
        of the given cochain.

        .. tab:: Sage

            EXAMPLES::

                sage: S2 = simplicial_sets.Sphere(2)
                sage: K = S2.product(S2)
                sage: H = Hodge(K)
                sage: H
                The Discrete Hodge structure of S^2 x S^2 over the base ring Rational Field
                sage: v = random_vector(QQ, len(K.n_cells(3)))
                sage: (h,e,c) = H.hodge_cochain_decomposition(v,3)
                sage: h
                (0, 0, 0, 0, 0, 0)
                sage: e
                (1/12, 0, 1/12, -1/12, 0, -1/12)
                sage: c
                (-1/12, -2, 1/4, 1/12, -1/6, 1/12)
                sage: y = H.preimage(v,3)
                sage: dif = K.chain_complex(base_ring=QQ).dual().differential(2)
                sage: dif*y == e
                True

        """
        if (degree == 0):
            raise ValueError(
                'Cannot compute preimage for 0-cochains (no d_{-1})')
        d_prev = self.coboundary_operator((degree - 1))
        ker_matrix = d_prev.T.right_kernel_matrix()
        M = d_prev.T.stack(ker_matrix)
        preimage = M.T.solve_right(cochain)
        return preimage[:len(self.K.n_cells((degree - 1)))]

if (__name__ == '__main__'):
    None
