r"""
The cochain algebra :math:`A_{PL}(K)`.
Let :math:`K` be a simplicial set, and let :math:`A_{PL} = \{(A_{PL})_n\}_{n \geq 0}` be the simplicial cochain
algebra defined at :ref:`simplicialapl`

.. math::

    A_{PL}(K) = \bigoplus_{p \geq 0}A_{PL}^p(K)

is the cochain algebra defined as follows:

* The homogenous part :math:`A_{PL}^p(K)` is the set of simplicial set morphisms from :math:`K` to :math:`A_{PL}^p`.
  That is, an element :math:`\Phi \in A_{PL}^p(K)` is a mapping that assigns to each :math:`n`-simplex :math:`\sigma \in K_n`,
  an element :math:`\Phi(\sigma) \in (A_{PL}^p)_n`, satisfying

  .. math::

      \begin{array}{c}
          \Phi({\partial_i(\sigma)})=\partial_i(\Phi(\sigma)) \\
          \Phi({s_j(\sigma)})=s_j(\Phi(\sigma))
      \end{array}

* Addition, scalar multiplication, product and the differential are induced by the corresponding operations
  in the algebras :math:`(A_{PL})_n`.

The structure of the cochain algebra :math:`A_{PL}(K)`, at some general dimension :math:`n` and degree :math:`p`,
can be visualized in figure :ref:`fig:simplicial_aplK`. The horizontal direction corresponds to the simplicial
structure for a given dimension :math:`n` (subscript), and the vertical direction corresponds to the graded structure
of the algebra (representing the degree :math:`p` with superscript). As the simplicial cochain algebra :math:`(A_{PL})_n` is at
the ground of this structure, all the elements of :math:`A^p_{PL}(K)_n` will vanish when :math:`p>n`. This is because it is not
possible to assign non-zero polynomial forms of degree greater than the dimension of the simplices.

.. image:: /_static/aplktkzcd.svg
   :align: center
   :class: only-light
   :alt: The structure of the cochain algebra :math:`A_{PL}(K)`.

.. image:: /_static/aplktkzcdneg.svg
   :align: center
   :class: only-dark
   :alt: The structure of the cochain algebra :math:`A_{PL}(K)`.

.. raw:: latex

    \begin{figure}[H]
    \centering
    \begin{tikzcd}
    & \vdots \arrow[d, "d^{p-2}_A"] & \vdots \arrow[d, "d^{p-2}_A"] & \vdots \arrow[d, "d^{p-2}_A"]& \\
    \cdots & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] A^{p-1}_{PL}(K)_{n-1} \arrow[d, "d^{p-1}_A"] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] A^{p-1}_{PL}(K)_{n}  \arrow[d, "d^{p-1}_A"] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above]  A^{p-1}_{PL}(K)_{n+1} \arrow[d, "d^{p-1}_A"] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] \cdots \\
    \cdots & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] A^{p}_{PL}(K)_{n-1} \arrow[d, "d^{p}_A"] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] A^{p}_{PL}(K)_{n}  \arrow[d, "d^{p}_A"] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] A^{p}_{PL}(K)_{n+1} \arrow[d, "d^{p}_A"] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] \cdots \\
    \cdots & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] A^{p+1}_{PL}(K)_{n-1} \arrow[d, "d^{p+1}_A"] & A^{p+1}_{PL}(K)_{n} \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] \arrow[d, "d^{p+1}_A"] & A^{p+1}_{PL}(K)_{n+1} \arrow[d, "d^{p+1}_A"] \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] & \arrow[l, "\vdots" above, shift left=2]  \arrow[l, shift right=3,"\partial_i" above] \cdots \\
    & \vdots  & \vdots & \vdots &
    \end{tikzcd}
    \caption{The structure of the cochain algebra $A_{PL}(K)$.}
    \label{simplicial_aplK}
    \end{figure}

"""

from sage.structure.unique_representation import UniqueRepresentation, CachedRepresentation
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.sage_object import SageObject
from sage.categories.morphism import Morphism
from sage.all import *
from sage.structure.parent import Parent
from sage.structure.element import Element
from sage.rings.rational_field import QQ
from sage.matrix.constructor import vector, matrix, zero_matrix, identity_matrix
from collections import defaultdict
from itertools import combinations
from sage.arith.misc import multinomial
from sage.combinat.set_partition_ordered import OrderedSetPartitions
from sage.structure.richcmp import rich_to_bool, op_EQ, op_NE, op_LT, op_LE, op_GT, op_GE
from sage.algebras.commutative_dga import sorting_keys
import copy
from copy import deepcopy
from .hodge import Hodge
from .SimplicialAPL import SimplicialAPL
from . import utils
from .utils import sgn_face, sgn_perm


class APLK(Parent, UniqueRepresentation, CachedRepresentation):

    def __init__(self, K, base_ring=QQ, precompute_degree=None):
        if ((not hasattr(K, 'n_cells')) or (not hasattr(K, 'face')) or (not hasattr(K, 'dimension'))):
            raise TypeError(
                'K must be a simplicial complex with n_cells(), face(), and dimension() methods')
        self.K = K
        self._base_ring = base_ring
        self._dimension = K.dimension()
        self._gens = {}
        self._coboundaries = {}
        self._cocycles = {}
        self._cohomology_raw = {}
        self._cohomology = {}
        self._cohomology_mmodels = {}
        self._cohomology_raw_mmodels = {}
        self._minimalmodels = {}
        self._numerical_invariants = {}
        self._ch_vector = ()

        self._apl_algebras = SimplicialAPL(self._dimension)

        Parent.__init__(self, base=QQ)
        f = MorphismFromQQToAPLK(self)
        self.register_coercion(f)
        self._gens = {'hodge': {}, 'whitney': {}}
        for d in range((K.dimension() + 1)):
            self._gens['hodge'][d] = {
                'harmonics': {}, 'exacts': {}, 'coexacts': {}}
            self._gens['whitney'][d] = {
                'harmonics': {}, 'exacts': {}, 'coexacts': {}}
        self._hodge = Hodge(K)
        self._hodge_matrix_decompositions = {}
        if precompute_degree:
            print('Precomputing hodge decomposition up to degree',
                  precomp_hodge_deg, flush=True)
            self._hodge_matrix_decompositions = self.hodge_matrix_decompositions(
                precomp_hodge_deg)

    def _check_compatibility(self, components):
        K = self.K
        SApl = self._apl_algebras
        face_map = self._face_homomorphism()
        for dim in range(1, (self._dimension + 1)):
            cells = self.K._n_cells_sorted(dim)
            A = SApl.n_th_object(dim)
            for (sigma_idx, sigma) in enumerate(cells):
                f_sigma = components.get(sigma, A.zero())
                if f_sigma.is_zero():
                    continue
                for i in range((dim + 1)):
                    tau = K.face(sigma, i)
                    #tau_dim = (dim - 1)
                    f_tau_expected = face_map(f_sigma, i)
                    f_tau_actual = components.get(tau, SApl.n_th_object(dim-1).zero())
                    if (not (f_tau_expected - f_tau_actual).reduce(0).is_zero()):
                        raise ValueError(
                            f'Face map compatibility failed for face {i} of {sigma}:\n  Expected: {f_tau_expected.reduce(0)}\n  Actual:   {f_tau_actual.reduce(0)}')

    def _cochain_to_vector(self, dim, cochain):
        cells = self.K._n_cells_sorted(dim)
        v = vector(QQ, len(cells), [cochain.get(sigma, 0) for sigma in cells])
        return v

    def _coface_coeff_endomorphism(self, faces, dim_from, dim_to):
        S = self._apl_algebras
        dom = S.n_th_object(dim_from).base_ring()
        cod = S.n_th_object(dim_to).base_ring()
        if (dim_from > dim_to):
            face_matrix = identity_matrix(cod, len(dom.gens()), sparse=True)
            face_matrix = face_matrix.delete_rows(faces).T
        else:
            face_matrix = identity_matrix(cod, len(cod.gens()), sparse=True)
            face_matrix = face_matrix.delete_rows(faces)
        codgens = vector(cod, cod.gens())
        image = list((face_matrix * codgens))
        return dom.hom(image, cod)

    def _degree_factorization(self, deg):
        return [(i, (deg - i)) for i in range(deg) if ((i <= (deg - i)) and (i > 0))]

    @cached_method(do_pickle=True)
    def _face_data(self, dim_from, dim_to):
        return utils._face_data(self.K, dim_from, dim_to, self._base_ring)

    def _face_homomorphism(self):
        if (dim == 0):
            raise ValueError(
                'Cannot compute face homomorphism for 0-simplices')
        return self._apl_algebras.face

    @cached_method(do_pickle=True)
    def _face_matrix(self, K, face, dim):
        return utils._face_matrix(K, dim, base_ring)

    def _gens_names_coexacts(self, d):
        return list(self.coexact_basis(d).keys())

    def _gens_names_exacts(self, d):
        return list(self.exact_basis(d).keys())

    def _gens_names_harmonics(self, d):
        return list(self.harmonic_basis(d).keys())

    @cached_method(do_pickle=True)
    def _get_basis(self, d, whitney_basis=True, subtype='harmonics', check=False):
        if whitney_basis:
            gensType = 'whitney'
        else:
            gensType = 'hodge'

        if (subtype == 'harmonics'):
            basis_func = self.harmonic_basis
            hodge_basis_func = self._hodge.harmonic_basis
            gLabel = 'h{}_{}'
        elif (subtype == 'exacts'):
            basis_func = self.exact_basis
            hodge_basis_func = self._hodge.exact_basis
            gLabel = 'e{}_{}'
        elif (subtype == 'coexacts'):
            basis_func = self.coexact_basis
            hodge_basis_func = self._hodge.coexact_basis
            gLabel = 'c{}_{}'
        if self._gens[gensType][d][subtype]:
            return self._gens[gensType][d][subtype]
        if (not whitney_basis):
            basis = hodge_basis_func(d)
            gens = {gLabel.format(d, i): h for (i, h) in enumerate(basis) if h}
        else:
            basis = basis_func(d, False, check)
            gens = {gname: self.whitney_form_from_vector(d, cochain, check) for (
                gname, cochain) in basis.items() if cochain}
        self._gens[gensType][d][subtype] = gens
        return gens

    def _get_cohomology_dimensions(self):
        dim = self._dimension
        co = self.K.cohomology(base_ring=QQ)
        return vector(QQ, [co[d].rank() for d in range((dim + 1))])

    def _get_coordinates(self, w):
        deg = w.degree()
        hodgeMats = self.hodge_decomposition(deg)
        (h, e, c) = w.hodge_cochain_decomposition()
        H = hodgeMats['H']
        if (not (H.nrows() == 0)):
            hCoords = H.T.solve_right(h)
        else:
            hCoords = zero_vector(QQ, H.ncols())
        X = hodgeMats['X']
        if (not (X.nrows() == 0)):
            xCoords = X.T.solve_right(e)
        else:
            xCoords = zero_vector(QQ, X.ncols())
        Y = hodgeMats['Y']
        if (not (Y.nrows() == 0)):
            yCoords = Y.T.solve_right(c)
        else:
            yCoords = zero_vector(QQ, Y.ncols())
        return {'harmonic_coords': hCoords, 'exact_coords': xCoords, 'coexact_coords': yCoords}

    @cached_method(do_pickle=True)
    def _hodge_matrix_decomposition(self, d, check=False, verbose=True):
        [H, X, Y] = self._hodge.hodge_decomposition(d)
        self._hodge_matrix_decompositions[d] = {'H': H, 'X': X, 'Y': Y}
        return self._hodge_matrix_decompositions[d]

    def _inject_subset_vars(self, func_basis, d=[], reload=True, verbose=True, check=False):
        def check_list_degs(degrees):
            if (not degrees):
                return range(1, (self._dimension + 1))
            elif (isinstance(degrees, tuple) or isinstance(degrees, list)):
                degs = degrees
            else:
                degs = [degrees]
            for d in degs:
                deg = int(d)
                if (deg < 0):
                    raise ValueError('max_degree must be a positive integer')
                if (deg not in ZZ):
                    raise ValueError('max_degree must be a positive integer')
                if (deg > self._dimension):
                    raise ValueError(
                        'max_degree must be lower or equal to the dimiension of self')
            return degs
        degrees = check_list_degs(d)
        gens = {}
        for deg in degrees:
            gens.update(func_basis(deg, check))
        return self._inject_variables(gens, verbose)

    def _inject_variables(self, gens, reload=True, verbose=True):
        from sage.repl.user_globals import set_global, get_globals
        for name in gens.keys():
            if ((not (name in get_globals().keys())) or reload):
                set_global(name, gens[name])
        if verbose:
            print('Defining {}'.format(', '.join(gens.keys())), flush=True)
        return None

    @cached_method(do_pickle=True)
    def _nonzero_product_faces(self, dim1, dim2):
        dim = (dim1 + dim2)
        cp = cartesian_product([list(combinations(
            range((dim + 1)), dim2)), list(combinations(range((dim + 1)), dim1))])
        return [c for c in cp if (not set(c[0]).intersection(set(c[1])))]

    def _pack_data(self):
        data = {}
        data['K'] = self.K
        self.gens(whitney_basis=True, verbose=True)
        self.gens(whitney_basis=False, verbose=True)
        data['gens'] = self._gens
        for n in range((self._dimension + 1)):
            self.coboundaries(n)
            self.cocycles(n)
            self.cohomology_raw(n)
            self.cohomology(n)
            self.hodge_matrix_decompositions(n)
        data['coboundaries'] = self._coboundaries
        data['cocycles'] = self._cocycles
        data['cohomology_raw'] = self._cohomology_raw
        data['cohomology'] = self._cohomology
        data['ch_vector'] = self._get_cohomology_dimensions()
        data['apl_algebras '] = self._apl_algebras
        data['hodge'] = self.hodge()
        data['hodge_matrix_decompositions'] = self._hodge_matrix_decompositions
        data['cohomology_mmodels'] = self._cohomology_mmodels
        data['minimalmodels'] = self._minimalmodels
        data['numerical_invariants'] = self._numerical_invariants
        return data

    def _repr_(self):
        return f'Algebra of Whitney Forms on {self.K}'

    def _vector_to_cochain(self, dim, v):
        cells = self.K._n_cells_sorted(dim)
        return {sigma: v[i] for (i, sigma) in enumerate(v)}

    def base_ring(self):
        return self._base_ring

    def basis(self, d):
        basis = []
        basis += list(self.harmonic_basis(d).values())
        basis += list(self.exact_basis(d).values())
        basis += list(self.coexact_basis(d).values())
        return basis

    def basis_ts(self, deg_y, deg_t):
        K = self.K
        b0 = self.basis(0)
        b2 = self.basis(deg_y)
        deg0_coefs = [prod(c) for c in cartesian_product((deg_t * [b0]))]
        b02 = [prod(c) for c in cartesian_product([deg0_coefs, b2])]
        rows = [g.terms_repr((deg_t + 1)) for g in b02]
        m = matrix(QQ, len(rows), rows, sparse=True)
        basis = m.row_space().basis()
        gens = [sum([(c * g) for (c, g) in zip(b, b02)]) for b in basis]
        return [g for g in gens if g]

    def ch_vector(self):
        if (not (len(self._ch_vector) == 0)):
            return self._ch_vector
        else:
            self._ch_vector = self._get_cohomology_dimensions()
        return self._ch_vector

    def coboundaries(self, n):
        if (n in self._coboundaries.keys()):
            return self._coboundaries[n]
        elif (n > self._dimension):
            return span(QQ, zero_vector(QQ, 0))
        basis = [v for v in self._hodge.coexact_basis(n) if v]
        F = self.base_ring()
        V = span(F, basis).span_of_basis(basis)
        self._coboundaries[n] = V
        return V

    # def m(self, cochains=[],dims=[]):
    #     dim = sum(dims)
    #     face_matrices = [self._face_data(dims[d], dim) for d in dims]
    #     ncells = len(self.K.n_cells(dim))
    #     w = vector(QQ, ncells)
    #     #product_faces = self._nonzero_product_faces(dim1, dim2)
    #     pathlengths = [dim-d for d in dims]
    #     product_faces = [[tuple(f) for f in path[1:]] for path
    #                      in OrderedSetPartitions(range(dim+1), [1]+ pathlengths)]
    #     #coef = ((factorial(dim1) * factorial(dim2)) / factorial((dim + 1)))
    #     coef = prod([factorial(d) for d in dims])/factorial(dim+1)
    #     for fpaths in product_faces:
    #         faces_orig_order = tuple(flatten(fpaths))
    #         sgn_prod = sgn_perm(faces_orig_order)
    #         propags = [face_matrices[i][fpaths[i]].T*c for (i, c) in enumerate(cochains)]
    #         v = propags[0]
    #         for i in range(1,len(propags)):
    #             v2 = propags[i]
    #             v = v.pairwise_product(v2)
    #         w += (sgn_prod * v)
    #     return (coef * w)

    def cochain_wedge_product(self, c1, dim1, c2, dim2):
        dim = (dim1 + dim2)
        face_data1 = self._face_data(dim1, dim)
        face_data2 = self._face_data(dim2, dim)
        w = vector(QQ, len(self.K.n_cells(dim)))
        product_faces = self._nonzero_product_faces(dim1, dim2)
        coef = ((factorial(dim1) * factorial(dim2)) / factorial((dim + 1)))
        #coef = 1/multinomial(dim1,dim2)
        for (f1, f2) in product_faces:
            faces_orig_order = (list(f1) + list(f2))
            sgn_prod = sgn_perm(faces_orig_order)
            f_matrix1 = face_data1[f1].T
            v1 = (f_matrix1 * c1)
            f_matrix2 = face_data2[f2].T
            v2 = (f_matrix2 * c2)
            v = v1.pairwise_product(v2)
            w += (sgn_prod * v)
        return (coef * w)

    def cocycles(self, n):
        if (n in self._cocycles.keys()):
            return self._cocycles[n]
        elif (n > self._dimension):
            return span(QQ, zero_vector(QQ, 0))
        H_basis = self._hodge.harmonic_basis(n)
        X_basis = self._hodge.exact_basis(n)
        basis = [v for v in (H_basis + X_basis) if v]
        F = self.base_ring()
        V = span(F, basis).span_of_basis(basis)
        self._cocycles[n] = V
        return V

    @cached_method(do_pickle=True)
    def coexact_basis(self, d, whitney_basis=True, check=False):
        gensSubtype = 'coexacts'
        return self._get_basis(d, whitney_basis, gensSubtype, check)

    def cohomology(self, n):
        if (n in self._cohomology.keys()):
            return self._cohomology[n]
        elif (n > self._dimension):
            return span(QQ, zero_vector(QQ, 0))
        H_basis = self.harmonic_basis(n)
        H_basis_brackets = [CohomologyClass(
            value, self) for (name, value) in H_basis.items()]
        self._cohomology[n] = CombinatorialFreeModule(self.base_ring(
        ), H_basis_brackets, sorting_key=sorting_keys, monomial_reverse=True)
        return self._cohomology[n]

    @cached_method(do_pickle=True)
    def cohomology_algebra(self, max_degree=-1, verbose=False):
        """
        Compute a CDGA with trivial differential, that is isomorphic to the cohomology of
        ``self`` up to ``max_degree`` (default: dimension of the space)

        INPUT:

        - ``max_degree`` -- integer (default: `dimension of the space`); degree to which the result is required to
          be isomorphic to ``self``'s cohomology

        .. tab:: Sage

            EXAMPLES::

                sage: S2 = simplicial_sets.Sphere(2)
                sage: K = S2.product(S2)
                sage: K.cohomology()
                {0: 0, 1: 0, 2: Z x Z, 3: 0, 4: Z}
                sage: W = APLK(K)
                sage: H = W.cohomology_algebra()
                sage: H
                Commutative Differential Graded Algebra with generators ('x0', 'x1', 'x2') in degrees (2, 2, 4) with relations [x0^2 + 2*x2, x0*x1 - x2, x1^2] over Rational Field with differential:
                   x0 --> 0
                   x1 --> 0
                   x2 --> 0
                sage: hgens = K.cohomology_ring(base_ring=QQ).gens()
                sage: hgens
                (h^{0,0}, h^{2,0}, h^{2,1}, h^{4,0})
                sage: x0 = hgens[1]
                sage: x1 = hgens[2]
                sage: x2 = hgens[3]
                sage: x0**2+2*x2
                0
                sage: x0*x1-x2
                0
                sage: x1**2
                0

        .. tab:: Raw code

            EXAMPLES::

                S2 = simplicial_sets.Sphere(2)
                K = S2.product(S2)
                print("Simplicial cohomology")
                print(K.cohomology())
                W = APLK(K)
                H = W.cohomology_algebra()
                print(H)
                hgens = K.cohomology_ring(base_ring=QQ).gens()
                print("testing relations of the generators")
                x0 = hgens[1]
                x1 = hgens[2]
                x2 = hgens[3]
                print(f"x0**2+2*x2 ==> {x0**2+2*x2}")
                print(f"x0*x1-x2 ==> {x0*x1-x2}")
                print(f"x1**2 ==> {x1**2}")
        """

        H = self.K.cohomology_ring(base_ring=self.base_ring())

        if max_degree == -1:
            max_deg = self.K.dimension()

        elif max_degree >= 0 and max_degree <= self.K.dimension():
            max_deg = max_degree
        else:
            raise ValueError(f"The parameter max_degree must be an integer in range (0, {max_deg})")

        cohomgens = {d:list(H.basis(d)) for d in range(1, max_deg+1)}

        if not cohomgens:
            raise ValueError("cohomology ring has no generators")

        h_vector = [len(H.basis(d)) for d in range(max_deg+1)]

        chgens = []
        degrees = []
        for d in cohomgens:
            for g in cohomgens[d]:
                degrees.append(d)
                chgens.append(g)

        A = GradedCommutativeAlgebra(self.base_ring(),
                                     [f'x{i}' for i in range(len(chgens))],
                                     degrees)
        rels = []
        for d in range(1, max_deg + 1):
            i = sum(h_vector[:d])
            j = i + h_vector[d]
            B1 = A.basis(d)
            V2 = self.cohomology_raw(d)
            images = []
            for g in B1:
                ig = g._im_gens_(H, chgens)
                if ig.is_zero():
                    images.append(V2.zero())
                else:
                    images.append(V2.from_vector(ig.to_vector()[i:j]))
            V1 = self.base_ring()**len(B1)
            h = V1.hom(images, codomain=V2)
            ker = h.kernel()
            for g in ker.basis():
                newrel = sum(g[i] * B1[i] for i in range(len(B1)))
                rels.append(newrel)
        if verbose:
            print("Building CDGA ==> Computing the quotient by relations...", flush=True)
        return A.quotient(A.ideal(rels)).cdg_algebra({})

    def cohomology_raw(self, n):
        if (n in self._cohomology_raw.keys()):
            return self._cohomology_raw[n]
        elif (n > self._dimension):
            return span(QQ, zero_vector(QQ, 0))
        basis = self._hodge.harmonic_basis(n)
        F = self.base_ring()
        V = span(F, basis).span_of_basis(basis)
        self._cohomology_raw[n] = V
        return V

    def constant(self, c):
        components = {}
        for dim in range((self._dimension + 1)):
            A = self._apl_algebras.n_th_object(dim)
            for sigma in self.K._n_cells_sorted(dim):
                components[sigma] = A(c)
        return self.element_class()(self, components, check=False)

    def dimension(self):
        return self._dimension

    def element_class(self):
        return APLKElement

    @cached_method(do_pickle=True)
    def exact_basis(self, d, whitney_basis=True, check=False):
        gensSubtype = 'exacts'
        return self._get_basis(d, whitney_basis, gensSubtype, check)

    def gens(self, whitney_basis=True, verbose=True):
        if whitney_basis:
            gensType = 'whitney'
        else:
            gensType = 'hodge'
        for d in range((self.dimension() + 1)):
            if verbose:
                print('Getting generators of degree ', d, '...', flush=True)
            if (not self._gens[gensType][d]['harmonics']):
                self._gens[gensType][d]['harmonics'] = self.harmonic_basis(
                    d, whitney_basis)
            if (not self._gens[gensType][d]['exacts']):
                self._gens[gensType][d]['exacts'] = self.exact_basis(
                    d, whitney_basis)
            if (not self._gens[gensType][d]['coexacts']):
                self._gens[gensType][d]['coexacts'] = self.coexact_basis(
                    d, whitney_basis)
        return self._gens[gensType]

    def gens_names(self, deg=[]):
        if (not deg):
            deg_list = range((self._dimension + 1))
        elif ((deg in ZZ) and (deg >= 0)):
            deg_list = [deg]
        names = []
        for d in deg_list:
            names += self._gens_names_harmonics(d)
            names += self._gens_names_exacts(d)
            names += self._gens_names_coexacts(d)
        return names

    @cached_method(do_pickle=True)
    def harmonic_basis(self, d, whitney_basis=True, check=False):
        gensSubtype = 'harmonics'
        return self._get_basis(d, whitney_basis, gensSubtype, check)

    def hodge(self):
        return self._hodge

    @cached_method(do_pickle=True)
    def hodge_decomposition(self, d, check=False):
        return self._hodge_matrix_decompositions.get(d, self._hodge_matrix_decomposition(d, check))

    @cached_method(do_pickle=True)
    def hodge_matrix_decompositions(self, deg=0, check=False, verbose=True):
        max_deg = int(deg)
        if (max_deg < 0):
            raise ValueError('max_degree must be a positive integer')
        if (max_deg not in ZZ):
            raise ValueError('max_degree must be a positive integer')
        if (max_deg > self._dimension):
            raise ValueError(
                'max_degree must be lower or equal to the dimiension of self')
        if (max_deg == 0):
            max_deg = self._dimension
        for d in range((max_deg + 1)):
            if verbose:
                print('Getting hodge matrix decomposition at degree ',
                      d, '...', flush=True)
            if (not (d in self._hodge_matrix_decompositions.keys())):
                self._hodge_matrix_decomposition(d, check)
        return self._hodge_matrix_decompositions

    def inject_coexact_vars(self, d=[], reload=True, verbose=True, check=False):
        return self._inject_subset_vars(self.coexact_basis, d, reload, verbose, check)

    def inject_exact_vars(self, d=[], reload=True, verbose=True, check=False):
        return self._inject_subset_vars(self.exact_basis, d, reload, verbose, check)

    def inject_harmonic_vars(self, d=[], reload=True, verbose=True, check=False):
        return self._inject_subset_vars(self.harmonic_basis, d, reload, verbose, check)

    def inject_variables(self, reload=True, verbose=True):
        gens = {}
        for (d, components) in self.gens(verbose=verbose).items():
            for (gtype, values) in components.items():
                gens.update(values)
        return self._inject_variables(gens, reload, verbose)

    def is_formal(self, i, max_iterations=3) -> bool:
        r"""
        Check if the algebra is ``i``-formal.

        That is, if it is ``i``-quasi-isomorphic to its cohomology algebra.

        INPUT:

        - ``i`` -- integer; the degree up to which the formality is checked

        - ``max_iterations`` -- integer (default: `3`); the maximum number of
          iterations used in the computation of the minimal model

        .. WARNING::

            The method is not granted to finish (it can't, since the minimal
            model could be infinitely generated in some degrees).
            The parameter ``max_iterations`` controls how many iterations of
            the method are attempted at each degree. In case they are not
            enough, an exception is raised. If you think that the result will
            be finitely generated, you can try to run it again with a higher
            value for ``max_iterations``.

            Moreover, the method uses criteria that are often enough to conclude
            that the algebra is either formal or non-formal. However, it could
            happen that the used criteria can not determine the formality. In
            that case, an error is raised.

        EXAMPLES::

            sage: A.<e1, e2, e3, e4, e5> = GradedCommutativeAlgebra(QQ)
            sage: B = A.cdg_algebra({e5: e1*e2 + e3*e4})
            sage: B.is_formal(1)
            True
            sage: B.is_formal(2)
            False

        ALGORITHM:

        Apply the criteria in :cite:`manero_effective_2020`. Both the `i`-minimal model of the
        algebra and its cohomology algebra are computed. If the numerical
        invariants are different, the algebra is not `i`-formal.

        If the numerical invariants match, the `\psi` condition is checked.
        """

        phi = self.minimal_model(i, max_iterations)
        M = phi.domain()
        H = M.cohomology_algebra(i + 1)
        try:
            H.minimal_model(i, max_iterations)
        except ValueError:  # If we could compute the minimal model in max_iterations
            return False    # but not for the cohomology, the invariants are distinct
        N1 = self.numerical_invariants(i, max_iterations)
        N2 = H.numerical_invariants(i, max_iterations)
        if any(N1[n] != N2[n] for n in range(1, i + 1)):
            return False    # numerical invariants don't match
        subsdict = {y.lift(): 0 for y in M.gens() if not y.differential().is_zero()}
        tocheck = [M(g.differential().lift().subs(subsdict)) for g in M.gens()]
        if all(c.is_coboundary() for c in tocheck):
            return True     # the morphism xi->[xi], yi->0 is i-quasi-iso
        raise NotImplementedError("the implemented criteria cannot determine formality")

    def load_data(self, data):
        self.K = data['K']
        self._gens = data['gens']
        self._coboundaries = data['coboundaries']
        self._cocycles = data['cocycles']
        self._cohomology_raw = data['cohomology_raw']
        self._cohomology = data['cohomology']
        self._ch_vector = data['ch_vector']
        self._apl_algebras = data['apl_algebras ']
        self._hodge = data['hodge']
        self._hodge_matrix_decompositions = data['hodge_matrix_decompositions']
        self._cohomology_mmodels = data['cohomology_mmodels']
        self._minimalmodels = data['minimalmodels']
        self._numerical_invariants = data['numerical_invariants']
        return None

    def numerical_invariants(self, max_degree=3, max_iterations=3):
        r"""
        Return the numerical invariants of the algebra, up to degree ``d``. The
        numerical invariants reflect the number of generators added at each step
        of the construction of the minimal model.

        The numerical invariants are the dimensions of the subsequent Hirsch
        extensions used at each degree to compute the minimal model.

        INPUT:

        - ``max_degree`` -- integer (default: `3`); the degree up to which the
          numerical invariants are computed

        - ``max_iterations`` -- integer (default: `3`); the maximum number of iterations
          used to compute the minimal model, if it is not already cached

        EXAMPLES::

            sage: A.<e1, e2, e3> = GradedCommutativeAlgebra(QQ)
            sage: B = A.cdg_algebra({e3 : e1*e2})
            sage: B.minimal_model(4)
            Commutative Differential Graded Algebra morphism:
            From: Commutative Differential Graded Algebra with
                  generators ('x1_0', 'x1_1', 'y1_0') in degrees (1, 1, 1)
                  over Rational Field with differential:
                    x1_0 --> 0
                    x1_1 --> 0
                    y1_0 --> x1_0*x1_1
            To:   Commutative Differential Graded Algebra with
                  generators ('e1', 'e2', 'e3') in degrees (1, 1, 1)
                  over Rational Field with differential:
                    e1 --> 0
                    e2 --> 0
                    e3 --> e1*e2
            Defn: (x1_0, x1_1, y1_0) --> (e1, e2, e3)
            sage: B.numerical_invariants(2)
            {1: [2, 1, 0], 2: [0, 0]}

        ALGORITHM:

        The numerical invariants are stored as the minimal model is constructed.

        .. WARNING::

            The method is not granted to finish (it can't, since the minimal
            model could be infinitely generated in some degrees).
            The parameter ``max_iterations`` controls how many iterations of
            the method are attempted at each degree. In case they are not
            enough, an exception is raised. If you think that the result will
            be finitely generated, you can try to run it again with a higher
            value for ``max_iterations``.

        REFERENCES:

        For a precise definition and properties, see :cite:`manero_effective_2020`.

        """
        self.minimal_model(max_degree, max_iterations)
        return {i: self._numerical_invariants[i]
                for i in range(1, max_degree + 1)}

    def minimal_model(self, i=3, max_iterations=3, partial_result=False, verbose=True, parallelComp=False):
        r"""

        .. tab:: sage

            EXAMPLES::

                sage: load("Sullivan_MM/tests/zariski.py")
                sage: [S6_1, S6_2] = pair6()
                sage: A1 = APLK(S6_1)
                sage: M1 = A1.minimal_model(i=2, max_iterations=2,parallelComp=False,verbose=True,partial_result=True)
                Starting the computation at degree 1
                Checking injectivity at degree 2 ==> iteration 1 (out of 2)
                (1/3) Trying to get a Whitney form primitive...
                (1/3) Trying to get a Whitney form primitive...
                (1/3) Trying to get a Whitney form primitive...
                Extending the model...
                ....creating GCA...
                ....building HOM B --> A...
                ....updating differential...
                ....Building new Minimal Model...
                Checking injectivity at degree 2 ==> iteration 2 (out of 2)
                sage: B1 = M1.domain()
                sage: B1
                Commutative Differential Graded Algebra with generators ('x1_0', 'x1_1', 'x1_2', 'x1_3', 'x1_4', 'y1_0',
                 'y1_1', 'y1_2', 'y1_3', 'y1_4', 'y1_5') in degrees (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) over Rational
                 Field with differential:
                   x1_0 --> 0
                   x1_1 --> 0
                   x1_2 --> 0
                   x1_3 --> 0
                   x1_4 --> 0
                   y1_0 --> x1_1*x1_2
                   y1_1 --> x1_1*x1_3
                   y1_2 --> x1_2*x1_3
                   y1_3 --> x1_1*x1_4
                   y1_4 --> x1_2*x1_4
                   y1_5 --> x1_3*x1_4
                sage: B1.cohomology(2)
                Free module generated by {[x1_0*x1_1], [x1_0*x1_2], [x1_0*x1_3], [x1_0*x1_4], [x1_1*y1_0], [x1_2*y1_0],
                [x1_3*y1_0 - x1_1*y1_2], [x1_4*y1_0 - x1_1*y1_4], [x1_1*y1_1], [x1_2*y1_1 + x1_1*y1_2], [x1_3*y1_1],
                [x1_4*y1_1 - x1_1*y1_5], [x1_2*y1_2], [x1_3*y1_2], [x1_4*y1_2 - x1_2*y1_5], [x1_1*y1_3],
                [x1_2*y1_3 + x1_1*y1_4], [x1_3*y1_3 + x1_1*y1_5], [x1_4*y1_3], [x1_2*y1_4], [x1_3*y1_4 + x1_2*y1_5],
                [x1_4*y1_4], [x1_3*y1_5], [x1_4*y1_5]} over Rational Field
                sage: x13 = M1._imgens['x1_3']
                sage: y15 = M1._imgens['y1_5']
                sage: p = x13*y15
                sage: p
                [1/12]*e2_28
                sage: p.dif()
                0
                sage: dp = x13*y15
                sage: p = dp.solve_primitive()
                sage: p.dif() == dp
                True
                sage: p.check()
                True

                sage: S2 = simplicial_sets.Sphere(2)
                sage: S4 = simplicial_sets.Sphere(4)
                sage: CP2 = simplicial_sets.ComplexProjectiveSpace(2)
                sage: WS = APLK(S2.wedge(S4))
                sage: WC = APLK(CP2)
                sage: MS = WS.minimal_model(i=4,max_iterations=3,verbose=True)
                Starting the computation at degree 2
                Checking injectivity at degree 3 ==> iteration 1 (out of 3)
                Checking surjectivity at degree 3...
                Checking injectivity at degree 4 ==> iteration 1 (out of 3)
                Extending the model...
                ....creating GCA...
                ....building HOM B --> A...
                ....updating differential...
                ....Building new Minimal Model...
                Checking injectivity at degree 4 ==> iteration 2 (out of 3)
                Checking surjectivity at degree 4...
                Extending the model...
                ....creating GCA...
                ....building HOM B --> A...
                ....updating differential...
                ....Building new Minimal Model...
                Checking injectivity at degree 5 ==> iteration 1 (out of 3)
                sage: MC = WC.minimal_model(i=4,max_iterations=3,verbose=True)
                Starting the computation at degree 2
                Checking injectivity at degree 3 ==> iteration 1 (out of 3)
                Checking surjectivity at degree 3...
                Checking injectivity at degree 4 ==> iteration 1 (out of 3)
                Checking surjectivity at degree 4...
                Checking injectivity at degree 5 ==> iteration 1 (out of 3)
                sage: MS.domain()
                Commutative Differential Graded Algebra with generators ('x2_0', 'y3_0', 'x4_0') in degrees (2, 3, 4) over Rational Field with differential:
                   x2_0 --> 0
                   y3_0 --> x2_0^2
                   x4_0 --> 0
                sage: MC.domain()
                Commutative Differential Graded Algebra with generators ('x2_0',) in degrees (2,) with relations [0] over Rational Field with differential:
                   x2_0 --> 0
                sage: S2.wedge(S4).cohomology()
                {0: 0, 1: 0, 2: Z, 3: 0, 4: Z}
                sage: CP2.cohomology()
                {0: 0, 1: 0, 2: Z, 3: 0, 4: Z}
                sage: MS.cohomology(2)
                Free module generated by {[x2_0]} over Rational Field
                sage: MS.cohomology(3)
                Free module generated by {} over Rational Field
                sage: MS.cohomology(4)
                Free module generated by {[x4_0]} over Rational Field
                sage: MC.cohomology(2)
                Free module generated by {[x2_0]} over Rational Field
                sage: MC.cohomology(3)
                Free module generated by {} over Rational Field
                sage: MC.cohomology(4)
                Free module generated by {[x2_0^2]} over Rational Field


        .. tab:: Raw code

            EXAMPLES::

                load("Sullivan_MM/tests/zariski.py")
                [S6_1, S6_2] = pair6()
                A1 = APLK(S6_1)
                M1 = A1.minimal_model(i=2, max_iterations=2,parallelComp=False,verbose=True,partial_result=True)
                B1 = M1.domain()
                B1.cohomology(2)
                x13 = M1._imgens['x1_3']
                y15 = M1._imgens['y1_5']
                dp = x13*y15
                p = dp.solve_primitive()
                p.dif() == dp
                p.check()

                S2 = simplicial_sets.Sphere(2)
                S4 = simplicial_sets.Sphere(4)
                CP2 = simplicial_sets.ComplexProjectiveSpace(2)
                WS = APLK(S2.wedge(S4))
                WC = APLK(CP2)
                MS = WS.minimal_model(i=4,max_iterations=3,verbose=True)
                MC = WC.minimal_model(i=4,max_iterations=3,verbose=True)
                MS.domain()
                MC.domain()
                S2.wedge(S4).cohomology()
                CP2.cohomology()
                MS.cohomology(2)
                MS.cohomology(3)
                MS.cohomology(4)
                MC.cohomology(2)
                MC.cohomology(3)
                MC.cohomology(4)

        """
        max_degree = int(i)
        if (max_degree < 1):
            raise ValueError('the degree must be a positive integer')
        if ((max_iterations not in ZZ) or (max_iterations < 1)):
            raise ValueError('max_iterations must be a positive integer')
        if (max_degree in self._minimalmodels):
            return self._minimalmodels[max_degree]
        from copy import copy

        def extend(M, ndegrees, ndifs, nimags, nnames, verbose=False):
            B = M.domain()
            if verbose:
                print(f'Extending the model...', flush=True)
            old_names = [str(g) for g in B.gens()]
            new_names = (old_names + list(nnames))
            new_degrees = ([g.degree() for g in B.gens()] + list(ndegrees))
            if verbose:
                print(f'....creating GCA...', flush=True)
            A = GradedCommutativeAlgebra(
                B.base_ring(), names=new_names, degrees=new_degrees)
            if verbose:
                print(f'....building HOM B --> A...', flush=True)
            h = B.hom(A.gens()[:B.ngens()], check=False)
            d = B.differential()
            if verbose:
                print(f'....updating differential...', flush=True)
            diff = {h(g): h(d(g)) for g in B.gens()}
            cndifs = list(copy(ndifs))
            for g in A.gens()[B.ngens():]:
                diff[g] = h(cndifs.pop(0))
            newCDGA = A.cdg_algebra(diff)
            new_imgens = tuple(([M._imgens[name]
                               for name in old_names] + list(nimags)))
            if verbose:
                print(f'....Building new Minimal Model...', flush=True)
            return MinimalModel(domain=newCDGA, codomain=self, names=tuple(new_names),
                                gens=new_imgens)

        def extendx(M, degree, verbose=False, parallelComp=False):
            if verbose:
                print(f'Checking surjectivity at degree {degree}...', flush=True)
            CM = M.cohomology_raw(degree)
            CW = self.cohomology_raw(degree)
            #ncells = len(self.K.n_cells(degree))
            imagesphico = []
            if parallelComp:
                if verbose:
                    print(f' Parallel Computation of the cohomology images...', flush=True)
                Mcohobasis = M.cohomology(degree).basis().keys()
                zipped_data = [(M, g) for g in Mcohobasis]
                imagesphico = [g[1] for g in imagesPhiCoho(zipped_data)]
            else:
                ncoords = CW.dimension()
                for g in M.cohomology(degree).basis().keys():
                    w = M.phi(g.representative()).reduce(0)
                    h = w.coordinates()['harmonic_coords']
                    if ((h == 0) and (len(h) < ncoords)):
                        h = zero_vector(QQ, ncoords)
                    imagesphico += [h]

            # phico: CM --> CW
            phico = matrix(QQ, CM.dimension(), list(imagesphico), sparse=True).T


            # if verbose:
            #     print('phico', flush=True)
            #     print(matrix(QQ, CM.dimension(), list(imagesphico), sparse=True), flush=True)
            #     print('##############################################', flush=True)
            #     print('phico.column_space().complement()', flush=True)
            #     print(phico, flush=True)
            #     print('##############################################', flush=True)
            #     print('CW', flush=True)
            #     print(CW, flush=True)
            if (phico.rank() == 0):
                QI = CW
            else:
                QI = phico.column_space().complement()
            # else:
            #     CW_basismat = CW.basis_matrix().sparse_matrix()
            #     QI = (phico * CW_basismat).row_space()
            self._numerical_invariants[degree] = [QI.dimension()]
            if (QI.dimension() > 0):
                nnames = [f'x{degree}_{j}' for j in range(QI.dimension())]
                nbasis = []
                for v in QI.basis():
                    vl = v #CW.lift(QI.lift(v))
                    #g = self.whitney_form_from_vector(degree, vl)
                    g = self.whitney_form_from_vector(degree, v)
                    nbasis.append(g)
                nimags = nbasis
                ndegrees = [degree for _ in nbasis]
                ndifs = [self.zero() for _ in nimags]
                Mext = extend(M, tuple(ndegrees), tuple(ndifs), tuple(nimags), tuple(nnames), verbose)
                Mext._numerical_invariants = self._numerical_invariants
                return Mext
            M._numerical_invariants = self._numerical_invariants
            return M

        @parallel(ncpus=Integer(10))
        def imagesPhiCoho(M, pol):
            #print(f' getting image phi cohomology of the polynomial {pol}', flush=True)
            p_rep = pol.representative()
            w = M.phi(p_rep).reduce(0)
            if w.dif().is_zero():
                h = w.coordinates()['harmonic_coords']
                ncoords = M.codomain().cohomology_raw(p_rep.degree()).dimension()
                if ((h == 0) and (len(h) < ncoords)):
                    h = zero_vector(QQ, ncoords)
            return h

        @parallel(ncpus=Integer(10))
        def find_preimages(M, pol):
            if verbose:
                print(f'finding preimage of the polynomial {pol}', flush=True)
            w = M.phi(pol)
            if verbose:
                print(f'finding preimage of the element of {pol}', flush=True)
            if w.is_zero():
                return self.zero()
            else:
                return w.solve_primitive(verbose=verbose)
            # v = w.integral()
            # if v.is_zero():
            #     return self.zero()
            # else:
            #     primitive = w.get_preimage_exact_component()
            #     if (primitive.differential().reduce(0) == w.reduce(0)):
            #         return primitive
            #     else:
            #         return w.solve_primitive(verbose=verbose)

        def extendy(M, degree, verbose=False, parallelComp=False):
            nnamesy = 0
            for iteration in range(max_iterations):
                if verbose:
                    print(
                        f'Checking injectivity at degree {degree} ==> iteration {(iteration + 1)} (out of {max_iterations})', flush=True)
                CM = M.cohomology_raw(degree)
                CW = self.cohomology_raw(degree)
                imagesphico = []
                if parallelComp:
                    if verbose:
                        print(
                            f' Parallel Computation of the cohomology images...', flush=True)
                    Mcohobasis = M.cohomology(degree).basis().keys()
                    zipped_data = [(M, g) for g in Mcohobasis]
                    imagesphico = [g[1] for g in imagesPhiCoho(zipped_data)]
                    if verbose:
                        print(
                            f'elements imagesphico ==> {[g for g in imagesphico]}', flush=True)
                        print(f'', flush=True)
                else:
                    ncoords = CW.dimension()
                    for g in M.cohomology(degree).basis().keys():
                        w = M.phi(g.representative()).reduce(0)
                        if w.dif().is_zero():
                            h = w.coordinates()['harmonic_coords']
                            if ((h == 0) and (len(h) < ncoords)):
                                h = zero_vector(QQ, ncoords)
                            imagesphico += [h]
                # if verbose:
                #     print(
                #         f'elements imagesphico ==> {[g for g in imagesphico]}', flush=True)
                #     print(f'', flush=True)

                # phico := matrix representation of the induced morphism phi on cohomology.
                # The ith-column represents the coordinate vector of the generator g \in H(M) at H(C(K)).
                phico = matrix(QQ, CM.dimension(), list(imagesphico), sparse=True).T
                # phicokermat := kernel matrix of the induced morphism phi
                phicokermat = phico.right_kernel_matrix().sparse_matrix()
                ker_dim = phicokermat.nrows()
                self._numerical_invariants[(degree - 1)].append(ker_dim)
                M._numerical_invariants = self._numerical_invariants
                if (ker_dim == 0):
                    return M
                if (iteration == (max_iterations - 1)):
                    return (M,)
                ndifs = (phicokermat * CM.basis_matrix()).rows()
                basisdegree = M.basis(degree)
                """
                print(f"len(basisdegree) ==> {len(basisdegree)}", flush=True)
                print(f"ndifs ==> {ndifs}", flush=True)
                print(f"phicokermat ==> {phicokermat}", flush=True)
                print(f"CM.basis_matrix().dimensions ==> {CM.basis_matrix().dimensions()}", flush=True)
                print(f"phicokermat.dimensions ==> {phicokermat.dimensions()}", flush=True)
                """
                ndifs = [sum(((basisdegree[j] * CM.lift(g)[j])
                             for j in range(len(basisdegree)))) for g in ndifs]
                #ncells = len(self.K.n_cells((degree - 1)))
                nimags = []
                if parallelComp:
                    raise NotImplementedError
                    if verbose:
                        print(f' Parallel Computation of the Whitney preimages...', flush=True)
                    #nimags = [w[1] for w in find_preimages(((M, g) for g in ndifs))]
                else:
                    for g in ndifs:
                        w = M.phi(g)
                        if w.is_zero():
                            nimags.append(self.zero())
                        else:
                            #print(f" finding preimage ==> {w.dif().reduce(0)}",flush=True)
                            primitive = w.solve_primitive(verbose=verbose)
                            nimags.append(primitive)
                        # v = w.integral()
                        # if v.is_zero():
                        #     nimags.append(self.zero())
                        # else:
                        #     #primitive = w.get_preimage_exact_component()
                        #     if (primitive.differential().reduce(0) == w.reduce(0)):
                        #         nimags.append(primitive)
                        #     else:
                        #         nimags.append(w.solve_primitive(verbose=verbose))
                ndegrees = [(degree - 1) for g in nimags]
                nnames = ['y{}_{}'.format((degree - 1), (j + nnamesy))
                          for j in range(len(nimags))]
                nnamesy += len(nimags)
                # if verbose:
                #     print()
                #     print("Extend ndifs", flush=True)
                #     print(ndifs)
                #     print()
                M = extend(M, tuple(ndegrees), tuple(ndifs),
                           tuple(nimags), tuple(nnames), verbose)
                M._numerical_invariants = self._numerical_invariants
            return M

        if (not self._minimalmodels):
            degnzero = 1
            while (self.cohomology(degnzero).dimension() == 0):
                self._numerical_invariants[degnzero] = [0]
                degnzero += 1
                if (degnzero > max_degree):
                    raise ValueError('cohomology is trivial up to max_degree')
            if verbose:
                print(
                    f'Starting the computation at degree {degnzero}', flush=True)
            gens = [g.representative() for (i, g) in enumerate(
                self.cohomology(degnzero).basis().keys())]
            self._numerical_invariants[degnzero] = [len(gens)]
            names = ['x{}_{}'.format(degnzero, j) for j in range(len(gens))]
            A = GradedCommutativeAlgebra(self.base_ring(), names, degrees=[
                                         degnzero for _ in names])
            B = A.cdg_algebra(A.differential({}))
            M = MinimalModel(domain=B, codomain=self,
                             names=tuple(names), gens=tuple(gens))
            Mext = extendy(M, (degnzero + 1), verbose, parallelComp)
            if isinstance(Mext, tuple):
                if (not partial_result):
                    raise ValueError(
                        'could not cover all relations in max iterations in degree {}'.format((degnzero + 1)))
                return Mext[0]
            M = Mext
            self._minimalmodels[degnzero] = M
        else:
            degnzero = max(self._minimalmodels)
            M = self._minimalmodels[degnzero]

        for degree in range((degnzero + 1), (max_degree + 1)):
            if (not (degree in self._numerical_invariants.keys())):
                self._numerical_invariants[degree] = []
            Mext = extendx(M, degree, verbose, parallelComp)
            M = extendy(Mext, (degree + 1), verbose, parallelComp)
            if isinstance(M, tuple):
                if partial_result:
                    return M[0]
                else:
                    raise ValueError(
                        'could not cover all relations in max iterations in degree {}'.format((degree + 1)))
            self._minimalmodels[degree] = M
        return M

    def one(self):
        components = {}
        for dim in range((self._dimension + 1)):
            A = self._apl_algebras.n_th_object(dim)
            for sigma in self.K._n_cells_sorted(dim):
                components[sigma] = A.one()
        return self.element_class()(self, components, check=False)

    def reset_data(self):
        self._gens = {}
        self._apl_algebras = {}
        self._hodge = {}
        self._hodge_matrix_decompositions = {}
        self._minimalmodels = {}
        self._numerical_invariants = {}
        self._coboundaries = {}
        self._cocycles = {}
        self._cohomology_raw = {}
        self._cohomology = {}
        self._ch_vector = self._get_cohomology_dimensions()
        self._apl_algebras = SimplicialAPL(self._dimension)
        self._gens = {'hodge': {}, 'whitney': {}}
        for d in range((self.K.dimension() + 1)):
            self._gens['hodge'][d] = {
                'harmonics': {}, 'exacts': {}, 'coexacts': {}}
            self._gens['whitney'][d] = {
                'harmonics': {}, 'exacts': {}, 'coexacts': {}}
        self._hodge = Hodge(self.K)
        self._hodge_matrix_decompositions = {}
        return None

    def save(self, filename='WData_temp'):
        data = self._pack_data()
        save(dumps([self, data]), filename)
        return None

    def whitney_form_from_cochain(self, cochain, check=False):
        S = self._apl_algebras
        whitney_form = self.zero()
        for dim in range((self._dimension + 1)):
            cells = self.K._n_cells_sorted(dim)
            dimCells = set(cells).intersection(set(cochain.keys()))
            if dimCells:
                v = self._cochain_to_vector(dim, cochain)
                element = self.whitney_form_from_vector(dim, v, check)
                whitney_form += element
        if check:
            self._check_compatibility(whitney_form._components)
        return whitney_form

    def whitney_form_from_vector(self, dim, v, check=False):
        S = self._apl_algebras
        A = S.n_th_object(dim)
        wf = A.whitney_form()
        components = self.zero()._components
        cells = self.K._n_cells_sorted(dim)
        for (i, c) in enumerate(v):
            components[cells[i]] += A((c * wf))
        for dim_to in range((dim + 1), (self._dimension + 1)):
            cells = self.K._n_cells_sorted(dim_to)
            face_data = self._face_data(dim, dim_to)
            ncells = len(cells)
            A = S.n_th_object(dim_to)
            for face in face_data.keys():
                face_matrix = face_data[face].T
                w = (face_matrix * v)
                sgn = sgn_face(face)
                for (j, c) in enumerate(w):
                    components[cells[j]
                               ] += A((c * S.whitney_map(face, dim_to)))
        return self.element_class()(self, components, check)

    def aplk_genset(self, dim, degt = 1, check=False):

        S = self._apl_algebras
        A = S.n_th_object(dim)
        R = A.base_ring()
        rgens = R.monomials_of_degree(degt)
        hodge = self.hodge()
        harmonic_basis = hodge.harmonic_basis(dim)
        exact_basis = hodge.exact_basis(dim)
        coexact_basis = hodge.coexact_basis(dim)
        cells = self.K._n_cells_sorted(dim)
        wf = A.whitney_form()
        genset = []
        for basis in [harmonic_basis, exact_basis, coexact_basis]:
            for v in basis:
                for t in rgens:
                    components = self.zero()._components
                    for (i, c) in enumerate(v):
                        components[cells[i]] += A((c* A(t) * wf))
                    for dim_to in range((dim + 1), (self._dimension + 1)):
                        cofaces = self.K._n_cells_sorted(dim_to)
                        face_data = self._face_data(dim, dim_to)
                        ncells = len(cofaces)
                        Ato = S.n_th_object(dim_to)
                        for face in face_data.keys():
                            face_matrix = face_data[face].T
                            w = (face_matrix * v)
                            #sgn = sgn_face(face)
                            for (j, c) in enumerate(w):
                                components[cofaces[j]] += (
                                    Ato((c * S.affine_map(faces=face, dim=dim_to, coef=Ato(t), normalized=True))))
                    gen = self.element_class()(self, components, check)
                    genset += [gen]
        return genset

    def zero(self):
        components = {}
        for dim in range((self._dimension + 1)):
            A = self._apl_algebras.n_th_object(dim)
            for sigma in self.K._n_cells_sorted(dim):
                components[sigma] = A.zero()
        return self.element_class()(self, components, check=False)


class APLKElement(Element):

    def __getitem__(self, sigma):
        return self._components[sigma]

    def __init__(self, parent, components, check=False):
        self._components = components
        self._base_ring = parent.base_ring()
        Element.__init__(self, parent)
        if check:
            print(
                '(WhitneyForm Element Constructor) Checking compatibility...', flush=True)
            parent._check_compatibility(components)
        self._vector = None
        self._hodge_decomp = ()
        self._hodge_whitney_decomp = ()
        self._coords = {}
        self._repr_str = None

    def __neg__(self):
        return ((- 1) * self)

    def __pow__(self, n):
        components = {}
        for sigma in self._components:
            components[sigma] = prod((n * [self._components[sigma]]))
        return self.parent().element_class()(self.parent(), components, check=False)

    def _add_(self, other):
        components = {}
        for sigma in self._components:
            components[sigma] = (self._components[sigma] +
                                 other._components[sigma])
        return self.parent().element_class()(self.parent(), components, check=False)

    def _div_(self, other):
        if (not other.is_constant()):
            raise ValueError(f'the element {other} is not constant')
        components = {}
        other_red = other.reduce(0)
        for sigma in self._components:
            components[sigma] = (
                self._components[sigma] / QQ(other_red._components[sigma].leading_coefficient()))
        return self.parent().element_class()(self.parent(), components, check=False)

    def _mul_(self, other):
        components = {}
        for sigma in self._components:
            components[sigma] = (self._components[sigma]
                                 * other._components[sigma])
        return self.parent().element_class()(self.parent(), components, check=False)

    def _repr_(self):
        if self._repr_str:
            return self._repr_str
        W = self.parent()
        d = self.degree()

        if self.is_zero():
            self._repr_str = '0'
            return self._repr_str

        elif self.integral()==0:
            self._repr_str = '[non-zero ker_oint]'
            return self._repr_str

        def terms_str(coords, names):
            terms = []
            for (c, g) in zip(coords, names):
                if c:
                    if (c != 1):
                        coeff = (('(' + str(c)) + ')*')
                    else:
                        coeff = ''
                    terms += [(coeff + g)]
            return terms

        def str_component(coords, names):
            prefix = ''
            suffix = ''
            if (len(coords.nonzero_positions()) > 1):
                prefix = '['
                suffix = ']'
            return ((prefix + ' + '.join(terms_str(coords, names))) + suffix)
        coords = self.coordinates()
        h_coords = coords['harmonic_coords']
        e_coords = coords['exact_coords']
        c_coords = coords['coexact_coords']
        harmonic_component = ''
        exact_component = ''
        coexact_component = ''
        if (h_coords != 0):
            h_names = W._gens_names_harmonics(d)
            h_gcd = gcd(h_coords)
            if (h_gcd == 1):
                h_gcd_str = ''
            else:
                h_coords = (h_coords / h_gcd)
                h_gcd_str = (('[' + str(h_gcd)) + ']*')
            harmonic_component = str_component(h_coords, h_names)
            if (h_gcd != 1):
                harmonic_component = (h_gcd_str + harmonic_component)
        if (e_coords != 0):
            e_names = W._gens_names_exacts(d)
            e_gcd = gcd(e_coords)
            if (e_gcd == 1):
                e_gcd_str = ''
            else:
                e_coords = (e_coords / e_gcd)
                e_gcd_str = (('[' + str(e_gcd)) + ']*')
            exact_component = str_component(e_coords, e_names)
            prefix = ''
            if h_coords:
                prefix = ' + '
            if (e_gcd != 1):
                exact_component = ((prefix + e_gcd_str) + exact_component)
        if (c_coords != 0):
            c_names = W._gens_names_coexacts(d)
            c_gcd = gcd(c_coords)
            if (c_gcd == 1):
                c_gcd_str = ''
            else:
                c_coords = (c_coords / c_gcd)
                c_gcd_str = (('[' + str(c_gcd)) + ']*')
            coexact_component = str_component(c_coords, c_names)
            prefix = ''
            if (h_coords or e_coords):
                prefix = ' + '
            if (c_gcd != 1):
                coexact_component = ((prefix + c_gcd_str) + coexact_component)
        self._repr_str = ((harmonic_component + exact_component) + coexact_component)
        return self._repr_str

    def _richcmp_(self, other, op):
        if (op == op_EQ):
            if (self._components.keys() != other._components.keys()):
                return False
            for sigma in self._components:
                if (self._components[sigma].reduce(0) != other._components[sigma].reduce(0)):
                    return False
            return True
        elif (op == op_NE):
            return (not self._richcmp_(other, op_EQ))
        else:
            raise NotImplementedError(
                'operation not implemented for this element class')

    def _sub_(self, other):
        components = {}
        for sigma in self._components:
            components[sigma] = (self._components[sigma] -
                                 other._components[sigma])
        return self.parent().element_class()(self.parent(), components, check=False)

    def base_ring(self):
        return self._base_ring

    def check(self):
        red_el = self.reduce(0)
        for homog in red_el.homogeneous_components().values():
            self.parent()._check_compatibility(homog._components)
        return True

    def coefficient(self):
        if (self.degree() == 0):
            return self
        W = self.parent()
        S = W._apl_algebras
        K = W.K
        dim = self.degree()
        components = W.zero()._components
        A = W._apl_algebras.n_th_object(dim)
        ncells = set(K.n_cells(dim))
        nkeys = set(self._components.keys())
        for sigma in ncells.intersection(nkeys):
            p = self._components[sigma].reduce(0)
            if (not p.is_zero()):
                coeff = p.leading_coefficient()
                components[sigma] = A(coeff)
        for d in reversed(range(dim)):
            A = W._apl_algebras.n_th_object(d)
            upperDims = (dim - d)
            faces = list(combinations(range((dim + 1)), upperDims))
            for face in faces:
                coface_morph = W._coface_coeff_endomorphism(face, dim, d)
                for sigma in K.n_cells(dim):
                    f_sigma = sigma
                    for f in reversed(face):
                        f_sigma = K.face(f_sigma, f)
                    components[f_sigma] = A(coface_morph(components[sigma]))
        for d in range((dim + 1), K.dimension()):
            A = W._apl_algebras.n_th_object(d)
            upperDims = (d - dim)
            faces = list(combinations(range((d + 1)), upperDims))
            for face in faces:
                coface_morph = W._coface_coeff_endomorphism(face, dim, d)
                for sigma in K.n_cells(d):
                    f_sigma = sigma
                    for f in face:
                        f_sigma = K.face(f_sigma, f)
                    components[sigma] = (
                        ((- 1) ** sgn_face(face)) * A(coface_morph(components[f_sigma])))
        return self.parent().element_class()(self.parent(), components, check=False)

    def coordinates(self):
        if self._coords:
            return self._coords
        else:
            self._coords = self.parent()._get_coordinates(self)
        return self._coords

    def degree(self):
        degrees = set()
        W = self.parent()
        for (sigma, f) in self._components.items():
            A = W._apl_algebras.n_th_object(sigma.dimension())
            if (not f.is_zero()):
                deg = A(f).degree()
                if (deg in range((A.n + 1))):
                    degrees.add(deg)
        if (len(degrees) == 1):
            return degrees.pop()
        else:
            return (- 1)

    def dif(self, check=False):
        r"""
        Alias for :meth:`differential`
        """
        return self.differential(check)

    def differential(self, check=False):
        components = {}
        for sigma in self._components:
            components[sigma] = self._components[sigma].differential().reduce(0)
        return self.parent().element_class()(self.parent(), components, check)

    def dup(self, check=False):
        r"""
        Alias for :meth:`dupont_contraction`
        """
        return self.dupont_contraction(check)

    def dupont_contraction(self, check=False):
        r"""
        The Dupont\'s contraction of polynomial differential forms defined
        on a generic simplicial set `S` (see :cite:`dupont1976simplicial`).
        This method implements the Dupont\'s contraction

        .. math::

            s_n: A^{*}_{PL}(S_n) \rightarrow A^{*-1}_{PL}(S_n)

        as it is described in :cite:`cheng2008transferring` (see also :cite:`dupont1976simplicial`).

        Let :math:`\mathbb{K}` be a field of characteristic :math:`0` and let :math:`S = \{S_n\}_{n \geq 0}` be a
        simplicial set. Also, let :math:`A_{PL}(S)` be the algebra of polynomial differential forms defined on :math:`S`,
        and :math:`C^*(S)`, the simplicial cochain complex associated to :math:`S`.

        Let :math:`I = \{i_0,\dots,i_p\}`, with  :math:`0 \leq i_0 < \cdots < i_p \leq n,` and define

        .. math::

            J := [n] \smallsetminus  I = \{j_0,\dots,j_q\}

        such that :math:`0 \leq j_0 < \cdots < j_q \leq n` and :math:`p+q=n`.

        Let :math:`\sigma_p \in S_p` and :math:`\sigma_n \in S_n` be two simplices of `S` such that,
        :math:`\partial_J(\sigma_n) = \sigma_p` where

        .. math::

            \partial_J = \partial_{j_0} \circ \cdots \circ \partial_{j_q}.

        Let :math:`\beta \in C^p(S)`. The Whitney map (see :cite:`Whitney1957GeometricIT, WhitneyFormsLOHI`)

        .. math::

            \mathcal{W}^p = \{\mathcal{W}^p_n: C^p(S_p) \rightarrow A^p_{PL}(S_n)\}

        is defined as:

        .. math::

            \mathcal{W}^p_n(\beta)(\sigma_n)|_{\sigma_p} = \beta(\sigma_p) \cdot n! \cdot \sum_{k=0}^{p} (-1)^j t_{i_k}
            y_{i_0} \wedge \cdots \wedge \hat{y}_{i_k} \wedge \cdots \wedge y_{i_p}

        where the symbol :math:`\; \hat{} \;` means the term is omitted. The elements in the image of
        :math:`\mathcal{W}` are called the `elementary differential forms` or just `Whitney forms`.
        The motivation behind this notation is that the subset `I` comes from the inclusion

        .. math::

            i: \Delta^p \hookrightarrow{} \Delta^n

        that, by the :math:`A_{PL}` functor translates to the inclusion of algebras:

        .. math::

                \begin{array}{cccc}
                   A_{PL}(i): &(A_{PL})_p & \hookrightarrow{} & (A_{PL})_n \\
                    & (t_0,\dots, t_p) &\rightarrow& (t_{i_0},\dots, t_{i_p})
                \end{array}



        Finally, consider the de Rham map (see :cite:`Whitney1957GeometricIT, dupont1976simplicial, felix_rational_2001`):

        .. math::

            \int_n: A^n_{PL}(S) \rightarrow C^n(S)

        Dupont constructed an explicit simplicial contraction of the commutative differential graded algebra
        of polynomial differential forms :math:`A_{PL}(S)` to :math:`C^*(S)` compatible with the intrinsic
        affine structure of the polynomial differential forms (affine relations) and also with
        the wedge product of forms (up to homotopy).

        This method implements step by step the description of the contraction given
        by Cheng et al. (see :cite:`cheng2008transferring`), with minor notation adaptations for the sake
        of maintain coherence with the rest of the code. The description given by Cheng et al. is as follows:

        For each vertex :math:`e_i` of the :math:`n`-simplex :math:`\Delta^n`, define the dilation map

        .. math::

            \phi_i : [0,1] \times \Delta^n \to \Delta^n

        by the formula

        .. math::

            \phi_i(u,t_0, \dots, t_n) = ((1-u)t_0,\dots,(1-u)t_i+u,\dots,(1-u)t_n) .

        Let

        .. math::

            (\pi_i){}_*:A^*_{PL}([0,1]\times\Delta^n) \rightarrow A^{*-1}_{PL}(\Delta^n)

        be integration over the first factor.

        Now, let :math:`\omega \in (A_{PL})_n` and define the operator

        .. math::

            h_n^i : A^*_{PL}(\Delta^n) \rightarrow A^{*-1}_{PL}(\Delta^n)

        by the formula

        .. math::

            h_n^i\omega = (\pi_i)_* \phi_i^* \omega.

        where :math:`\phi_i^* \omega` is the pullback of :math:`\omega` respect to :math:`\phi_i`.

        Let

        .. math::

            \epsilon_n^i: A^*_{PL}(\Delta^n) \rightarrow \mathbb{K}

        be evaluation at the vertex :math:`e_i`. The Poincar\'e Lemma states that

        .. math::

            \mathbb{1}_{A} - \epsilon_n^i =  d \circ h_n^i + h_n^i \circ d .


        Now, let :math:`J^k:=\{\{i_0,\dots, i_{k-1}\} \; | \; 0 \leq i_0 < \cdots < i_{k-1} \leq n\}`,
        be the set of all subsets of :math:`\{0,\dots,n\}` with cardinality `k`.

        **Theorem** (Dupont :cite:`dupont1976simplicial`):

            The operator

            .. math::

                s_n(\omega) = \sum_{k=0}^{n-1} \sum_{I \in J^k} \mathcal{W}^I_n(1) \wedge (h^{i_k} \circ
                \cdots \circ  h^{i_0})(\omega)

            defines a simplicial contraction from :math:`A^*_{PL}(S)` to :math:`C^*(S)`:

            .. math::

                \mathcal{W}_n \circ \int_n - \mathbb{1}_{A}  = d \circ s_n+s_n \circ d .

        **Theorem** (Getzler :cite:`Getzler_2009`):

            The side conditions

            - :math:`\int_n \circ s_n = 0`

            - :math:`s_n \circ s_n = 0`

            hold.

        .. SEEALSO::

            :meth:`.AplN.Element.integral`

            :meth:`.AplN.whitney_form`

            :meth:`.AplN.Element.dupont_operator`

            :meth:`.SimplicialAPL.whitney_map`

            :meth:`.integral`


        .. REFERENCES::

            - :cite:`Whitney1957GeometricIT`

            - :cite:`dupont1976simplicial`

            - :cite:`cheng2008transferring`

            - :cite:`WhitneyFormsLOHI`

            - :cite:`felix_rational_2001`



        INPUT:

        - ``p`` -- an element of ``self``.

        - ``i`` -- integer; the vertex index to apply the operator

        OUTPUT: an element of ``self``;

        EXAMPLES::

            sage: K = simplicial_complexes.Sphere(2)
            sage: W = WhitneyFormAlgebraComplex(K)
            sage: W.inject_variables()
            Getting generators of degree  0 ...
            Getting generators of degree  1 ...
            Getting generators of degree  2 ...
            Defining t0, t1, t2, t3, e1_0, e1_1, e1_2, c1_0, c1_1, c1_2, h2_0, e2_0, e2_1, e2_2
            sage: p = t0**2+t3**5
            sage: dp = p.differential()
            sage: wi = sum(dp.reduce(0).hodge_whitney_decomposition())
            sage: dp-wi == dp.dupont_contraction().differential()
            True

        """

        def contraction(p):
            A = p.parent()
            S = self.parent()._apl_algebras
            n = A.n
            result = A.zero()
            for k in range(n):
                simplices = list(combinations(range((n + 1)), (k + 1)))
                for sigma in simplices:
                    facepath = tuple(sorted((set(range((n + 1))) - set(sigma))))
                    #print(f"k ==> {k}, sigma ==> {sigma} and facepath==> {facepath} at dim {n}", flush=True)
                    if not len(facepath) == n-k:
                        raise RuntimeError("internal error using combinations "
                                           "at dupont_contraction method (AplK)")
                    wf = S.whitney_map(facepath, n)
                    dup = p
                    for i in sigma:
                        dup = dup.dupont_operator(i)
                    result += (wf * dup)
            return result.reduce(0)

        components = {}
        for (sigma, pol) in self._components.items():
            components[sigma] = contraction(self._components[sigma])
        return self.parent().element_class()(self.parent(), components, check)

    def get_preimage_exact_component(self):
        W = self.parent()
        deg = self.degree()
        lengthCoords = len(W.coexact_basis((deg - 1)))
        exact_basis = W.exact_basis(deg)
        exact_coords = self.coordinates()['exact_coords']
        if (exact_coords == 0):
            return W.zero()
        else:
            hodge = W.hodge()
            v = (hodge.exact_matrix(deg).T * exact_coords)
            preimage_cochain = hodge.preimage(v, deg)
            w = W.whitney_form_from_vector((deg - 1), preimage_cochain)
            return w

    def hodge_cochain_decomposition(self):
        if self._hodge_decomp:
            return self._hodge_decomp
        if self.is_zero():
            z = self.integral()
            return tuple(3*[z])
        hodge = self.parent().hodge()
        cochain = self.integral()
        deg = self.degree()
        self._hodge_decomp = hodge.hodge_cochain_decomposition(cochain, deg)
        return self._hodge_decomp

    def hodge_whitney_decomposition(self):
        if self._hodge_whitney_decomp:
            return self._hodge_whitney_decomp
        W = self.parent()
        hodge = W.hodge()
        (h, e, c) = self.hodge_cochain_decomposition()
        self._hodge_whitney_decomp = tuple(
            [W.whitney_form_from_vector(self.degree(), x) for x in (h, e, c)])
        return self._hodge_whitney_decomp

    def hodge_whitney_remainders(self):
        if (not (self.integral() == 0)):
            (wh, we, wc) = self.hodge_whitney_decomposition()
            harmonic_remainder = ((self - we) - wc)
            exact_remainder = ((self - wh) - wc)
            coexact_remainder = ((self - wh) - we)
            return (harmonic_remainder, exact_remainder, coexact_remainder)
        else:
            print('The element is a representative of the zero cochain....', flush=True)
            return ((), (), ())

    def homogeneous_components(self):
        degs = self.homogeneous_degrees()
        if (len(degs) == 1):
            return {degs[0]: self}
        reducedSelf = self.reduce(0)
        components = {}
        for d in degs:
            element = self.parent().zero()
            dcomp = self.parent().zero()._components
            for (sigma, f) in reducedSelf._components.items():
                element._components[sigma] = f.homogeneous_component(d)
            if (not element.is_zero()):
                components[d] = element
        return components

    def homogeneous_degrees(self):
        degs = []
        for (sigma, f) in self._components.items():
            homComps = f.homogeneous_components()
            if isinstance(homComps, dict):
                degs += list(homComps.keys())
            elif (not self.is_zero()):
                degs += [self.degree()]
            else:
                degs += [0]
        return list(set(degs))

    def is_closed(self):
        if (self.differential().reduce(0) == 0):
            return True
        return False

    def is_coexact(self):
        (rem_H, rem_E, rem_C) = self.hodge_whitney_remainders()
        if ((isinstance(rem_H, APLKElement) and rem_H.is_zero()) or (rem_H == 0)):
            if ((isinstance(rem_E, APLKElement) and rem_E.is_zero()) or (rem_E == 0)):
                if (not rem_C.is_zero()):
                    return True
        return False

    def is_cohomologous_to(self, other):
        if other.is_zero():
            return self.is_exact()
        if ((not isinstance(other, self.parent().element_class())) or (self.parent() is not other.parent())):
            raise ValueError(f'the element {other} does not lie in this CDGA')
        difference = (self - other)
        if difference.is_homogeneous():
            return (difference.is_exact() or difference.is_zero())
        return (self.is_exact() and other.is_exact())

    def is_constant(self):
        if (self.degree() != 0):
            return False
        components = {}
        w = self.reduce(0)
        for sigma in w._components:
            if (not (w._components[sigma].leading_coefficient().degree() == 0)):
                return False
        return True

    def is_exact(self):
        (rem_H, rem_E, rem_C) = self.hodge_whitney_remainders()
        if ((isinstance(rem_H, APLKElement) and rem_H.is_zero()) or (rem_H == 0)):
            if ((isinstance(rem_C, APLKElement) and rem_C.is_zero()) or (rem_C == 0)):
                if (not rem_E.is_zero()):
                    return True
        return False

    def is_harmonic(self):
        (rem_H, rem_E, rem_C) = self.hodge_whitney_remainders()
        if ((isinstance(rem_E, APLKElement) and rem_E.is_zero()) or (rem_E == 0)):
            if ((isinstance(rem_C, APLKElement) and rem_C.is_zero()) or (rem_C == 0)):
                if (not rem_H.is_zero()):
                    return True
        return False

    def is_homogeneous(self):
        if self.is_zero():
            return True
        homogeneous = True
        for (sigma, f) in self._components.items():
            if (not f.is_zero()):
                homogeneous = (homogeneous and f.is_homogeneous())
                if (not homogeneous):
                    return False
        return True

    def is_zero(self):
        return (self.reduce(0) == self.parent().zero())

    def leading_coefficient(self):
        coeffs = self.leading_coefficients()
        if (not coeffs):
            return (0, 0)
        degrees = [c[1] for c in coeffs]
        idx = degrees.index(max(degrees))
        return coeffs[idx]

    def leading_coefficients(self):
        if self.is_zero():
            return []
        W = self.parent()
        K = W.K
        cells = K.n_cells(self.degree())
        components = self._components
        coeffs = []
        for sigma in cells:
            if ((sigma in components) and components[sigma]):
                coeffs += [self._components[sigma].leading_coefficient()]
        degrees = [e.degree() for e in coeffs]
        return list(set(zip(coeffs, degrees)))

    def reduce(self, i=0):
        components = {}
        for sigma in self._components:
            components[sigma] = self._components[sigma].reduce(i)
        return self.parent().element_class()(self.parent(), components, check=False)

    def solve_primitive(self, verbose=False):
        if self.differential():
            raise ValueError('The element is not closed.')
        W = self.parent()
        K = W.K
        S = W._apl_algebras
        result = W.zero()
        for (deg, homo) in self.homogeneous_components().items():
            wi = homo.get_preimage_exact_component().reduce(0)
            if verbose:
                print('(1/3) Trying to get a Whitney form primitive...', flush=True)
            if (wi.differential().reduce(0) == homo.reduce(0)):
                result += wi
            else:
                if verbose:
                    print(
                        ' (2/3) Trying to get a primitive with the Dupont contraction ==> (ds+sd) == (wi-p)...', flush=True)
                s = homo.dupont_contraction().reduce(0)
                if ((wi - s).differential().reduce(0) == homo.reduce(0)):
                    result += wi - s
                else:
                    if verbose:
                        print('(3/3) Trying the brute-force approach...', flush=True)
                        print("", flush=True)
                        print(f"(wi-s).dif() ==> {(wi-s).differential().reduce(0)}", flush=True)
                        print("", flush=True)
                    b0 = W.basis(0)
                    b2 = W.basis((homo.degree() - 1))
                    deg_t = homo.reduce(0).leading_coefficient()[1]
                    deg0_coefs = [prod(c)
                                  for c in cartesian_product((deg_t * [b0]))]
                    b02 = [prod(c) for c in cartesian_product(
                        [deg0_coefs, b2]) if prod(c).differential()]
                    db02 = [g.differential().reduce(0) for g in b02]
                    rows = [g.terms_repr(deg_t) for g in db02]
                    m = matrix(QQ, len(db02), rows, sparse=True)
                    vdp = homo.reduce(0).terms_repr(deg_t)
                    coords = m.T.solve_right(vdp)
                    primitive = sum([prod(c) for c in zip(coords, b02)])
                    assert (primitive.differential().reduce(
                        0) == homo.reduce(0))
                    result += primitive
        return result

    def str(self):
        return {sigma: f for (sigma, f) in self._components.items() if (not f.is_zero())}

    def terms_repr(self, deg_t=[]):
        K = self.parent().K
        list_repr = []
        if (not deg_t):
            deg_t = self.leading_coefficient()[1]
        deg_y = self.degree()
        for f in K.facets():
            pol = self._components[f]
            if pol:
                v = pol._to_extended_graded_module(
                    deg_y=deg_y, deg_t=deg_t).to_vector()
            else:
                n = len(pol.parent().extended_basis(
                    deg_y=deg_y, deg_t=deg_t, cum=True))
                v = vector(QQ, (n * [0]))
            list_repr.append(list(v))
        return vector(QQ, flatten(list_repr), sparse=True)

    def to_AplK(self, reduce=None):
        aplK_dict = {}
        for dim in range((self.parent().dimension() + 1)):
            for sigma in self.parent().K._n_cells_sorted(dim):
                f_sigma = self._components[sigma]
                if ((not (reduce == None)) and (reduce in ZZ) and (reduce in range((f_sigma.parent().n + 1)))):
                    f_sigma = f_sigma.reduce(reduce)
                if f_sigma.is_zero():
                    continue
                aplK_dict[sigma] = f_sigma
        return aplK_dict

    def to_cochain(self):
        cochain = {}
        for dim in range((self.parent().dimension() + 1)):
            for sigma in self.parent().K._n_cells_sorted(dim):
                f_sigma = self._components[sigma]
                if f_sigma.is_zero():
                    continue
                if (f_sigma.degree() == dim):
                    try:
                        val = f_sigma.integral()
                        if (val != 0):
                            cochain[sigma] = val
                    except (AttributeError, ValueError):
                        if (not f_sigma.is_zero()):
                            cochain[sigma] = f_sigma.leading_coefficient()
        return cochain

    def integral(self):
        r"""
        Returns the integral of ``self``.

        George De Rham :cite:`de1931analysis` in the 1930\'s  proved that integration provides a natural direct
        quasi-isomorphism of cochain complexes that connects the algebra of differential forms
        (in this context :math:`(A_{PL}(K)`) with the cochain complex :math:`C^*(K)`:

        .. math::

            \oint : A_{PL}(K) \rightarrow C^*(K)

        as follows. Let :math:`\int_{n}` be the linear map:

        .. math::

            \int_{n}: (A_{PL})_{n}^{n} \rightarrow \mathbb{Q}

        by setting

        .. math::
           :nowrap:

            \begin{split}
            \int_{n}t_1^{k_1}\dots t_n^{k_n}dt_1 \wedge \dots \wedge dt_n &= \int_{0}^{1} dt_1\int_{0}^{1-t_1} dt_2 \dots\\
            &\dots \int_{0}^{1-\sum\limits_{1}^{n-1}t_i}t_1^{k_1}\dots t_n^{k_n}dt_n = \\
            &= \frac{k_1!k_2! \dots k_n!}{(k_1+ \dots +k_n+n)!}.
            \end{split}

        This map represents the integration :math:`\int_{\Delta^n}\omega` of an `n`-form
        :math:`\omega \in (A_{PL})^n_n` over the standard `n`-simplex :math:`\Delta^n`.
        Using this map, we can integrate elements of :math:`A_{PL}(K)` as follows: consider a homogeneous
        element :math:`\Phi^n_n \in A^n_{PL}(K_n)`. Its integral is the element of :math:`C^n(K)` determined
        by the integration map:

        .. math::

            \left(\oint(\Phi^n_n)\right)(\sigma) = \int_{n}\Phi^n_n(\sigma),

        for every :math:`\sigma \in K_n`. For homogeneous elements :math:`\Phi^n_m\in A^n_{PL}(K_m)`
        with :math:`n\neq m`, the integral is set to zero (:math:`\left(\oint(\Phi^n_m)\right)(\sigma)=0`).
        Then, the map is extended to all :math:`A_{PL}(K)` by linearity.

        OUTPUT: a vector represented the cochain element.

        EXAMPLES::

            sage: from Sullivan_MM import *
            sage: S2 = simplicial_complexes.Sphere(2)
            sage: K = S2.wedge(S2)
            sage: K.set_immutable()
            sage: W = WhitneyFormAlgebraComplex(K)
            sage: W.inject_variables()
            Getting generators of degree  0 ...
            Getting generators of degree  1 ...
            Getting generators of degree  2 ...
            Defining t0, t1, t2, t3, t4, t5, t6, e1_0, e1_1, e1_2, e1_3, e1_4, e1_5, c1_0, c1_1, c1_2, c1_3, c1_4,
            c1_5, h2_0, h2_1, e2_0, e2_1, e2_2, e2_3, e2_4, e2_5
            sage: e2_1.integral()
            (0, 1, 0, 0, 0, 0, -1, 0)
            sage: W.whitney_form_from_vector(v=e2_1.integral(),dim=2) == e2_1
            True
        """
        if self._vector:
            return self._vector
        W = self.parent()
        assert (self.is_homogeneous() or self.is_zero())
        deg = self.degree()
        cells = W.K._n_cells_sorted(deg)
        if (deg == 0):
            base_ring = QQ
            values = zero_vector(base_ring, len(cells))
            for (i, sigma) in enumerate(cells):
                p = self._components[sigma].reduce(0)
                if p:
                    values[i] = p.leading_coefficient()
            self._vector = vector(base_ring, len(cells), values, sparse=True)
        else:
            values = []
            for sigma in cells:
                c = 0
                if (sigma in self._components.keys()):
                    p = self._components[sigma].reduce(0)
                    c = p.integral()
                values.append(c)
            self._vector = vector(QQ, len(cells), values, sparse=True)
        return self._vector


class MorphismFromQQToAPLK(Morphism):
    def __init__(self, codomain):
        self.constant = codomain.constant
        Morphism.__init__(self, QQ, codomain)

    def _call_(self, x):
        return self.constant(x)


class CohomologyClass(SageObject, CachedRepresentation):
    """
    A class for representing cohomology classes.

    This just has ``_repr_`` and ``_latex_`` methods which put
    brackets around the object's name.

    EXAMPLES::

        sage: from sage.algebras.commutative_dga import CohomologyClass
        sage: CohomologyClass(3)
        [3]
        sage: A.<x,y,z,t> = GradedCommutativeAlgebra(QQ, degrees=(2,2,3,3))
        sage: CohomologyClass(x^2 + 2*y*z, A)
        [2*y*z + x^2]

    TESTS:

    In order for the cache to not confuse objects with the same representation,
    we can pass the parent of the representative as a parameter::

        sage: A.<e1,e2,e3,e4,e5,e6> = GradedCommutativeAlgebra(QQ)
        sage: B1 = A.cdg_algebra({e5:e1*e2,e6:e3*e4})
        sage: B2 = A.cdg_algebra({e5:e1*e2,e6:e1*e2+e3*e4})
        sage: B1.minimal_model()
        Commutative Differential Graded Algebra morphism:
          From: Commutative Differential Graded Algebra with generators ('x1_0', 'x1_1', 'x1_2', 'x1_3', 'y1_0', 'y1_1') in degrees (1, 1, 1, 1, 1, 1) over Rational Field with differential:
           x1_0 --> 0
           x1_1 --> 0
           x1_2 --> 0
           x1_3 --> 0
           y1_0 --> x1_0*x1_1
           y1_1 --> x1_2*x1_3
          To:   Commutative Differential Graded Algebra with generators ('e1', 'e2', 'e3', 'e4', 'e5', 'e6') in degrees (1, 1, 1, 1, 1, 1) over Rational Field with differential:
           e1 --> 0
           e2 --> 0
           e3 --> 0
           e4 --> 0
           e5 --> e1*e2
           e6 --> e3*e4
          Defn: (x1_0, x1_1, x1_2, x1_3, y1_0, y1_1) --> (e1, e2, e3, e4, e5, e6)
        sage: B2.minimal_model()
        Commutative Differential Graded Algebra morphism:
          From: Commutative Differential Graded Algebra with generators ('x1_0', 'x1_1', 'x1_2', 'x1_3', 'y1_0', 'y1_1') in degrees (1, 1, 1, 1, 1, 1) over Rational Field with differential:
           x1_0 --> 0
           x1_1 --> 0
           x1_2 --> 0
           x1_3 --> 0
           y1_0 --> x1_0*x1_1
           y1_1 --> x1_2*x1_3
          To:   Commutative Differential Graded Algebra with generators ('e1', 'e2', 'e3', 'e4', 'e5', 'e6') in degrees (1, 1, 1, 1, 1, 1) over Rational Field with differential:
           e1 --> 0
           e2 --> 0
           e3 --> 0
           e4 --> 0
           e5 --> e1*e2
           e6 --> e1*e2 + e3*e4
          Defn: (x1_0, x1_1, x1_2, x1_3, y1_0, y1_1) --> (e1, e2, e3, e4, e5, -e5 + e6)
    """
    def __init__(self, rep, cdga=None):
        """
        EXAMPLES::

            sage: from sage.algebras.commutative_dga import CohomologyClass
            sage: CohomologyClass(x - 2)                                                # needs sage.symbolic
            [x - 2]
        """
        self._name = str(rep)
        self._rep = rep
        self._cdga = cdga

    def __hash__(self):
        r"""
        TESTS::

            sage: from sage.algebras.commutative_dga import CohomologyClass
            sage: hash(CohomologyClass(sin)) == hash(sin)                               # needs sage.symbolic
            True
        """
        return hash(self._name)

    def _repr_(self):
        """
        EXAMPLES::

            sage: from sage.algebras.commutative_dga import CohomologyClass
            sage: CohomologyClass(sin)                                                  # needs sage.symbolic
            [sin]
        """
        return '[{}]'.format(self._name)

    def _latex_(self):
        r"""
        EXAMPLES::

            sage: from sage.algebras.commutative_dga import CohomologyClass
            sage: latex(CohomologyClass(sin))                                           # needs sage.symbolic
            \left[ \sin \right]
            sage: latex(CohomologyClass(x^2))                                           # needs sage.symbolic
            \left[ x^{2} \right]
        """
        from sage.misc.latex import latex
        return '\\left[ {} \\right]'.format(latex(self._name))

    def representative(self):
        """
        Return the representative of ``self``.

        EXAMPLES::

            sage: from sage.algebras.commutative_dga import CohomologyClass
            sage: x = CohomologyClass(sin)                                              # needs sage.symbolic
            sage: x.representative() == sin                                             # needs sage.symbolic
            True
        """
        return self._rep


class MinimalModel(SageObject, UniqueRepresentation, CachedRepresentation):

    def __init__(self, domain, codomain, names, gens, numerical_invariants=None, base_ring=QQ):

        self._base_ring = base_ring
        self._cdga = domain
        self._aplk_algebra = codomain
        self._imgens = {name: gen for (name, gen) in zip(names, gens)}
        self._hodge_decomps = {}
        self._cohomology = {}
        self._cohomology_raw = {}
        self._harmonic_basis = {}
        self._coexact_basis = {}

        if numerical_invariants:
            self._numerical_invariants = loads(numerical_invariants)
        else:
            self._numerical_invariants = {}

    def numerical_invariants(self):
        return self._numerical_invariants

    # def _coexact_basis_raw(self, deg):
    #     if (not (deg in self._hodge_decomps.keys())):
    #         self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(
    #             deg)
    #     return self.hodge_basis_decomposition_raw[deg]['coexacts']

    # def _exact_basis_raw(self, deg):
    #     if (not (deg in self._hodge_decomps.keys())):
    #         self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(
    #             deg)
    #     return self.hodge_basis_decomposition_raw[deg]['exacts']

    def _gens_from_subspace(self, n, VS):
        A = self.domain()
        B = A.basis(n)
        basis_raw = (VS.lift(VS.basis()[i]) for i in range(VS.dimension()))
        basis = []
        for coeffs in basis_raw:
            element = sum([(c * b) for (c, b) in zip(list(coeffs), B)])
            if (not element.is_zero()):
                basis += [element]
        return basis

    def _get_free_module(self, n, VS):
        A = self.domain()
        M_basis = self._gens_from_subspace(n, VS)
        M_basis_brackets = [CohomologyClass(b, A) for b in M_basis]
        return CombinatorialFreeModule(A.base_ring(), M_basis_brackets, sorting_key=sorting_keys, monomial_reverse=True)

    def _harmonic_basis_raw(self, deg):
        if (not (deg in self._hodge_decomps.keys())):
            self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(deg)
        return self.hodge_basis_decomposition_raw[deg]['harmonics']

    def _repr_(self):
        return f'Minimal Model of the {self._aplk_algebra}'

    # def add_coexacts(self, deg, gens):
    #     if (not (deg in self._coexact_basis.keys())):
    #         self._coexact_basis[deg] = gens
    #     else:
    #         self._coexact_basis[deg].append(gens)
    #
    # def add_harmonics(self, deg, gens):
    #     if (not (deg in self._harmonic_basis.keys())):
    #         self._harmonic_basis[deg] = gens
    #     else:
    #         self._harmonic_basis[deg].update(gens)
    #     self.hodge_subspaces_decomposition_raw(deg, update=True)
    #     return None

    def basis(self, n):
        return self._cdga.basis(n)

    def coboundaries(self, n):
        Y = self.coboundaries_raw(n)
        return self._get_free_module(n, Y)

    def coboundaries_raw(self, n):
        A = self.domain()
        F = A.base_ring()
        if (n == 0):
            return VectorSpace(F, 0, sparse=True)
        if (n == 1):
            V0 = VectorSpace(F, len(A.basis(1)), sparse=True)
            return V0.subspace([])
        D = self.differential(n)
        return D.image()

    def cocycles(self, n):
        X = self.cocycles_raw(n)
        return self._get_free_module(n, X)

    def cocycles_raw(self, n):
        A = self.domain()
        F = A.base_ring()
        if (n == 0):
            return VectorSpace(F, 1, sparse=True)
        D = self.differential(n)
        return D.right_kernel()

    def codomain(self):
        return self._aplk_algebra

    def coexact_gens(self, deg):
        Y = self.hodge_subspaces_decomposition_raw(deg)['coexacts']
        return self._gens_from_subspace(deg, Y)

    def cohomology(self, n):
        H = self.cohomology_raw(n)
        return self._get_free_module(n, H)
    
    def cohomology_raw(self, n):
        return self.domain().cohomology_raw(n)
        return self.hodge_subspaces_decomposition_raw(n)['harmonics']

    def differential(self, deg):
        return self._cdga.differential().differential_matrix(deg).sparse_matrix().T

    def domain(self):
        return self._cdga

    def exact_gens(self, deg):
        X = self.hodge_subspaces_decomposition_raw(deg)['exacts']
        return self._gens_from_subspace(deg, X)

    def harmonic_gens(self, deg):
        H = self.cohomology_raw(deg)
        return self._gens_from_subspace(deg, H)

    def hodge_basis_decomposition_raw(self, deg):
        if (not (deg in self._hodge_decomps.keys())):
            self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(deg)
        return {k: S.basis() for (k, S) in self._hodge_decomps[deg].items()}

    def hodge_subspaces_decomposition_raw(self, deg, update=True):
        if ((deg in self._hodge_decomps.keys()) and (not update)):
            return self._hodge_decomps[deg]
        dif_prev = self.differential((deg - 1))
        dif_curr = self.differential(deg)
        ngens = len(self.basis(deg))
        cobo_mat_prev = self.coboundaries_raw((deg - 1)).basis_matrix()
        if (deg == 0):
            X = zero_matrix(QQ, ngens).row_space()
        elif ((cobo_mat_prev.ncols() == 0) and (dif_prev.T.ncols() == 0)):
            X = zero_matrix(QQ, ngens).row_space()
        else:
            X = (cobo_mat_prev * dif_prev.T).row_space()
        Y = (dif_curr.T * dif_curr).row_space()
        if ((Y.dimension() == 0) and (not (Y.degree() == ngens))):
            Y = zero_matrix(QQ, ngens).row_space()
        H = (X + Y).complement().basis_matrix().sparse_matrix().row_space()
        self._hodge_decomps[deg] = {'harmonics': H, 'exacts': X, 'coexacts': Y}
        return self._hodge_decomps[deg]


    def im_gens(self):
        r"""
        Return the images of the generators of the domain.

        OUTPUT:

        - ``dict`` -- a copy of the dictionary indexed by the generators of the
                     minimal model, and its values are the corresponding images by the morphism :math:'\vaphi'

        .. tab:: Sage

            EXAMPLES::
                sage: S2 = simplicial_sets.Sphere(2)
                sage: W = APLK(S2)
                sage: M = W.minimal_model(i=6)
                sage: M.im_gens()
                {'x2_0': h2_0, 'y3_0': 0}
        """
        return self._imgens.copy()

    def laplacian(self, dim):
        r"""
        Returns the discrete laplacian of dimension ``dim``.

        INPUT:

        - ``dim`` -- the dimension of the cochain module.

        OUTPUT: a tuple of sparse matrices `(L, Ldown, Lup)` corresponding with the laplacian, the
        down laplacian and the up laplacian matrices.

        .. tab:: Sage

            EXAMPLES::


        """

        d_curr = self.differential(dim)
        d_prev = self.differential((dim - 1))
        L_down = (d_prev * d_prev.T)
        L_up = (d_curr.T * d_curr)
        L = (L_down + L_up)
        self._laplacians[dim] = (L, L_down, L_up)
        return (L, L_down, L_up)


    def phi(self, pol):
        B = self._cdga
        if (not (pol.parent() == B)):
            raise ValueError(f'The element {pol} does not belong to {B}')
        W = self._aplk_algebra
        m_gens = B.gens()
        w_gens = {g: self._imgens[str(g)] for g in m_gens}
        w_element = W.zero()
        for (exp, coef) in pol.dict().items():
            term = (coef * W.one())
            for i in range(len(exp)):
                e = exp[i]
                if e:
                    gen = w_gens[m_gens[i]]
                    term *= (gen ** e)
            w_element += term
        return w_element

if (__name__ == '__main__'):
    print('Module loaded', flush=True)
    print()
