from sage.all import *
from sage.structure.parent import Parent
from sage.structure.element import Element
from sage.structure.unique_representation import UniqueRepresentation, CachedRepresentation
from sage.misc.cachefunc import cached_method
from sage.rings.rational_field import QQ
from sage.matrix.constructor import matrix, zero_matrix, identity_matrix
from collections import defaultdict
from itertools import combinations
from sage.structure.richcmp import rich_to_bool, op_EQ, op_NE, op_LT, op_LE, op_GT, op_GE
from sage.algebras.commutative_dga import sorting_keys
import copy
from .hodge import Hodge
from sage.topology.simplicial_set import shrink_simplicial_complex


@cached_method
def parity(p):
    return (sum((1 for (x, px) in enumerate(p) for (y, py) in enumerate(p) if ((x < y) and (px > py)))) % 2)

@cached_method
def sgn_face(face):
    return prod([((- 1) ** i) for i in face])

@cached_method
def sgn_perm(p):
    return ((- 1) ** parity(p))



class CochainAlgebraSSets(Parent, UniqueRepresentation, CachedRepresentation):

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
        Parent.__init__(self, base=base_ring)
        f = MorphismFromQQToCA(self)
        self.register_coercion(f)
        self._gens = {}
        for d in range((K.dimension() + 1)):
            self._gens[d] = {'harmonics': {}, 'exacts': {}, 'coexacts': {}}
        self._hodge = Hodge(K, base_ring=self._base_ring)
        self._hodge_matrix_decompositions = {}
        if precompute_degree:
            print('Precomputing hodge decomposition up to degree',
                  precomp_hodge_deg, flush=True)
            self._hodge_matrix_decompositions = self.hodge_matrix_decompositions(
                precomp_hodge_deg)

    def _degree_factorization(self, deg):
        return [(i, (deg - i)) for i in range(deg) if ((i <= (deg - i)) and (i > 0))]

    def _face_data_SSets(self, dim_from, dim_to):
        upperDims = (dim_to - dim_from)
        faces = list(combinations(range((dim_to + 1)), upperDims))
        data = {}

        def filter_mat(dim):
            all_cells = self.K.all_n_simplices(dim)
            deg_cells_idx = [i for i in range(
                len(all_cells)) if all_cells[i].is_degenerate()]
            filter_matrix = identity_matrix(
                self._base_ring, len(all_cells), sparse=True)
            return filter_matrix.delete_columns(deg_cells_idx)
        from_filter = filter_mat(dim_from)
        to_filter = filter_mat(dim_to)
        for face in faces:
            d = dim_to
            m = identity_matrix(self._base_ring, len(
                self.K.all_n_simplices(d)), sparse=True)
            for f in reversed(face):
                m = (self._face_matrix_SSets(f, d) * m)
                d -= 1
            data[face] = ((from_filter.T * m) * to_filter)
        return data

    def _face_matrix_SSets(self, face, dim):
        S1 = self.K.all_n_simplices((dim - 1))
        S2 = self.K.all_n_simplices(dim)
        face_data = self.K.face_data()
        M = matrix(self._base_ring, len(S1), len(S2), (lambda i, j: (1 if (
            (S1[i] in self.K.faces(S2[j])) and (self.K.face(S2[j], face) == S1[i])) else 0)), sparse=True)
        return M

    def _gens_names_coexacts(self, d):
        return list(self.coexact_basis(d).keys())

    def _gens_names_exacts(self, d):
        return list(self.exact_basis(d).keys())

    def _gens_names_harmonics(self, d):
        return list(self.harmonic_basis(d).keys())

    def _get_basis(self, d, genstype='harmonics'):
        if self._gens[d][genstype]:
            return self._gens[d][genstype]
        if (genstype == 'harmonics'):
            basis_func = self.harmonic_basis
            hodge_basis_func = self._hodge.harmonic_basis
            gLabel = 'h{}_{}'
        elif (genstype == 'exacts'):
            basis_func = self.exact_basis
            hodge_basis_func = self._hodge.exact_basis
            gLabel = 'e{}_{}'
        elif (genstype == 'coexacts'):
            basis_func = self.coexact_basis
            hodge_basis_func = self._hodge.coexact_basis
            gLabel = 'c{}_{}'
        basis = hodge_basis_func(d)
        gens = {gLabel.format(d, i): self.cochain_algebra_element_from_vector(
            h, d) for (i, h) in enumerate(basis) if h}
        self._gens[d][genstype] = gens
        return gens

    def _get_cohomology_dimensions(self):
        dim = self._dimension
        co = self.K.cohomology(base_ring=self._base_ring)
        return vector(self._base_ring, [co[d].rank() for d in range((dim + 1))], sparse=True)

    def _get_coordinates(self, v):
        deg = v.degree()
        hodgeMats = self.hodge_decomposition(deg)
        (h, e, c) = v.hodge_cochain_decomposition()
        H = hodgeMats['H']
        if (not (H.nrows() == 0)):
            hCoords = H.T.solve_right(h)
        else:
            hCoords = zero_vector(self._base_ring, H.ncols())
        X = hodgeMats['X']
        if (not (X.nrows() == 0)):
            xCoords = X.T.solve_right(e)
        else:
            xCoords = zero_vector(self._base_ring, X.ncols())
        Y = hodgeMats['Y']
        if (not (Y.nrows() == 0)):
            yCoords = Y.T.solve_right(c)
        else:
            yCoords = zero_vector(self._base_ring, Y.ncols())
        return {'harmonic_coords': hCoords, 'exact_coords': xCoords, 'coexact_coords': yCoords}

    def _hodge_matrix_decomposition(self, d, verbose=True):
        [H, X, Y] = self._hodge.hodge_decomposition(d)
        self._hodge_matrix_decompositions[d] = {'H': H, 'X': X, 'Y': Y}
        return self._hodge_matrix_decompositions[d]

    def _inject_subset_vars(self, func_basis, d=[], reload=True, verbose=True):
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
            gens.update(func_basis(deg))
        return self._inject_variables(gens, verbose)

    def _inject_variables(self, gens, reload=True, verbose=True):
        from sage.repl.user_globals import set_global, get_globals
        for name in gens.keys():
            if ((not (name in get_globals().keys())) or reload):
                set_global(name, gens[name])
        if verbose:
            print('Defining {}'.format(', '.join(gens.keys())), flush=True)
        return None

    def _nonzero_product_faces(self, dim1, dim2):
        dim = (dim1 + dim2)
        cp = cartesian_product([list(combinations(
            range((dim + 1)), dim2)), list(combinations(range((dim + 1)), dim1))])
        return [c for c in cp if (not set(c[0]).intersection(set(c[1])))]

    def _pack_data(self):
        data = {}
        data['K'] = self.K
        self.gens(verbose=True)
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
        data['hodge'] = self.hodge()
        data['hodge_matrix_decompositions'] = self._hodge_matrix_decompositions
        data['cohomology_mmodels'] = self._cohomology_mmodels
        data['minimalmodels'] = self._minimalmodels
        data['numerical_invariants'] = self._numerical_invariants
        return data

    def _repr_(self):
        return f'Cochain Algebra on {self.K}'

    def base_ring(self):
        return self._base_ring

    def basis(self, d):
        basis = []
        basis += list(self.harmonic_basis(d).values())
        basis += list(self.exact_basis(d).values())
        basis += list(self.coexact_basis(d).values())
        return basis

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
            return span(self._base_ring, zero_vector(self._base_ring, 0))
        basis = [v for v in self._hodge.coexact_basis(n) if v]
        F = self.base_ring()
        V = span(F, basis).span_of_basis(basis)
        self._coboundaries[n] = V
        return V

    def cochain_algebra_element_from_vector(self, v, dim):
        components = self.zero()._components
        components[dim] = v
        return self.element_class()(self, components, dim)

    def cochain_wedge_product(self, c1, dim1, c2, dim2):
        if ((dim1 == 0) and (dim1 == dim2)):
            return c1.pairwise_product(c2)
        dim = (dim1 + dim2)
        face_data1 = self._face_data_SSets(dim1, dim)
        face_data2 = self._face_data_SSets(dim2, dim)
        idDim1 = identity_matrix(self._base_ring, dim1, sparse=True)
        idDim2 = identity_matrix(self._base_ring, dim2, sparse=True)
        w = vector(self._base_ring, len(self.K.n_cells(dim)), sparse=True)
        product_faces = self._nonzero_product_faces(dim1, dim2)
        for (f1, f2) in product_faces:
            if (dim1 == 0):
                f_matrix1 = face_data1[f1].T
                v1 = (f_matrix1 * c1)
                v = c2.pairwise_product(v1)
                w += v
            elif (dim2 == 0):
                f_matrix2 = face_data2[f2].T
                v2 = (f_matrix2 * c2)
                v = c1.pairwise_product(v2)
                w += v
            else:
                faces_orig_order = (list(f1) + list(f2))
                sgn_prod = sgn_perm(faces_orig_order)
                f_matrix1 = face_data1[f1].T
                v1 = (f_matrix1 * c1)
                f_matrix2 = face_data2[f2].T
                v2 = (f_matrix2 * c2)
                v = v1.pairwise_product(v2)
                w += (sgn_prod * v)
        base_ring = self.base_ring()
        coef = base_ring(
            ((factorial(dim1) * factorial(dim2)) / factorial((dim + 1))))
        return (coef * w)

    def cocycles(self, n):
        if (n in self._cocycles.keys()):
            return self._cocycles[n]
        elif (n > self._dimension):
            return span(self._base_ring, zero_vector(self._base_ring, 0))
        H_basis = self._hodge.harmonic_basis(n)
        X_basis = self._hodge.exact_basis(n)
        basis = [v for v in (H_basis + X_basis) if v]
        F = self.base_ring()
        V = span(F, basis).span_of_basis(basis)
        self._cocycles[n] = V
        return V

    def coexact_basis(self, d):
        genstype = 'coexacts'
        return self._get_basis(d, genstype)

    def cohomology(self, n):
        if (n in self._cohomology.keys()):
            return self._cohomology[n]
        elif (n > self._dimension):
            return span(self._base_ring, zero_vector(self._base_ring, 0))
        H_basis = self.harmonic_basis(n)
        H_basis_brackets = [CohomologyClass(
            value, self) for (name, value) in H_basis.items()]
        self._cohomology[n] = CombinatorialFreeModule(self.base_ring(
        ), H_basis_brackets, sorting_key=sorting_keys, monomial_reverse=True)
        return self._cohomology[n]

    def cohomology_raw(self, n):
        if (n in self._cohomology_raw.keys()):
            return self._cohomology_raw[n]
        elif (n > self._dimension):
            return span(self._base_ring, zero_vector(self._base_ring, 0))
        basis = self._hodge.harmonic_basis(n)
        F = self.base_ring()
        V = span(F, basis).span_of_basis(basis)
        self._cohomology_raw[n] = V
        return V

    def constant(self, c):
        components = {}
        baseRing = self.base_ring()
        dim = 0
        ncells = len(self.K._n_cells_sorted(dim))
        components[dim] = vector(baseRing, (ncells * [baseRing(c)]))
        return self.element_class()(self, components, dim)

    def dimension(self):
        return self._dimension

    def element_class(self):
        return CochainAlgebraElementSSets

    def exact_basis(self, d):
        genstype = 'exacts'
        return self._get_basis(d, genstype)

    def gens(self, verbose=True):
        for d in range((self.dimension() + 1)):
            if verbose:
                print('Getting generators of degree ', d, '...', flush=True)
            if (not self._gens[d]['harmonics']):
                self._gens[d]['harmonics'] = self.harmonic_basis(d)
            if (not self._gens[d]['exacts']):
                self._gens[d]['exacts'] = self.exact_basis(d)
            if (not self._gens[d]['coexacts']):
                self._gens[d]['coexacts'] = self.coexact_basis(d)
        return self._gens

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

    def harmonic_basis(self, d):
        genstype = 'harmonics'
        return self._get_basis(d, genstype)

    def hodge(self):
        return self._hodge

    def hodge_decomposition(self, d):
        return self._hodge_matrix_decompositions.get(d, self._hodge_matrix_decomposition(d))

    def hodge_matrix_decompositions(self, deg=0, verbose=True):
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
                self._hodge_matrix_decomposition(d)
        return self._hodge_matrix_decompositions

    def inject_coexact_vars(self, d=[], reload=True, verbose=True):
        return self._inject_subset_vars(self.coexact_basis, d, reload, verbose)

    def inject_exact_vars(self, d=[], reload=True, verbose=True):
        return self._inject_subset_vars(self.exact_basis, d, reload, verbose)

    def inject_harmonic_vars(self, d=[], reload=True, verbose=True):
        return self._inject_subset_vars(self.harmonic_basis, d, reload, verbose)

    def inject_variables(self, reload=True, verbose=True):
        gens = {}
        for (d, components) in self.gens(verbose=verbose).items():
            for (gtype, values) in components.items():
                gens.update(values)
        return self._inject_variables(gens, reload, verbose)

    def load_data(self, data):
        self.K = data['K']
        self._gens = data['gens']
        self._coboundaries = data['coboundaries']
        self._cocycles = data['cocycles']
        self._cohomology_raw = data['cohomology_raw']
        self._cohomology = data['cohomology']
        self._ch_vector = data['ch_vector']
        self._hodge = data['hodge']
        self._hodge_matrix_decompositions = data['hodge_matrix_decompositions']
        self._cohomology_mmodels = data['cohomology_mmodels']
        self._minimalmodels = data['minimalmodels']
        self._numerical_invariants = data['numerical_invariants']
        return None

    def minimal_model(self, i=3, max_iterations=3, partial_result=False, verbose=True, parallelComp=False):
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
                ndf = cndifs.pop(0)
                if ndf:
                    diff[g] = h(ndf)
            newCDGA = A.cdg_algebra(diff)
            new_imgens = tuple(([M._imgens[name]
                               for name in old_names] + list(nimags)))
            if verbose:
                print(f'....Building new Minimal Model...', flush=True)
            return MinimalModel(domain=newCDGA, codomain=self, names=tuple(new_names), gens=new_imgens)

        def extendx(M, degree, verbose=False, parallelComp=False):
            if verbose:
                print(
                    f'Checking surjectivity at degree {degree}...', flush=True)
            CM = M.cohomology_raw(degree)
            CW = self.cohomology_raw(degree)
            ncells = len(self.K.n_cells(degree))
            imagesphico = []
            if parallelComp:
                if verbose:
                    print(
                        f' Parallel Computation of the cohomology images...', flush=True)
                Mcohobasis = M.cohomology(degree).basis().keys()
                zipped_data = [(M, g) for g in Mcohobasis]
                imagesphico = [g[1] for g in imagesPhiCoho(zipped_data)]
            else:
                ncoords = CW.dimension()
                for g in M.cohomology(degree).basis().keys():
                    w = M.phi(g.representative())
                    if (w == 0):
                        h = zero_vector(self._base_ring, ncoords)
                    else:
                        h = w.coordinates()['harmonic_coords']
                        if ((h == 0) and (len(h) < ncoords)):
                            h = zero_vector(self._base_ring, ncoords)
                    imagesphico += [h]
            phico = matrix(self._base_ring, CM.dimension(),
                           list(imagesphico), sparse=True)
            print('phico', flush=True)
            print(phico, flush=True)
            print('##############################################', flush=True)
            print('phico.column_space().complement()', flush=True)
            print(phico.column_space().complement(), flush=True)
            print('##############################################', flush=True)
            print('CW', flush=True)
            print(CW, flush=True)
            if (phico.rank() == 0):
                QI = CW
            else:
                QI = phico.row_space().complement()
            self._numerical_invariants[degree] = [QI.dimension()]
            if (QI.dimension() > 0):
                nnames = [f'x{degree}_{j}' for j in range(QI.dimension())]
                nbasis = []
                for v in QI.basis():
                    vl = CW.lift(QI.lift(v))
                    g = self.cochain_algebra_element_from_vector(vl, degree)
                    nbasis.append(g)
                nimags = nbasis
                ndegrees = [degree for _ in nbasis]
                ndifs = [self.zero() for _ in nimags]
                return extend(M, tuple(ndegrees), tuple(ndifs), tuple(nimags), tuple(nnames), verbose)
            return M

        @parallel(ncpus=Integer(40))
        def imagesPhiCoho(M, pol):
            print(
                f' getting image phi cohomology of the polynomial {pol}', flush=True)
            p_rep = pol.representative()
            w = M.phi(p_rep)
            h = w.coordinates()['harmonic_coords']
            ncoords = M.codomain().cohomology_raw(p_rep.degree()).dimension()
            print(h)
            if ((h == 0) and (len(h) < ncoords)):
                h = zero_vector(self._base_ring, ncoords)
            return h

        @parallel(ncpus=Integer(40))
        def find_preimages(M, pol):
            print(f' finding preimage of the polynomial {pol}', flush=True)
            w = M.phi(pol)
            print(
                f' finding preimage of the Whitney form of {pol}', flush=True)
            return w.get_preimage_exact_component()

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
                    ncoords = CW.dimension()
                    imagesphico = [g[1] for g in imagesPhiCoho(zipped_data)]
                    print(
                        f'elements imagesphico ==> {[g for g in imagesphico]}', flush=True)
                    print(f'', flush=True)
                else:
                    ncoords = CW.dimension()
                    for g in M.cohomology(degree).basis().keys():
                        w = M.phi(g.representative())
                        if (w == 0):
                            h = zero_vector(self._base_ring, ncoords)
                        else:
                            h = w.coordinates()['harmonic_coords']
                            if ((h == 0) and (len(h) < ncoords)):
                                h = zero_vector(self._base_ring, ncoords)
                        imagesphico += [h]
                if (len(imagesphico) == 0):
                    phico = zero_matrix(
                        self._base_ring, CW.dimension(), CM.dimension(), sparse=True)
                else:
                    phico = matrix(self._base_ring, CM.dimension(),
                                   list(imagesphico), sparse=True).T
                phico = matrix(self._base_ring, CM.dimension(),
                               list(imagesphico), sparse=True).T
                phico = phico.right_kernel_matrix().sparse_matrix()
                ker_dim = phico.nrows()
                self._numerical_invariants[(degree - 1)].append(ker_dim)
                if (ker_dim == 0):
                    return M
                if (iteration == (max_iterations - 1)):
                    return (M,)
                ndifs = (phico * CM.basis_matrix()).rows()
                basisdegree = M.basis(degree)
                ndifs = [sum(((basisdegree[j] * g[j])
                             for j in range(len(basisdegree)))) for g in ndifs]
                ncells = len(self.K.n_cells((degree - 1)))
                nimags = []
                if parallelComp:
                    if verbose:
                        print(
                            f' Parallel Computation of the Whitney preimages...', flush=True)
                    nimags = [w[1]
                              for w in find_preimages(((M, g) for g in ndifs))]
                else:
                    for g in ndifs:
                        w = M.phi(g)
                        nimags.append(w.get_preimage_exact_component())
                ndegrees = [(degree - 1) for g in nimags]
                nnames = ['y{}_{}'.format((degree - 1), (j + nnamesy))
                          for j in range(len(nimags))]
                nnamesy += len(nimags)
                M = extend(M, tuple(ndegrees), tuple(ndifs),
                           tuple(nimags), tuple(nnames), verbose)
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
        dim = 0
        ncells = len(self.K._n_cells_sorted(dim))
        components[dim] = vector(self.base_ring(), (ncells * [1]), sparse=True)
        return self.element_class()(self, components, dim)

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
        self._gens = {}
        for d in range((K.dimension() + 1)):
            self._gens[d] = {'harmonics': {}, 'exacts': {}, 'coexacts': {}}
        self._hodge = Hodge(self.K)
        self._hodge_matrix_decompositions = {}
        return None

    def save(self, filename='CAData_temp'):
        data = self._pack_data()
        save(dumps([self, data]), filename)
        return None

    def zero(self, deg=0):
        components = {}
        for dim in range((self._dimension + 1)):
            ncells = len(self.K._n_cells_sorted(dim))
            components[dim] = zero_vector(self.base_ring(), ncells)
        return self.element_class()(self, components, deg)


class CochainAlgebraElementSSets(Element):
    def __init__(self, parent, components, deg):
        Element.__init__(self, parent)
        self._base_ring = parent.base_ring()
        self._components = components
        self._degree = deg
        if (not (isinstance(deg, tuple) or (deg > parent.dimension()))):
            self._homogeneous = True
        else:
            self._homogeneous = False
        if (not (isinstance(deg, tuple) or (deg > parent.dimension()))):
            self._vector = components[deg]
        elif (deg > parent.dimension()):
            self._vector = zero_vector(parent.base_ring(), 0)
        self._hodge_decomp = ()
        self._coords = {}
        self._repr_str = ()

    def __neg__(self):
        return ((- 1) * self)

    def __pow__(self, n):
        return prod((n * [self]))

    def _add_(self, other):
        C = self.parent()
        components = C.zero()._components
        for (dim, v) in self._components.items():
            components[dim] += (v + other._components[dim])
        new_deg = max(self.degree(), other.degree())
        return self.parent().element_class()(self.parent(), components, new_deg)

    def _mul_(self, other):
        C = self.parent()
        element = C.zero()
        for (deg1, c1) in self.homogeneous_components().items():
            for (deg2, c2) in other.homogeneous_components().items():
                deg = (deg1 + deg2)
                if ((deg <= C.dimension()) and c1 and c2):
                    v = C.cochain_wedge_product(
                        c1.to_vector(), deg1, c2.to_vector(), deg2)
                    element += C.cochain_algebra_element_from_vector(v, deg)
        return element

    def _repr_(self):
        if self._repr_str:
            return self._repr_str
        C = self.parent()
        if self.is_zero():
            self._repr_str = '0'
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

        def homogeneous_repr(d, coords):
            h_coords = coords['harmonic_coords']
            e_coords = coords['exact_coords']
            c_coords = coords['coexact_coords']
            harmonic_component = ''
            exact_component = ''
            coexact_component = ''
            if (h_coords != 0):
                h_names = C._gens_names_harmonics(d)
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
                e_names = C._gens_names_exacts(d)
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
                c_names = C._gens_names_coexacts(d)
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
                    coexact_component = (
                        (prefix + c_gcd_str) + coexact_component)
            return ((harmonic_component + exact_component) + coexact_component)
        coords = self.coordinates()
        if self.is_homogeneous():
            d = self.degree()
            self._repr_str = homogeneous_repr(d, coords)
        else:
            self._repr_str = ''
            prefix = ''
            for (d, c) in coords.items():
                self._repr_str += (prefix + homogeneous_repr(d, c))
                prefix = ' + '
        return self._repr_str

    def _richcmp_(self, other, op):
        if (op == op_EQ):
            if (other in self.base_ring()):
                return (self == self.parent().constant(other))
            if (self._components.keys() != other._components.keys()):
                return False
            for (dim, v) in self._components.items():
                if (v != other._components[dim]):
                    return False
            return True
        elif (op == op_NE):
            return (not self._richcmp_(other, op_EQ))
        else:
            raise NotImplementedError(
                'operation not implemented for this element class')

    def _sub_(self, other):
        C = self.parent()
        components = C.zero()._components
        for (dim, v) in self._components.items():
            components[dim] += (v - other._components[dim])
        new_deg = max(self.degree(), other.degree())
        return self.parent().element_class()(self.parent(), components, new_deg)

    def base_ring(self):
        return self._base_ring

    def coordinates(self):
        if self._coords:
            if self.is_homogeneous():
                return self._coords[self.degree()]
            else:
                return self._coords
        else:
            if (self.degree() > self.parent().dimension()):
                self._coords = {'harmonic_coords': (
                ), 'exact_coords': (), 'coexact_coords': ()}
                return self._coords
            for (d, c) in self.homogeneous_components().items():
                self._coords[d] = self.parent()._get_coordinates(c)
            if self.is_homogeneous():
                return self._coords[self.degree()]
            else:
                return self._coords

    def degree(self):
        if self.is_homogeneous():
            return self._degree
        else:
            return max(self.homogeneous_degrees())

    def differential(self):
        C = self.parent()
        hodge = C.hodge()
        if self.is_homogeneous():
            if (self.degree() == C.dimension()):
                new_deg = 0
                return C.zero()
            else:
                deg = self.degree()
                new_deg = (deg + 1)
                components = self._components
                v = self._components[deg]
                diff = hodge.coboundary_operator(deg)
                components[new_deg] = (diff * v)
                components[deg] = zero_vector(self._base_ring, len(v))
        else:
            for dim in reversed((self._components.keys() - 1)):
                diff = hodge.coboundary_operator(dim)
                v = self._components[dim]
                components[(dim + 1)] = (diff * v)
            new_deg = ()
        return self.parent().element_class()(self.parent(), components, new_deg)

    def get_preimage_exact_component(self):
        if self.is_zero():
            return self.parent().zero()
        if (self.degree() == 0):
            return ()
        C = self.parent()
        deg = self.degree()
        (h, e, c) = self.hodge_cochain_decomposition()
        if (e == 0):
            return zero_vector(self._base_ring, len(self._components[(deg - 1)]))
        else:
            hodge = C.hodge()
            preimage = hodge.preimage(e, deg)
            return C.cochain_algebra_element_from_vector(preimage, (deg - 1))
    def hodge_cochain_decomposition(self):
        if self._hodge_decomp:
            return self._hodge_decomp
        hodge = self.parent().hodge()
        v = self.to_vector()
        deg = self.degree()
        self._hodge_decomp = hodge.hodge_cochain_decomposition(v, deg)
        return self._hodge_decomp

    def homogeneous_components(self):
        C = self.parent()
        components = {}
        for (d, v) in self._components.items():
            components[d] = C.cochain_algebra_element_from_vector(v, d)
        return components

    def homogeneous_degrees(self):
        degs = []
        for (d, v) in self._components.items():
            if (not (v == 0)):
                degs.append(d)
        return degs

    def is_closed(self):
        if self.differential().is_zero():
            return True
        return False

    def is_coexact(self):
        (h, e, c) = self.hodge_cochain_decomposition()
        if ((not (c == 0)) and ((h == e) and (e == 0))):
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

    def is_exact(self):
        (h, e, c) = self.hodge_cochain_decomposition()
        if ((not (e == 0)) and ((h == c) and (h == 0))):
            return True
        return False

    def is_harmonic(self):
        (h, e, c) = self.hodge_cochain_decomposition()
        if ((not (h == 0)) and ((e == c) and (e == 0))):
            return True
        return False

    def is_homogeneous(self):
        degs = self.homogeneous_degrees()
        if ((not degs) or (len(degs) == 1)):
            return True
        else:
            return False

    def is_zero(self):
        C = self.parent()
        for v in self._components.values():
            if (not (v == 0)):
                return False
        return True

    def str(self):
        return self._vector

    def to_cochain(self):
        if self.is_zero():
            return {}
        C = self.parent()
        cochain = {}
        for (dim, v) in self._components.items():
            if v:
                cells = C.K._n_cells_sorted(dim)
                cochain[dim] = {k: v for (k, v) in zip(cells, v)}
        return cochain

    def to_vector(self):
        return self._vector



class MorphismFromQQToCA(Morphism):
    def __init__(self, codomain):
        self.constant = codomain.constant
        Morphism.__init__(self, codomain.base_ring(), codomain)

    def _call_(self, x):
        return self.constant(x)


class CohomologyClass(SageObject, CachedRepresentation):
    def __init__(self, rep, cdga=None):
        self._name = str(rep)
        self._rep = rep
        self._cdga = cdga

    def __hash__(self):
        return hash(self._name)

    def _repr_(self):
        return '[{}]'.format(self._name)

    def _latex_(self):
        from sage.misc.latex import latex
        return '\\left[ {} \\right]'.format(latex(self._name))

    def representative(self):
        return self._rep


class MinimalModel(SageObject, UniqueRepresentation, CachedRepresentation):

    def __init__(self, domain, codomain, names, gens):
        self._cdga = domain
        self._C_Algebra = codomain
        self._base_ring = codomain.base_ring()
        self._imgens = {name: gen for (name, gen) in zip(names, gens)}
        self._hodge_decomps = {}
        self._cohomology = {}
        self._cohomology_raw = {}
        self._harmonic_basis = {}
        self._coexact_basis = {}

    def _coexact_basis_raw(self, deg):
        if (not (deg in self._hodge_decomps.keys())):
            self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(
                deg)
        return self.hodge_basis_decomposition_raw[deg]['coexacts']

    def _exact_basis_raw(self, deg):
        if (not (deg in self._hodge_decomps.keys())):
            self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(
                deg)
        return self.hodge_basis_decomposition_raw[deg]['exacts']

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
            self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(
                deg)
        return self.hodge_basis_decomposition_raw[deg]['harmonics']

    def _repr_(self):
        return f'Minimal Model of the {self._C_Algebra}'

    def add_coexacts(self, deg, gens):
        if (not (deg in self._coexact_basis.keys())):
            self._coexact_basis[deg] = gens
        else:
            self._coexact_basis[deg].append(gens)

    def add_harmonics(self, deg, gens):
        if (not (deg in self._harmonic_basis.keys())):
            self._harmonic_basis[deg] = gens
        else:
            self._harmonic_basis[deg].update(gens)
        self.hodge_subspaces_decomposition_raw(deg, update=True)
        return None

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
        return self._C_Algebra

    def coexact_gens(self, deg):
        Y = self.hodge_subspaces_decomposition_raw(deg)['coexacts']
        return self._gens_from_subspace(deg, Y)

    def cohomology(self, n):
        H = self.cohomology_raw(n)
        return self._get_free_module(n, H)

    def cohomology_raw(self, n):
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
            self._hodge_decomps[deg] = self.hodge_subspaces_decomposition_raw(
                deg)
        return {k: S.basis() for (k, S) in self._hodge_decomps[deg].items()}

    def hodge_subspaces_decomposition_raw(self, deg, update=False):
        if ((deg in self._hodge_decomps.keys()) and (not update)):
            return self._hodge_decomps[deg]
        dif_prev = self.differential((deg - 1))
        dif_curr = self.differential(deg)
        ngens = len(self.basis(deg))
        cobo_mat_prev = self.coboundaries_raw((deg - 1)).basis_matrix()
        if (deg == 0):
            X = zero_matrix(self._base_ring, ngens).row_space()
        elif ((cobo_mat_prev.ncols() == 0) and (dif_prev.T.ncols() == 0)):
            X = zero_matrix(self._base_ring, ngens).row_space()
        else:
            X = (cobo_mat_prev * dif_prev.T).row_space()
        Y = (dif_curr.T * dif_curr).row_space()
        if ((Y.dimension() == 0) and (not (Y.degree() == ngens))):
            Y = zero_matrix(self._base_ring, ngens).row_space()
        H = (X + Y).complement().basis_matrix().sparse_matrix().row_space()
        self._hodge_decomps[deg] = {'harmonics': H, 'exacts': X, 'coexacts': Y}
        return self._hodge_decomps[deg]

    def phi(self, pol):
        C = self._C_Algebra
        deg = pol.degree()
        if (deg > C.dimension()):
            return C.zero(deg)
        B = self._cdga
        if (not (pol.parent() == B)):
            raise ValueError(f'The element {pol} does not belong to {B}')
        m_gens = B.gens()
        c_gens = {g: self._imgens[str(g)] for g in m_gens}
        c_element = C.zero(deg)
        for (exp, coef) in pol.dict().items():
            term = C.constant(coef)
            for i in range(len(exp)):
                e = exp[i]
                if e:
                    gen = c_gens[m_gens[i]]
                    term *= (gen ** e)
            c_element += term
        return c_element


if (__name__ == '__main__'):
    print('Module loaded', flush=True)
    print()
