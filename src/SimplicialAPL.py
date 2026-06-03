r"""
.. _simplicialapl:

We define now a simplicial object in the category of cochain algebras, called the **simplicial cochain algebra**
:math:`A_{PL} = \{(A_{PL})_n\}_{n \geq 0}` as follows:

* For each :math:`n \geq 0`, the cochain algebra :math:`(A_{PL})_n` is the one defined above.

* The face and degeneration morphisms are the unique cochain algebra morphisms

.. math::

    \begin{array}{rll}
    \partial_i: & (A_{PL})_{n} \rightarrow (A_{PL})_{n-1}, \; & 0 \leq i \leq n, \\
    s_j: & (A_{PL})_{n} \rightarrow (A_{PL})_{n+1}, \; & 0 \leq j \leq n, \\
    \end{array}

satisfying:

.. math::

     \partial_i (t_k) = \left\{\begin{matrix}
     t_k, & k<i \\
     0, & k=i \\
     t_{k-1}, & k>i
     \end{matrix}\right., \; \; \; \; \; \;
     s_j (t_k) = \left\{\begin{matrix}
     t_k, & k<j \\
     t_k+t_{k+1}, & k=j \\
     t_{k+1}, & k>j
     \end{matrix}\right.

The structure of the simplicial cochain algebra :math:`A_{PL}` can be visualized in figure :ref:`simplicial_apln`,
where horizontally is represented the simplicial structure for a given dimension :math:`n` (subscript), and vertically
the graded structure of the algebra (representing the degree :math:`p`, with superscript). This object has a triangular
structure due to the vanishing of the elements when :math:`p>n`.

.. image:: /_static/simplicialapllight.svg
   :align: center
   :class: only-light
   :alt: The structure of the simplicial cochain algebra :math:`A_{PL}`.

.. image:: /_static/simplicialapldark.svg
   :align: center
   :class: only-dark
   :alt: The structure of the simplicial cochain algebra :math:`A_{PL}`.


.. raw:: latex

    \begin{figure}[H]
    \centering
    \begin{tikzcd}
    &  & &  & & \\
    0 & \arrow[l, "\partial_i" above] (A_{PL})^{0}_{0} \arrow[d, "d^{0}_A"] & \arrow[l,  |shift left=1| ] \arrow[l, |shift right=1| , "\partial_i" above] (A_{PL})^{0}_{1}  \arrow[d, "d^{0}_A"] & \arrow[l, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ,"\partial_i" above]   (A_{PL})^{0}_{2} \arrow[d, "d^{0}_A"] & \arrow[l, |shift left=3| ] \arrow[l, |shift left=1| ] \arrow[l, |shift right=1| ] \arrow[l, "\partial_i" above, |shift right=3| ] (A_{PL})^{0}_{3} \arrow[d, "d^{0}_A"] & \arrow[l, |shift left=4| ] \arrow[l, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ] \arrow[l, |shift right=4| ,"\partial_i" above] \cdots  \\
    & 0 & \arrow[l, "\partial_i" {above, yshift=5pt}, |shift left=1| ] \arrow[l, |shift right=1| ] (A_{PL})^{1}_{1}  \arrow[d, "d^{1}_A"] & \arrow[l, "\partial_i" {above, yshift=12pt}, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ]  (A_{PL})^{1}_{2} \arrow[d, "d^{1}_A"] & \arrow[l, |shift left=3| ] \arrow[l, |shift left=1| ] \arrow[l, |shift right=1| ] \arrow[l, "\partial_i" above, |shift right=3| ] (A_{PL})^{1}_{3} \arrow[d, "d^{1}_A"] & \arrow[l, |shift left=4| ] \arrow[l, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ] \arrow[l, |shift right=4| ,"\partial_i" above] \cdots  \\
     &  & 0 & \arrow[l, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ,"\partial_i" above]  (A_{PL})^{2}_{2} \arrow[d, "d^{2}_A"] & \arrow[l, |shift left=3| ] \arrow[l, |shift left=1| ] \arrow[l, |shift right=1| ] \arrow[l, "\partial_i" above, |shift right=3| ] (A_{PL})^{2}_{3} \arrow[d, "d^{2}_A"] & \arrow[l, |shift left=4| ] \arrow[l, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ] \arrow[l, |shift right=4| ,"\partial_i" above]\cdots  \\
     & & & 0 & \arrow[l, |shift left=3| ] \arrow[l, |shift left=1| ] \arrow[l, |shift right=1| ] \arrow[l, "\partial_i" above, |shift right=3| ] (A_{PL})^{3}_{3}  & \arrow[l, |shift left=4| ] \arrow[l, |shift left=2| ] \arrow[l] \arrow[l, |shift right=2| ] \arrow[l, |shift right=4| ,"\partial_i" above] \cdots \\
    \end{tikzcd}
    \caption{The structure of the simplicial cochain algebra $(A_{PL})_n$.}
    \label{simplicial_apln}
    \end{figure}

"""

from sage.structure.unique_representation import UniqueRepresentation, CachedRepresentation
from sage.misc.cachefunc import cached_method, cached_function
from sage.all import *
from sage.algebras.commutative_dga import *
from sage.structure.parent import Parent
from sage.structure.element import Element
from sage.topology.simplicial_set import *
from sage.rings.integer_ring import ZZ
from sage.structure.richcmp import rich_to_bool, op_EQ, op_NE, op_LT, op_LE, op_GT, op_GE
from sage.rings.polynomial.polydict import ETuple
from copy import deepcopy
import itertools
from itertools import combinations
from .AlgebraPL import AplN


class SimplicialAPL(UniqueRepresentation, CachedRepresentation):
    r"""
    The simplicial cochain algebra :math:`A_{PL} = \{(A_{PL})_{n}\}_{n \geq 0}`.
    """

    def __init__(self, n):
        r"""
        Initialization of ``self``
        """
        self.n = n
        self._data = {i: AplN(i) for i in range((n + 1))}

    @cached_method(do_pickle=True)
    def _coface_coeff_endomorphism(self, faces, dim_from, dim_to):
        dom = self.n_th_object(dim_from).base_ring()
        cod = self.n_th_object(dim_to).base_ring()
        if (dim_from > dim_to):
            face_matrix = identity_matrix(cod, len(dom.gens()), sparse=True)
            face_matrix = face_matrix.delete_rows(faces).T
        else:
            face_matrix = identity_matrix(cod, len(cod.gens()), sparse=True)
            face_matrix = face_matrix.delete_rows(faces)
        codgens = vector(cod, cod.gens())
        image = list((face_matrix * codgens))
        return dom.hom(image, cod)

    @cached_method(do_pickle=True)
    def _face(self, dim, deg, face_idx):
        if (not (0 <= face_idx <= dim)):
            raise ValueError(
                f'the face must be an integer in the range {{0,{dim}}}')
        if (not (0 <= deg <= (dim + 1))):
            raise ValueError(
                f'the degree must be an integer in the range {{1,{(dim + 1)}}}')
        baseRingFaceHom = self._face_coeff_endomorphism(dim, face_idx)
        if (deg == 0):
            return {'base_ring_hom': baseRingFaceHom, 'graded_module_hom': {}}
        A = self.n_th_object(dim)
        B = self.n_th_object((dim - 1))
        MA = A._free_graded_module(deg)
        face_matrix = A._graded_face_matrix(face_idx, deg)
        face_matrix = face_matrix.change_ring(QQ)
        idx = A._reduction_indices(face_idx, deg)
        m = identity_matrix(QQ, MA.dimension())
        face_hom = m[idx, : ]
        return {'base_ring_hom': baseRingFaceHom, 'graded_module_hom': face_hom}

    @cached_method(do_pickle=True)
    def _face_coeff_endomorphism(self, dim, face):
        dom = self.n_th_object(dim).base_ring()
        cod = self.n_th_object((dim - 1)).base_ring()
        image = list(cod.gens())
        image.insert(face, 0)
        return dom.hom(image, cod)

    @cached_method(do_pickle=True)
    def _degen_coeff_homomorphism(self, dim, i):
        """
        Description

        """
        dom = self.n_th_object(dim).base_ring()
        cod = self.n_th_object(dim + 1).base_ring()
        image = list(cod.gens())[:i] + [sum(cod.gens()[i:(i + 2)])] + list(cod.gens())[i + 2:]
        return dom.hom(image, cod)

    @cached_method(do_pickle=True)
    def _degen_mon_homomorphism(self, dim, i):
        r"""
        Description

        """
        dom = self.n_th_object(dim)
        cod = self.n_th_object(dim + 1)
        m = identity_matrix(QQ,dim+2)
        m = m.delete_columns([i])
        m[i,i] = 1
        return dom.lift_morphism(m, names=cod.variable_names())

    def __repr__(self):
        r"""
        String representation of ``self``.

        """
        return 'The Simplicial Commutative Differential Graded Algebra (A_{PL})_{%s}' % self.n

    @cached_method(do_pickle=True)
    def affine_map(self, faces, dim, coef=1, normalized=True):
        r"""
        Returns the differential form on :math:`\omega \in (A_{PL})_{dim}` of degree
        ``n = dim-len(faces)`` for which

        .. math::

            \partial_J(\omega)= \frac{coef}{n!} * \mathcal{Whitney}

        with the face-path :math:`J` specified in ``faces``.

        If ``normalized=True``, then :math:`\int \partial_J(\omega) = 1`.

        .. NOTE::

            If ``coef= factorial(n)``, this map is equivalent to :meth:`whitney_map`.

        INPUT:

        - ``faces`` -- tuple; the face path specified by an strictly increasing sequence of non-negative integers

        - ``dim`` -- integer; codomain\'s dimension

        - ``coef`` -- an element of the domain's base_ring (default:1)

        - ``normalized`` -- boolean; if ``True``, returns the normalized differential form

        .. tab:: Sage

            EXAMPLES::

                sage: S = SimplicialAPL(5)
                sage: A = S.n_th_object(4)
                sage: R = A.base_ring()
                sage: A.inject_variables()
                Defining y0, y1, y2, y3, y4
                sage: R.inject_variables()
                Defining t0, t1, t2, t3, t4
                sage: S.affine_map(faces=(1,),dim=5,coef=factorial(4)) == S.whitney_map((1,),5)
                True
                sage: w = S.affine_map(faces=(1,),dim=5,coef=factorial(4))
                sage: [S.face(w,i).reduce(0) for i in range(6)]
                [0, 24*y1*y2*y3*y4, 0, 0, 0, 0]

                sage: coef = t0*t1
                sage: theta = S.affine_map((4,),5,coef)
                sage: [S.face(theta,i).reduce(0) for i in range(6)]
                [0, 0, 0, 0, (-t1^2 - t1*t2 - t1*t3 - t1*t4 + t1)*y1*y2*y3*y4, 0]
                sage: S.face(theta,4).integral()
                1/720

                sage: eta = S.affine_map((4,),5,coef, normalized=True)
                sage: S.face(eta,4).integral()
                1




        """
        dim_from = (dim - len(faces))
        hom = self._coface_coeff_endomorphism(faces, dim_from, dim)
        Apl_from = self.n_th_object(dim_from)
        Apl_to = self.n_th_object(dim)
        R = Apl_from.base_ring()

        w_form =  self.whitney_map(faces, dim)
        if not normalized:
            return hom(coef) * (1/factorial(dim_from))*w_form
        else:
            if (coef in R and not coef in QQ):
                c = Apl_to.zero()
                for (i, m) in enumerate(coef.monomials()):
                    cf = hom(coef.coefficients()[i])
                    num = factorial(dim_from+m.degree())
                    den = factorial(m.degree())*factorial(dim_from)
                    c += ((cf * (num / den)) * hom(m))
            return (c * w_form)

    @cached_method(do_pickle=True)
    def degeneracy(self, p, i):
        r"""
        Returns the degeneracy ``i`` of the differential form ``p``

        .. tab:: Sage

            EXAMPLES::

                sage: from Sullivan_MM import *
                sage: S = SimplicialAPL(10)
                sage: A = AplN(4)
                sage: R = A.base_ring()
                sage: A.inject_variables()
                Defining y0, y1, y2, y3, y4
                sage: R.inject_variables()
                Defining t0, t1, t2, t3, t4
                sage: theta = t1*y0
                sage: S.degeneracy(theta,0)
                t2*y0 + t2*y1

                sage: theta = A(t4)
                sage: S.degeneracy(theta,4)
                t4 + t5

                sage: theta = y4
                sage: S.degeneracy(theta,4)
                y4 + y5

                sage: theta = t0*y3*y4
                sage: S.degeneracy(theta,4)
                t0*y3*y4 + t0*y3*y5
                sage: _ in AplN(5)
                True


        """
        dom = p.parent()
        dim = dom.n
        cod = self.n_th_object(dim + 1)
        homcoef = self._degen_coeff_homomorphism(dim, i)
        hommon = self._degen_mon_homomorphism(dim, i)
        degeneracy = cod.zero()
        for term in p.terms():
            c = term.leading_coefficient()
            m = term.leading_monomial()
            degeneracy += cod(homcoef(c))*hommon(m)
        return degeneracy

    @cached_method(do_pickle=True)
    def face(self, p, i):
        r"""
        Returns the face ``i`` of the differential form ``p``

        .. tab:: Sage

            EXAMPLES::

                sage: S = SimplicialAPL(10)
                sage: A = S.n_th_object(4)
                sage: R = A.base_ring()
                sage: A.inject_variables()
                Defining y0, y1, y2, y3, y4
                sage: R.inject_variables()
                Defining t0, t1, t2, t3, t4
                sage: w = t0*y1*y3
                sage: S.face(w,0)
                0
                sage: S.face(w,2)
                t0*y1*y2
                sage: _ in S.n_th_object(3)
                True
                sage: S.face(w,4)
                t0*y1*y3
                sage: _ in S.n_th_object(3)
                True

        """
        A = p.parent()
        dim = A.n
        if (not (0 <= i <= dim)):
            raise ValueError(
                f'the face must be an integer in the range {{0,{dim}}}')
        if (not p):
            return self.n_th_object((dim - 1)).zero()
        deg = A(p).degree()
        if (not (0 <= deg <= (dim + 1))):
            raise ValueError(
                f'the degree must be an integer in the range {{1,{(dim + 1)}}}')
        hom = self._face(dim, deg, i)
        baseRingFaceHom = hom['base_ring_hom']
        B = self.n_th_object((dim - 1))
        if (A(p).degree() == 0):
            return B(baseRingFaceHom(A(p).leading_coefficient()))
        MB = B._free_graded_module(deg)
        face_hom = hom['graded_module_hom']
        new_element = B.zero()
        for term in p.terms():
            c = term.leading_coefficient()
            m = term.leading_monomial()
            v = m._to_graded_module().to_vector()
            vb = MB.from_vector((face_hom * v))
            new_coeff = baseRingFaceHom(c)
            new_monomial = B._from_graded_module(deg, vb)
            new_element += (new_coeff * new_monomial)
        return new_element

    @cached_method(do_pickle=True)
    def n_th_object(self, n):
        r"""
        Returns the ``n``-simplex of ``self``.

        .. tab:: Sage

            EXAMPLES::

                    sage: S = SimplicialAPL(10)
                    sage: S.n_th_object(5)
                    The Commutative Differential Graded Algebra (A_{PL})_{5} defined as
                    the  tensor product of the Polynomial Ring QQ<t_{0},...,t_{5}> with
                    the Exterior Algebra generated by QQ<y_{0},...,y_{5}>.

                    The degrees of the generators are:

                        deg(t_i)=0
                        deg(y_j)=1

                    The differential 'd' is defined as:

                        d(t_i)=y_i
                        d(y_j)=0

        .. tab:: Python code

            EXAMPLES::

                S = SimplicialAPL(10)
                S.n_th_object(5)



        """
        return self._data[n]

    @cached_method(do_pickle=True)
    def whitney_map(self, faces, dim):
        r"""
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
                    & (t_0,\dots, t_p) & \rightarrow & (t_{i_0},\dots, t_{i_p})
                \end{array}

        .. tab:: Sage

            EXAMPLES::

            This example ilustrates the locallity property of Whitney forms::

                    sage: S = SimplicialAPL(10)
                    sage: A3 = S.n_th_object(3)
                    sage: w1 = S.whitney_map((1,), 4)
                    sage: w1
                    -6*t4*y0*y2*y3 + 6*t3*y0*y2*y4 - 6*t2*y0*y3*y4 + 6*t0*y2*y3*y4
                    sage: S.face(w1,0)
                    0
                    sage: S.face(w1,1)
                    -6*t3*y0*y1*y2 + 6*t2*y0*y1*y3 - 6*t1*y0*y2*y3 + 6*t0*y1*y2*y3
                    sage: S.face(w1,2)
                    0
                    sage: S.face(w1,3)
                    0
                    sage: S.face(w1,4)
                    0
                    sage: S.face(w1,1) == A3.whitney_form()
                    True

            This example ilustrates the Whitney map along a face-path of length 2::

                    sage: w23 = S.whitney_map((2,3),5)
                    sage: w23
                    -6*t5*y0*y1*y4 + 6*t4*y0*y1*y5 - 6*t1*y0*y4*y5 + 6*t0*y1*y4*y5
                    sage: S.face(S.face(w23,3),2) == A3.whitney_form()
                    True

        """
        Apl = self.n_th_object(dim)
        n = Apl.n
        R = Apl.base_ring()
        rgens = list(R.gens())
        w_form = Apl.zero()
        gens = list(Apl.gens())
        for face in reversed(faces):
            rgens.pop(face)
            gens.pop(face)
        for i in range(len(rgens)):
            y_gens = copy.deepcopy(gens)
            y_gens.pop(i)
            w_form += ((((- 1) ** i) * rgens[i]) * prod(y_gens))
        return (factorial((dim - len(faces))) * w_form)


