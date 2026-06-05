r"""

"""
    
from sage.misc.cachefunc import cached_method, cached_function
from sage.topology import simplicial_complex, simplicial_set, delta_complex, cubical_complex
from sage.rings.rational_field import QQ
from itertools import combinations
from sage.matrix.constructor import matrix, identity_matrix
from sage.all import *

@cached_method
def parity(p):
    r"""
    
    """
    return (sum((1 for (x, px) in enumerate(p) for (y, py) in enumerate(p) if ((x < y) and (px > py)))) % 2)

@cached_method
def sgn_face(face):
    r"""
    
    """
    return prod([((- 1) ** i) for i in face])

@cached_method
def sgn_perm(p):
    r"""
    
    """
    return ((- 1) ** parity(p))

@cached_method
def _face_data_SComplex(K, dim_from, dim_to, base_ring=QQ):
    r"""
    
    """
    upperDims = (dim_to - dim_from)
    faces = list(combinations(range((dim_to + 1)), upperDims))
    data = {}
    for face in faces:
        d = dim_to
        m = identity_matrix(base_ring, len(K.n_cells(d)), sparse=True)
        for f in reversed(face):
            m = _face_matrix_SComplex(K, f, d, base_ring) * m
            d -= 1
        data[face] = m
    return data
    
@cached_method
def _face_matrix_SComplex(K, face, dim, base_ring=QQ):
    r"""
    
    """
    K1 = K._n_cells_sorted((dim - 1))
    K2 = K._n_cells_sorted(dim)
    M = matrix(base_ring, len(K1), len(K2), (lambda i, j: (1 if (
        (K1[i] in K2[j].faces()) and (K2[j].face(face) == K1[i])) else 0)), sparse=True)
    return M
    
@cached_method
def _face_data_SSets(K, dim_from, dim_to, base_ring = QQ):
    r"""
    
    """
    upperDims = (dim_to - dim_from)
    faces = list(combinations(range((dim_to + 1)), upperDims))
    data = {}

    def filter_mat(dim):
        all_cells = K.all_n_simplices(dim)
        deg_cells_idx = [i for i in range(
            len(all_cells)) if all_cells[i].is_degenerate()]
        filter_matrix = identity_matrix(
            base_ring, len(all_cells), sparse=True)
        return filter_matrix.delete_columns(deg_cells_idx)
    from_filter = filter_mat(dim_from)
    to_filter = filter_mat(dim_to)
    for face in faces:
        d = dim_to
        m = identity_matrix(base_ring, len(
            K.all_n_simplices(d)), sparse=True)
        for f in reversed(face):
            m = _face_matrix_SSets(K, f, d) * m
            d -= 1
        data[face] = ((from_filter.T * m) * to_filter)
    return data

@cached_method
def _face_matrix_SSets(K, face, dim, base_ring = QQ):
    r"""
    
    """
    S1 = K.all_n_simplices((dim - 1))
    S2 = K.all_n_simplices(dim)
    face_data = K.face_data()
    M = matrix(base_ring, len(S1), len(S2), (lambda i, j: (1 if (
        (S1[i] in K.faces(S2[j])) and (K.face(S2[j], face) == S1[i])) else 0)), sparse=True)
    return M

@cached_method
def _face_data(K, dim_from, dim_to, base_ring = QQ):
    r"""
    
    """
    if isinstance(K, simplicial_set.SimplicialSet_finite):
        return _face_data_SSets(K, dim_from, dim_to, base_ring)
    elif isinstance(K,simplicial_complex.SimplicialComplex):
        return _face_data_SComplex(K, dim_from, dim_to, base_ring)
    else:
        raise ValueError(f"{K} is neither a simplicial set nor a simplicial complex")

@cached_method
def _face_matrix(K, face, dim, base_ring = QQ):
    r"""
    
    """
    
    if isinstance(K, simplicial_set.SimplicialSet_finite):
        return _face_matrix_SSets(K, dim_from, dim_to, base_ring)
    elif isinstance(K,simplicial_complex.SimplicialComplex):
        return _face_matrix_SComplex(K, dim_from, dim_to, base_ring)
    else:
        raise ValueError(f"{K} is neither a simplicial set nor a simplicial complex")

def nconnectedFacePaths(degrees):
    dimto = sum(degrees)
    n = len(degrees)
    upperDims = [dimto - p for p in degrees] # face paths of lenght q = dimto - p
    fpaths = {p:tuple(combinations(range(dimto + 1), upperDims[i])) for i,p in enumerate(degrees)}
    npaths = {p:binomial(dimto, p) for p in degrees}
    rawprods = list(cartesian_product([fpaths[p] for p in degrees]))
    prods = []
    for fcandidate in rawprods:
        s = [set(f) for f in fcandidate]
        globalInters = s[0]
        for f in s[1:]:
            globalInters = globalInters.intersection(f)
        if not len(globalInters) == 0:
            continue
        # the intersection of all face paths must be 0
        # we check now the if every pair of p- and q-face paths are is (n-p-q)-connected
        # we check if the intersections form an sphere
        success =  True
        for pair in combinations(range(n), 2):
            s = [set(fcandidate[i]) for i in pair]
            if not len(s[0].intersection(s[1])) == dimto-sum([degrees[i] for i in pair]):
                success=False
                continue
        if success:
            prods += [fcandidate]
    return prods


"""
from Sullivan_MM import *
S = SimplicialAPL(10)
degrees = [2,1,2,1]
n = sum(degrees)
K = simplicial_complexes.Simplex(n)
W = APLK(K)

prods = nconnectedFacePaths(degrees)
wprods = [prod([S.whitney_map(fpath,n) for fpath in multipath]) for multipath in prods]
redws = [w.reduce(0) for w in wprods]
products = {p:w for p,w in zip(prods,redws)}
# for f,w in products.items():
#     print(f"{f} ==> {w}")
from Sullivan_MM.utils import sgn_perm
flatProds = [flatten(p) for p in products]
signs = [sgn_perm(p) for p in flatProds]
theoIntegral = (prod([factorial(d) for d in degrees]))/factorial(n+len(degrees)-1)
print(f"absolute value of each integral ==> {theoIntegral}")

sg = -1 # <== sgn
for i,(f,w) in enumerate(products.items()):
    print(f"sgn {f} ==> {sign(w.integral())}")
    assert signs[i] == sg*sign(w.integral())
    assert abs(theoIntegral) == abs(w.integral())
    print(f"face paths {f} ==> whitney product {w} ==> integral {w.integral()}")
    print(f"face paths {f} ==> theoretical sign {signs[i]} ==> agreement {signs[i] == sign(w.integral())}")
    print(f"abstule value of integral agrees with theoretical formula ==> {abs(theoIntegral) == abs(w.integral())}")
    print()

for i,(f,w) in enumerate(products.items()):
    if not w.is_zero():
        print(f"face paths {f} ==> whitney product {w} ==> integral {w.integral()}")
"""
# face paths ((0, 1), (0, 2), (1, 2)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((0, 1), (0, 3), (1, 3)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((0, 1), (1, 2), (0, 2)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((0, 1), (1, 3), (0, 3)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((0, 2), (0, 1), (1, 2)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((0, 2), (0, 3), (2, 3)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((0, 2), (1, 2), (0, 1)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((0, 2), (2, 3), (0, 3)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((0, 3), (0, 1), (1, 3)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((0, 3), (0, 2), (2, 3)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((0, 3), (1, 3), (0, 1)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((0, 3), (2, 3), (0, 2)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((1, 2), (0, 1), (0, 2)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((1, 2), (0, 2), (0, 1)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((1, 2), (1, 3), (2, 3)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((1, 2), (2, 3), (1, 3)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((1, 3), (0, 1), (0, 3)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((1, 3), (0, 3), (0, 1)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((1, 3), (1, 2), (2, 3)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((1, 3), (2, 3), (1, 2)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((2, 3), (0, 2), (0, 3)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((2, 3), (0, 3), (0, 2)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60
# face paths ((2, 3), (1, 2), (1, 3)) ==> theoretical sign 1 ==> agreement True ==> integral -1/60
# face paths ((2, 3), (1, 3), (1, 2)) ==> theoretical sign -1 ==> agreement True ==> integral 1/60

# from Sullivan_MM import *
# S = SimplicialAPL(10)
# K = simplicial_complexes.Simplex(5)
# W = APLK(K)
# degrees = [1,2,2]
# prods = nconnectedFacePaths(degrees)
# fdata = W._face_data(1,3)
# fpaths = list(fdata.keys())
# prods = []
# for f1 in fpaths:
#     for f2 in fpaths:
#         for f3 in fpaths:
#             s1 = set(f1)
#             s2 = set(f2)
#             s3 = set(f3)
#             if (len(s1.intersection(s2))==1 and len(s1.intersection(s3))==1 and
#                     len(s2.intersection(s3))==1 and len(s1.intersection(s2.intersection(s3))) == 0):
#                 prods += [(f1,f2,f3)]
