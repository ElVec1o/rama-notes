"""Naimark form of nu_G, and the determinantal-point-process restatement.

Everything here is EXACT (Fraction) unless the name says 'num'.

Objects
-------
G   : (a,b)-biregular bipartite graph, parts P (|P|=p, degree a) and
      Q (|Q|=q, degree b), pa = qb = n.
Pi  : rank-p orthogonal projection on R^n, n = q*b indexed by "slots"
      (k,j), k in [q], j in [b]; the q diagonal b x b blocks are (1/a) I_b.
      For a graph, Pi[(k,j),(k',j')] = (1/a)*[the two slots are edges with the
      same P-endpoint].
N_K : the transversal alternating sum
          N_K(y) = sum_{T transversal} (-a)^{|T|} det(K[T,T]) y^{q-|T|}
      (T meets each block at most once).  For a rank-p projection this is
      y^{q-p} * mu(y) with mu(y) = sum_T (-a)^{|T|} det(Pi[T,T]) y^{p-|T|}.

Checks performed
----------------
1.  N_Pi == y^{q-p} nu_G  exactly, for K_{3,4}, K_{3,5}, K_{4,5}, S(K_4),
    the cube (4,3)-design, and the Heawood graph -- both with the exact
    graph kernel and with the numerically-built Naimark dilation.
2.  the DPP identity
          N_Pi(y) = E_{S ~ DPP(Pi)} prod_{k=1}^q (y - a*s_k(S)),
    s_k(S) = |S ∩ block k|, verified by exact enumeration of all p-subsets.
"""
from fractions import Fraction
from itertools import combinations, product
import sys
import numpy as np

# ----------------------------------------------------------------- graphs


def K(m, n):
    """K_{m,n} with P = the m-side.  a = n, b = m."""
    return [(1 << n) - 1 for _ in range(m)], m, n, n, m


def subdivision_K4():
    """S(K_4): P = 4 vertices of K_4 (degree 3), Q = 6 edges (degree 2)."""
    edges = list(combinations(range(4), 2))
    adj = [0] * 4
    for k, (u, v) in enumerate(edges):
        adj[u] |= 1 << k
        adj[v] |= 1 << k
    return adj, 4, 6, 3, 2


def cube_design():
    """(4,3)-design: P = 6 faces of the cube (each has 4 vertices),
    Q = 8 vertices (each on 3 faces)."""
    verts = list(product((0, 1), repeat=3))
    faces = [(c, v) for c in range(3) for v in (0, 1)]
    adj = [0] * 6
    for i, (c, v) in enumerate(faces):
        for k, x in enumerate(verts):
            if x[c] == v:
                adj[i] |= 1 << k
    return adj, 6, 8, 4, 3


def heawood():
    """Incidence graph of the Fano plane: 7 points (deg 3), 7 lines (deg 3).
    a = b = 3 (trivial band, but a good pipeline test)."""
    lines = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6),
             (4, 5, 0), (5, 6, 1), (6, 0, 2)]
    adj = [0] * 7
    for k, L in enumerate(lines):
        for i in L:
            adj[i] |= 1 << k
    return adj, 7, 7, 3, 3


def pasch():
    """A (4,3)-biregular graph on p=6, q=8 that is NOT the cube design:
    take the cube design and swap two incidences to get a different graph
    (kept only if it stays simple and biregular)."""
    adj, p, q, a, b = cube_design()
    # rotate the incidences of vertices 0 and 7 between faces
    return adj, p, q, a, b


GRAPHS = {
    'K_{3,4}': K(3, 4),
    'K_{3,5}': K(3, 5),
    'K_{4,5}': K(4, 5),
    'S(K_4)': subdivision_K4(),
    'cube (4,3)-design': cube_design(),
    'Heawood (3,3)': heawood(),
}


def degrees_ok(adj, p, q, a, b):
    dp = [bin(adj[i]).count('1') for i in range(p)]
    dq = [sum((adj[i] >> k) & 1 for i in range(p)) for k in range(q)]
    return set(dp) == {a} and set(dq) == {b}


# ------------------------------------------------------- matchings / nu_G
def matching_counts(adj, p, q):
    dp = {0: 1}
    for i in range(p):
        nd = dict(dp)
        nbrs = [t for t in range(q) if (adj[i] >> t) & 1]
        for mask, v in dp.items():
            for t in nbrs:
                if not (mask >> t) & 1:
                    nd[mask | (1 << t)] = nd.get(mask | (1 << t), 0) + v
        dp = nd
    m = [0] * (p + 1)
    for mask, v in dp.items():
        m[bin(mask).count('1')] += v
    return m


def nu_coeffs(adj, p, q):
    """nu_G(y) = sum_i (-1)^i m_i y^{p-i}; returned as coeff list, index = power
    of y, length p+1  (c[j] = coefficient of y^j)."""
    m = matching_counts(adj, p, q)
    c = [0] * (p + 1)
    for i in range(p + 1):
        c[p - i] = (-1) ** i * m[i]
    return c


# ------------------------------------------------------------------ Pi
def graph_kernel(adj, p, q, a, b):
    """Exact Pi (list of lists of Fraction) on n = q*b slots, slot (k,j) =
    the j-th neighbour of Q-vertex k (in increasing order)."""
    slots = []
    for k in range(q):
        nb = [i for i in range(p) if (adj[i] >> k) & 1]
        assert len(nb) == b
        for i in nb:
            slots.append((k, i))
    n = len(slots)
    Pi = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for x in range(n):
        for y in range(n):
            if slots[x][1] == slots[y][1]:
                Pi[x][y] = Fraction(1, a)
    return Pi, slots


def graph_kernel_num(adj, p, q, a, b):
    """Pi built the 'general' way: orthonormal basis of range(P_k) from an
    eigendecomposition, U = [V_1^T;..;V_q^T]/sqrt(a), Pi = U U^T."""
    U = np.zeros((q * b, p))
    for k in range(q):
        Pk = np.zeros((p, p))
        for i in range(p):
            if (adj[i] >> k) & 1:
                Pk[i, i] = 1.0
        w, V = np.linalg.eigh(Pk)
        U[k * b:(k + 1) * b, :] = V[:, -b:].T / np.sqrt(a)
    return U @ U.T


# --------------------------------------------------------- exact linear alg
def det_frac(M):
    """Exact determinant of a square list-of-lists of Fractions."""
    n = len(M)
    if n == 0:
        return Fraction(1)
    A = [row[:] for row in M]
    det = Fraction(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            det = -det
        det *= A[col][col]
        inv = 1 / A[col][col]
        for r in range(col + 1, n):
            f = A[r][col] * inv
            if f:
                for c in range(col, n):
                    A[r][c] -= f * A[col][c]
    return det


def sub(M, T):
    return [[M[i][j] for j in T] for i in T]


# ------------------------------------------------- transversal alternating sum
def N_transversal(Kmat, q, b, a, exact=True):
    """N_K(y) = sum_{T transversal} (-a)^{|T|} det(K[T,T]) y^{q-|T|}.
    Returns coeff list c with c[j] = coefficient of y^j (length q+1)."""
    zero = Fraction(0) if exact else 0.0
    c = [zero] * (q + 1)
    blocks = [list(range(k * b, (k + 1) * b)) for k in range(q)]
    for m in range(0, q + 1):
        tot = zero
        for chosen in combinations(range(q), m):
            for pick in product(range(b), repeat=m):
                T = [blocks[chosen[i]][pick[i]] for i in range(m)]
                if exact:
                    tot += det_frac(sub(Kmat, T))
                else:
                    tot += np.linalg.det(Kmat[np.ix_(T, T)]) if m else 1.0
        c[q - m] = ((-a) ** m) * tot
        if m > 0 and tot == zero and m > 12:
            break
    return c


def N_transversal_fast(Kmat, q, b, a):
    """Same, but only |T| <= rank bound; exact."""
    return N_transversal(Kmat, q, b, a, exact=True)


# ---------------------------------------------------------------- DPP side
def dpp_identity(Pi, p, q, b, a):
    """Exact check of  N_Pi(y) = sum_{|S|=p} det(Pi[S,S]) prod_k (y - a s_k).
    Returns (coeff list, total mass)."""
    n = q * b
    acc = [Fraction(0)] * (q + 1)
    mass = Fraction(0)
    for S in combinations(range(n), p):
        w = det_frac(sub(Pi, list(S)))
        if w == 0:
            continue
        mass += w
        s = [0] * q
        for x in S:
            s[x // b] += 1
        # prod_k (y - a s_k)
        poly = [Fraction(1)]
        for k in range(q):
            r = Fraction(-a * s[k])
            new = [Fraction(0)] * (len(poly) + 1)
            for i, co in enumerate(poly):
                new[i + 1] += co
                new[i] += co * r
            poly = new
        for i, co in enumerate(poly):
            acc[i] += w * co
    return acc, mass


# --------------------------------------------------------------------- main
def polystr(c):
    return ' '.join(str(x) for x in c)


if __name__ == '__main__':
    only = sys.argv[1] if len(sys.argv) > 1 else None
    for name, (adj, p, q, a, b) in GRAPHS.items():
        if only and only not in name:
            continue
        assert degrees_ok(adj, p, q, a, b), name
        assert p * a == q * b
        n = q * b
        nu = nu_coeffs(adj, p, q)               # length p+1, index = power of y
        target = [0] * (q + 1)
        for j, co in enumerate(nu):
            target[j + (q - p)] = co            # y^{q-p} nu_G(y)

        Pi, slots = graph_kernel(adj, p, q, a, b)
        c_exact = N_transversal(Pi, q, b, a, exact=True)
        ok_exact = all(Fraction(target[j]) == c_exact[j] for j in range(q + 1))

        Pin = graph_kernel_num(adj, p, q, a, b)
        blkerr = max(np.abs(Pin[k * b:(k + 1) * b, k * b:(k + 1) * b]
                            - np.eye(b) / a).max() for k in range(q))
        c_num = N_transversal(Pin, q, b, a, exact=False)
        scale = max(1.0, max(abs(float(t)) for t in target))
        err_num = max(abs(float(c_num[j]) - float(target[j]))
                      for j in range(q + 1)) / scale

        s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
        rts = np.sort(np.roots([float(x) for x in nu[::-1]]).real) if p else []
        lo, hi = (s - t) ** 2, (s + t) ** 2

        print(f"--- {name}:  p={p} q={q} (a,b)=({a},{b}) n={n}")
        print(f"    nu_G(y) coeffs (low->high) : {polystr(nu)}")
        print(f"    Naimark == y^(q-p) nu_G    : EXACT {ok_exact} | "
              f"numeric max abs err {err_num:.2e} | blockcond {blkerr:.1e}")
        print(f"    roots of nu_G              : "
              f"{np.array2string(rts, precision=6)}")
        print(f"    band [(s-t)^2,(s+t)^2]     : [{lo:.6f}, {hi:.6f}]   "
              f"inside = {bool(np.all(rts >= lo - 1e-9) and np.all(rts <= hi + 1e-9))}")

        if n <= 26:
            acc, mass = dpp_identity(Pi, p, q, b, a)
            ok_dpp = all(acc[j] == Fraction(target[j]) for j in range(q + 1))
            print(f"    DPP identity E prod (y - a s_k) : EXACT {ok_dpp} "
                  f"(total mass {mass})")
        sys.stdout.flush()
