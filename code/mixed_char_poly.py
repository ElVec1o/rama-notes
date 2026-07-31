"""
mixed_char_poly.py
==================

Mixed characteristic polynomial

    mu[A_1,...,A_q](y) = prod_k (1 - d/dz_k) det(y I + sum_k z_k A_k) |_{z=0}

and tests of the "tree band" conjecture

    CONJECTURE X:  A_1..A_q rank-b PSD on R^p with sum_k A_k = a I
                   ==> every root of mu[A](y) lies in
                       [ (sqrt(a-1)-sqrt(b-1))^2 , (sqrt(a-1)+sqrt(b-1))^2 ].

KEY IDENTITY USED (derived, then validated numerically & symbolically):

  Let m = |S|.  D_S := coeff of prod_{k in S} z_k in det(yI + sum z_k A_k)
  (automatically homogeneous, sitting on y^{p-m}).  Then

      mu[A](y) = sum_{S subset [q]} (-1)^{|S|} D_S y^{p-|S|}

  and by the finite-difference identity
      D_S = [y^{p-m}] sum_{R subset S} (-1)^{m-|R|} det(yI + sum_{k in R} A_k)
  Swapping the order of summation gives the *closed form* we actually compute:

      mu[A](y) = sum_{R subset [q]} (-1)^{|R|}
                     sum_{m=|R|}^{p} C(q-|R|, m-|R|) e_m(M_R) y^{p-m},
      M_R = sum_{k in R} A_k,   e_m = m-th elementary symmetric fn of eigenvalues
                                     (det(yI+M) = sum_m e_m(M) y^{p-m}).

  Cost: 2^q symmetric eigendecompositions of p x p matrices.
"""

import numpy as np
from itertools import combinations
from math import comb


# ----------------------------------------------------------------------
# elementary symmetric functions, computed stably from eigenvalues
# ----------------------------------------------------------------------
def esym_from_eigs(eigs, p):
    """Return e[0..p] with prod_i (y + lam_i) = sum_m e[m] y^(p-m)."""
    e = np.zeros(p + 1, dtype=float)
    e[0] = 1.0
    for lam in eigs:
        e[1:] = e[1:] + lam * e[:-1]
    return e


# ----------------------------------------------------------------------
# main routine: float64
# ----------------------------------------------------------------------
def mixed_char_poly_slow(As):
    """Reference (unvectorised) implementation."""
    q = len(As)
    p = As[0].shape[0]
    mu = np.zeros(p + 1, dtype=float)
    binom = [[comb(n, k) for k in range(p + 1)] for n in range(q + 1)]
    for r in range(q + 1):
        sgn = -1.0 if (r & 1) else 1.0
        for R in combinations(range(q), r):
            if r == 0:
                mu[0] += sgn * 1.0
                continue
            M = As[R[0]].copy()
            for k in R[1:]:
                M += As[k]
            eig = np.linalg.eigvalsh(M)
            e = esym_from_eigs(eig, p)
            brow = binom[q - r]
            for m in range(r, p + 1):
                mu[m] += sgn * brow[m - r] * e[m]
    return mu


_POPCNT_CACHE = {}


def _popcounts(q):
    if q not in _POPCNT_CACHE:
        pc = np.zeros(1 << q, dtype=np.int64)
        for i in range(1, 1 << q):
            pc[i] = pc[i >> 1] + (i & 1)
        _POPCNT_CACHE[q] = pc
    return _POPCNT_CACHE[q]


def mixed_char_poly(As):
    """Vectorised. As: list of q real symmetric p x p arrays (or a (q,p,p) array).
    Returns c[0..p] with mu(y) = sum_m c[m] y^(p-m)."""
    A = np.asarray(As, dtype=float)
    q, p, _ = A.shape
    N = 1 << q
    # all subset sums
    S = np.zeros((N, p, p))
    low = np.zeros(N, dtype=np.int64)
    for mask in range(1, N):
        lb = mask & (-mask)
        k = lb.bit_length() - 1
        S[mask] = S[mask ^ lb] + A[k]
        low[mask] = k
    eig = np.linalg.eigvalsh(S)                      # (N,p) ascending
    E = np.zeros((N, p + 1))
    E[:, 0] = 1.0
    for j in range(p):
        lam = eig[:, j][:, None]
        E[:, 1:] = E[:, 1:] + lam * E[:, :-1]
    pc = _popcounts(q)
    # Sr[r,m] = sum over masks with popcount r of E[mask,m]
    Sr = np.zeros((q + 1, p + 1))
    for m in range(p + 1):
        Sr[:, m] = np.bincount(pc, weights=E[:, m], minlength=q + 1)
    mu = np.zeros(p + 1)
    for r in range(q + 1):
        sgn = -1.0 if (r & 1) else 1.0
        for m in range(r, p + 1):
            mu[m] += sgn * comb(q - r, m - r) * Sr[r, m]
    return mu


# ----------------------------------------------------------------------
# exact rational version (for diagonal / rational families)
# ----------------------------------------------------------------------
def char_coeffs_exact(M):
    """M: list-of-lists of Fractions/ints, p x p symmetric.
    Returns e[0..p] with det(yI+M) = sum_m e[m] y^(p-m), via Faddeev-LeVerrier."""
    from fractions import Fraction
    p = len(M)
    # Faddeev-LeVerrier for det(xI - M) = x^p + c1 x^(p-1) + ... ; c_m = (-1)^m e_m
    Mm = [[Fraction(M[i][j]) for j in range(p)] for i in range(p)]
    Nk = [[Fraction(0) for _ in range(p)] for _ in range(p)]
    cs = [Fraction(1)]
    for k in range(1, p + 1):
        # N = M*Nk + c_{k-1} I
        if k == 1:
            Ak = [[Mm[i][j] for j in range(p)] for i in range(p)]
        else:
            Ak = [[sum(Mm[i][t] * Nk[t][j] for t in range(p)) for j in range(p)]
                  for i in range(p)]
        tr = sum(Ak[i][i] for i in range(p))
        ck = -tr / k
        cs.append(ck)
        Nk = [[Ak[i][j] + (ck if i == j else Fraction(0)) for j in range(p)]
              for i in range(p)]
    # det(xI - M) = sum_k cs[k] x^(p-k), and cs[k] = (-1)^k e_k
    return [cs[k] * (-1) ** k for k in range(p + 1)]


def mixed_char_poly_exact(As):
    """As: list of q p x p matrices as list-of-lists of ints/Fractions.
    Returns exact coefficient list c[0..p], mu(y) = sum c[m] y^(p-m)."""
    from fractions import Fraction
    q = len(As)
    p = len(As[0])
    mu = [Fraction(0)] * (p + 1)
    for r in range(q + 1):
        sgn = -1 if (r & 1) else 1
        for R in combinations(range(q), r):
            if r == 0:
                mu[0] += sgn
                continue
            M = [[sum(Fraction(As[k][i][j]) for k in R) for j in range(p)]
                 for i in range(p)]
            e = char_coeffs_exact(M)
            for m in range(r, p + 1):
                mu[m] += sgn * comb(q - r, m - r) * e[m]
    return mu


# ----------------------------------------------------------------------
# brute-force reference implementation via sympy symbolic differentiation
# (slow; only for tiny p,q -- validates the subset identity on NON-diagonal A)
# ----------------------------------------------------------------------
def mixed_char_poly_sympy(As):
    import sympy as sp
    q = len(As)
    p = len(As[0])
    y = sp.symbols('y')
    zs = sp.symbols('z0:%d' % q)
    M = sp.zeros(p, p)
    for i in range(p):
        M[i, i] += y
    for k in range(q):
        for i in range(p):
            for j in range(p):
                M[i, j] += zs[k] * sp.nsimplify(As[k][i][j])
    D = sp.expand(M.det(method='berkowitz'))
    f = D
    for k in range(q):
        f = sp.expand(f - sp.diff(f, zs[k]))
    f = f.subs({z: 0 for z in zs})
    poly = sp.Poly(sp.expand(f), y)
    c = [sp.Rational(0)] * (p + 1)
    for (deg,), coeff in poly.terms():
        c[p - deg] = sp.Rational(coeff)
    return c


# ----------------------------------------------------------------------
# graph side: matching counts and nu_G
# ----------------------------------------------------------------------
def matching_counts(adjmask, p, q):
    """adjmask[i] = bitmask over Q of neighbours of P-vertex i.
    Returns m[0..p], m[i] = number of i-matchings of the bipartite graph."""
    dp = np.zeros(1 << q, dtype=object)
    dp[0] = 1
    for i in range(p):
        nd = dp.copy()
        nbrs = [t for t in range(q) if (adjmask[i] >> t) & 1]
        for mask in range(1 << q):
            v = dp[mask]
            if v == 0:
                continue
            for t in nbrs:
                if not (mask >> t) & 1:
                    nd[mask | (1 << t)] += v
        dp = nd
    m = [0] * (p + 1)
    for mask in range(1 << q):
        if dp[mask]:
            m[bin(mask).count('1')] += int(dp[mask])
    return m


def nu_from_graph(adjmask, p, q):
    """nu_G(y) = sum_i (-1)^i m(G,i) y^(p-i); returns coeff list c[0..p]."""
    m = matching_counts(adjmask, p, q)
    return [(-1) ** i * m[i] for i in range(p + 1)]


def projections_from_graph(adjmask, p, q):
    """P_k = diag(indicator of N(k)) for k in Q, as p x p integer matrices."""
    Ps = []
    for k in range(q):
        d = [1 if (adjmask[i] >> k) & 1 else 0 for i in range(p)]
        Ps.append([[d[i] if i == j else 0 for j in range(p)] for i in range(p)])
    return Ps


# ----------------------------------------------------------------------
# band
# ----------------------------------------------------------------------
def band(a, b):
    s = np.sqrt(a - 1.0)
    t = np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def roots_of(c):
    r = np.roots(np.asarray(c, dtype=float))
    return np.sort(r.real), np.max(np.abs(r.imag))
