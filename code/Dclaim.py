"""Dclaim.py -- INDEPENDENT re-derivation and test of

    (D)   mu[P_1..P_q]  =  psi_0  box_p  rho    with rho REAL-ROOTED,
          psi_0(x) = x^{p - p/b} (x - b)^{p/b}          [needs b | p].

Nothing here imports the earlier deconvolution code path: box_p, psi_0, the
deconvolution and the real-rootedness certificate are all rebuilt from the
definitions, so that agreement with the earlier files is evidence and not
tautology.

CONVENTIONS
-----------
A monic degree-p polynomial is a coefficient list  c[0..p], HIGHEST POWER FIRST:
    f(x) = sum_i c[i] x^{p-i},  c[0] = 1.
All arithmetic is over Fraction unless a name says 'float'.

box_p (MSS finite free additive convolution), from the definition
    (f box_p g)(x) = sum_k x^{p-k} sum_{i+j=k} (p-i)!(p-j)!/(p!(p-k)!) c_i(f) c_j(g).

mu (MSS mixed characteristic polynomial):  for PSD A_1..A_q,
    mu[A](x) = prod_k (1 - d/dz_k) det( x I + sum_k z_k A_k ) |_{z=0}
             = sum_{T subset [q]} (-1)^{|T|} [prod_{k in T} z_k] det(xI + sum z_k A_k).
For a COMMUTING (0/1-diagonal) family this is evaluated exactly by the
rank-one randomisation
    mu(x) = E prod_{i=1}^p ( x - b d_i ),
where each block k independently picks one of its b elements uniformly and
d_i counts how many blocks picked i.  (E w_k w_k^T = P_k, so MSS applies.)
That formula is cross-checked below against a direct multilinear expansion.
"""
from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial
import sys

import numpy as np

# ----------------------------------------------------------------- box_p
def boxp(f, g, p):
    """finite free convolution, coefficient lists highest-power-first."""
    out = [Fraction(0)] * (p + 1)
    for k in range(p + 1):
        s = Fraction(0)
        for i in range(k + 1):
            j = k - i
            if j > p or i > p:
                continue
            s += (Fraction(factorial(p - i) * factorial(p - j),
                           factorial(p) * factorial(p - k))
                  * Fraction(f[i]) * Fraction(g[j]))
        out[k] = s
    return out


def boxp_pow(f, p, n):
    r = [Fraction(1)] + [Fraction(0)] * p          # x^p is the box_p identity
    for _ in range(n):
        r = boxp(r, f, p)
    return r


# --------------------------------------------------- box_p as a linear map
def boxp_matrix(f, p):
    """The matrix M with (f box_p g) = M g, in the highest-power-first basis."""
    M = [[Fraction(0)] * (p + 1) for _ in range(p + 1)]
    for k in range(p + 1):
        for j in range(k + 1):
            i = k - j
            M[k][j] = (Fraction(factorial(p - i) * factorial(p - j),
                                factorial(p) * factorial(p - k)) * Fraction(f[i]))
    return M


def deconv(mu, f, p):
    """the unique monic g with f box_p g = mu.  M is lower triangular with
    diagonal entries  (p-k)!(p-0)!/(p!(p-k)!) * f_0 = 1, so it is unimodular
    and the solve is exact forward substitution."""
    M = boxp_matrix(f, p)
    g = [Fraction(0)] * (p + 1)
    for k in range(p + 1):
        s = Fraction(mu[k])
        for j in range(k):
            s -= M[k][j] * g[j]
        assert M[k][k] == 1, M[k][k]
        g[k] = s
    return g


# ------------------------------------------------------------- polynomials
def poly_from_roots(roots):
    """monic prod (x - r), coefficients highest power first."""
    c = [Fraction(1)]
    for r in roots:
        nc = [Fraction(0)] * (len(c) + 1)
        for i, co in enumerate(c):
            nc[i] += co                                # x * co * x^{...}
            nc[i + 1] -= Fraction(r) * co
        c = nc
    return c


def psi0(p, b, m=None):
    """char poly of b*Q, Q an orthogonal projection of rank m (default p/b)."""
    if m is None:
        assert p % b == 0, (p, b)
        m = p // b
    return poly_from_roots([Fraction(0)] * (p - m) + [Fraction(b)] * m)


# ------------------------------------------ EXACT real-rootedness (Sturm)
def _polydiv(A, B):
    """A, B coefficient lists highest-power-first over Q.  Return remainder."""
    A = [Fraction(x) for x in A]
    B = [Fraction(x) for x in B]
    while A and A[0] == 0:
        A = A[1:]
    while B and B[0] == 0:
        B = B[1:]
    if not B:
        raise ZeroDivisionError
    while len(A) >= len(B) and A:
        f = A[0] / B[0]
        for i in range(len(B)):
            A[i] -= f * B[i]
        A = A[1:]
        while A and A[0] == 0:
            A = A[1:]
    return A


def _deriv(A):
    n = len(A) - 1
    return [Fraction(A[i]) * (n - i) for i in range(n)]


def _gcd_poly(A, B):
    A, B = [Fraction(x) for x in A], [Fraction(x) for x in B]
    while True:
        while B and B[0] == 0:
            B = B[1:]
        if not B:
            break
        A, B = B, _polydiv(A, B)
    return [x / A[0] for x in A] if A else A


def squarefree(A):
    g = _gcd_poly(A, _deriv(A))
    if len(g) <= 1:
        return [Fraction(x) for x in A]
    # A / g by long division
    A = [Fraction(x) for x in A]
    out = []
    R = A[:]
    while len(R) >= len(g):
        f = R[0] / g[0]
        out.append(f)
        for i in range(len(g)):
            R[i] -= f * g[i]
        R = R[1:]
    return out


def sturm_real_root_count(A):
    """EXACT number of DISTINCT real roots of A (over Q), via Sturm's theorem
    on the square-free part.  Returns (n_distinct_real, deg_squarefree)."""
    P = squarefree(A)
    n = len(P) - 1
    if n <= 0:
        return 0, 0
    chain = [P, _deriv(P)]
    while True:
        r = _polydiv(chain[-2], chain[-1])
        if not r:
            break
        chain.append([-x for x in r])
    def signs_at_inf(sgn):
        out = []
        for c in chain:
            d = len(c) - 1
            out.append(int(np.sign(float(c[0]))) * (1 if sgn > 0 else (-1) ** d))
        return out
    def var(s):
        s = [x for x in s if x != 0]
        return sum(1 for i in range(len(s) - 1) if s[i] * s[i + 1] < 0)
    return var(signs_at_inf(-1)) - var(signs_at_inf(+1)), n


def is_real_rooted_exact(A):
    """True iff every root of the monic A is real (counted without multiplicity
    by Sturm on the square-free part -- deg(sqfree) distinct real roots means
    all roots real)."""
    nreal, nsq = sturm_real_root_count(A)
    return nreal == nsq, nreal, nsq


def maximag_float(A, dps=None):
    """max |Im(root)| / max|root| at high precision (mpmath)."""
    import mpmath as mp
    d = len(A) - 1
    if dps is None:
        dps = max(60, 6 * d)
    with mp.workdps(dps):
        c = [mp.mpf(Fraction(x).numerator) / mp.mpf(Fraction(x).denominator)
             for x in A]
        r = mp.polyroots(c, maxsteps=400, extraprec=60 * d)
        sc = max(1.0, max(abs(float(mp.re(z))) for z in r))
        return max(abs(float(mp.im(z))) for z in r) / sc, \
               sorted(float(mp.re(z)) for z in r)


# ------------------------------------------------------- commuting families
def mu_commuting_exact(blocks, p, b):
    """EXACT mu for the commuting family P_k = diag(1_{blocks[k]}).
    blocks[k] is a b-subset of range(p); every i in range(p) must lie in
    exactly a of them.  Uses  mu(x) = E prod_i (x - b d_i)  over the b^q
    independent uniform choices (one element per block)."""
    q = len(blocks)
    tot = [Fraction(0)] * (p + 1)
    w = Fraction(1, b ** q)
    for choice in product(*blocks):
        d = [0] * p
        for i in choice:
            d[i] += 1
        c = poly_from_roots([Fraction(b * d[i]) for i in range(p)])
        for i in range(p + 1):
            tot[i] += w * c[i]
    return tot


def mu_multilinear_exact(A_list, p):
    """EXACT mu from the DEFINITION, for arbitrary symmetric rational A_k:
       mu(x) = sum_{T} (-1)^{|T|} [prod_{k in T} z_k] det(xI + sum z_k A_k).
    The bracket is a sum over which rows take which A_k: for |T| = t,
       [prod_{k in T} z_k] det(xI + sum z_k A_k)
         = sum over injections/row-choices; computed here by expanding the
    determinant of  xI + sum_{k in T} z_k A_k  multilinearly in rows.
    Implemented as: coefficient of prod z_k = sum over ordered assignments of
    the t matrices to t distinct rows.  Uses generalised matrix functions --
    only used for small p as a cross-check."""
    q = len(A_list)
    out = [Fraction(0)] * (p + 1)
    for t in range(0, min(q, p) + 1):
        for T in combinations(range(q), t):
            # coefficient of z_{T} in det(xI + sum_{k in T} z_k A_k):
            # = sum over t-subsets S of rows, |S| = t, of the "mixed" term.
            # det(M) with M = xI + sum z_k A_k.  Expand: choose for each row
            # either the (xI) part or one A_k part; each A_k used once.
            s = [Fraction(0)] * (p + 1)
            for S in combinations(range(p), t):
                for perm in _perms(t):
                    # rows S[i] take matrix A_{T[perm[i]]}, other rows take xI
                    rest = [i for i in range(p) if i not in S]
                    # determinant expansion: det of the matrix whose rows in S
                    # come from A's and rows outside S come from x*e_i.
                    # = sum over which columns the S-rows use ... do it by
                    # building the matrix symbolically in x is easier: the
                    # non-S rows are x*e_i, so the determinant reduces to
                    # x^{p-t} * det( A-rows restricted to columns S ) * sign
                    sub = [[Fraction(A_list[T[perm[i]]][S[i]][S[j]])
                            for j in range(t)] for i in range(t)]
                    s[t] += _det(sub)      # x^{p-t} * complementary minor
                    del rest
            for i in range(p + 1):
                out[i] += Fraction((-1) ** t) * s[i]
    return out


def _perms(t):
    from itertools import permutations
    return list(permutations(range(t)))


def _det(M):
    n = len(M)
    if n == 0:
        return Fraction(1)
    A = [row[:] for row in M]
    det = Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det *= A[c][c]
        inv = 1 / A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] * inv
            if f:
                for j in range(c, n):
                    A[r][j] -= f * A[c][j]
    return det


# ------------------------------------------------------------- graph zoo
def graph_blocks(edges, p):
    """b = 2 family from a graph: block k = the two endpoints of edge k."""
    return [tuple(e) for e in edges], p, len(edges), 2


def K4():
    return list(combinations(range(4), 2)), 4


def K33():
    return [(i, 3 + j) for i in range(3) for j in range(3)], 6


def Q3():
    V = list(product((0, 1), repeat=3))
    idx = {v: i for i, v in enumerate(V)}
    E = []
    for v in V:
        for c in range(3):
            w = list(v)
            w[c] ^= 1
            w = tuple(w)
            if idx[v] < idx[w]:
                E.append((idx[v], idx[w]))
    return E, 8


def petersen():
    # outer 0..4 cycle, inner 5..9 pentagram, spokes i -- i+5
    E = [(i, (i + 1) % 5) for i in range(5)]
    E += [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    E += [(i, 5 + i) for i in range(5)]
    return E, 10


def K5():
    return list(combinations(range(5), 2)), 5      # p odd: b does not divide p


def cube_design():
    """p = 6 faces, q = 8 vertices, a = 4, b = 3."""
    verts = list(product((0, 1), repeat=3))
    faces = [(c, v) for c in range(3) for v in (0, 1)]
    blocks = []
    for k, x in enumerate(verts):
        blocks.append(tuple(i for i, (c, v) in enumerate(faces) if x[c] == v))
    return blocks, 6, 8, 4, 3


def Kmn(m, n):
    """K_{m,n} with P = m-side (deg n), Q = n-side (deg m): a = n, b = m."""
    return [tuple(range(m)) for _ in range(n)], m, n, n, m


def report_row(name, p, q, a, b, mu, m=None, verbose=True):
    f = psi0(p, b, m)
    rho = deconv(mu, f, p)
    back = boxp(f, rho, p)
    ok_back = all(Fraction(back[i]) == Fraction(mu[i]) for i in range(p + 1))
    rr, nreal, nsq = is_real_rooted_exact(rho)
    mi, rts = maximag_float(rho)
    if verbose:
        print("  %-22s (p,q,a,b)=(%2d,%2d,%d,%d)  m=%-2s reconv_exact=%s "
              "REAL-ROOTED=%-5s  (%d/%d distinct real)  max|Im|/scale=%.3e"
              % (name, p, q, a, b, m if m is not None else p // b, ok_back,
                 rr, nreal, nsq, mi))
    return dict(name=name, p=p, q=q, a=a, b=b, rho=rho, rr=rr, maximag=mi,
                roots=rts, ok_back=ok_back)


# --------------------------------------------------------------- self tests
def selftest():
    print("=" * 96)
    print("SELF-TESTS of the rebuilt box_p / deconv / Sturm stack")
    print("=" * 96)
    rng = np.random.default_rng(0)
    # 1. box_p against the Haar definition E_U chi[A + U B U^T] (Monte Carlo)
    p = 4
    A = np.diag([1.0, 2.0, -1.0, 0.5])
    B = np.diag([0.3, -0.7, 2.0, 1.0])
    acc = np.zeros(p + 1)
    N = 40000
    for _ in range(N):
        X = rng.standard_normal((p, p))
        U, _ = np.linalg.qr(X)
        acc += np.poly(A + U @ B @ U.T)
    acc /= N
    cf = boxp(poly_from_roots([Fraction(x).limit_denominator(10**6)
                               for x in np.diag(A)]),
              poly_from_roots([Fraction(x).limit_denominator(10**6)
                               for x in np.diag(B)]), p)
    print("  [1] box_p vs Haar Monte-Carlo (N=%d): max abs dev = %.4f  (MC noise)"
          % (N, max(abs(float(cf[i]) - acc[i]) for i in range(p + 1))))
    # 2. deconv inverts boxp exactly
    f = poly_from_roots([Fraction(i) for i in (0, 1, 2, 3, 4)])
    g = poly_from_roots([Fraction(i) for i in (-1, 0, 2, 5, 7)])
    h = boxp(f, g, 5)
    print("  [2] deconv(f box g, f) == g exactly:", deconv(h, f, 5) == g)
    # 3. x^p is the identity
    print("  [3] f box x^p == f exactly:",
          boxp(f, [Fraction(1)] + [Fraction(0)] * 5, 5) == f)
    # 4. shift: (x-c)^p box f = f(x-c)
    c = Fraction(3)
    sh = boxp(poly_from_roots([c] * 5), g, 5)
    gshift = poly_from_roots([Fraction(r) + c for r in (-1, 0, 2, 5, 7)])
    print("  [4] (x-c)^p box f == f(x-c) exactly:", sh == gshift)
    # 5. Sturm
    print("  [5] Sturm on (x-1)(x-2)(x-3):",
          is_real_rooted_exact(poly_from_roots([Fraction(1), Fraction(2),
                                                Fraction(3)])))
    print("      Sturm on (x^2+1)(x-1):",
          is_real_rooted_exact([Fraction(1), Fraction(-1), Fraction(1),
                                Fraction(-1)]))
    print("      Sturm on (x-1)^3       :",
          is_real_rooted_exact(poly_from_roots([Fraction(1)] * 3)))
    # 6. commuting mu vs the multilinear definition, small case
    edges, p = K4()
    blocks = [tuple(e) for e in edges]
    mu1 = mu_commuting_exact(blocks, p, 2)
    A_list = []
    for blk in blocks:
        M = [[Fraction(0)] * p for _ in range(p)]
        for i in blk:
            M[i][i] = Fraction(1)
        A_list.append(M)
    mu2 = mu_multilinear_exact(A_list, p)
    print("  [6] mu(S(K_4)) randomisation == multilinear definition:",
          mu1 == mu2)
    print("      mu =", [str(x) for x in mu1])
    # 7. against the project's own mcp() (float)
    sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
    from mcp2 import mcp                                                   # noqa
    P = np.zeros((len(blocks), p, p))
    for k, blk in enumerate(blocks):
        for i in blk:
            P[k, i, i] = 1.0
    ref = mcp(P)
    print("      vs project mcp():  max dev = %.2e"
          % max(abs(float(mu1[i]) - ref[i]) for i in range(p + 1)))
    print()


if __name__ == '__main__':
    selftest()
    print("=" * 96)
    print("CLAIM (D):  rho = mu deconv psi_0,  psi_0 = x^{p-p/b}(x-b)^{p/b}")
    print("=" * 96)
    for nm, (E, p) in [('S(K_4)  [K_4]', K4()), ('K_{3,3}', K33()),
                       ('Q_3 (cube)', Q3()), ('Petersen', petersen())]:
        blocks = [tuple(e) for e in E]
        q = len(blocks)
        a = 2 * q // p
        mu = mu_commuting_exact(blocks, p, 2)
        report_row(nm, p, q, a, 2, mu)
    print()
    blocks, p, q, a, b = cube_design()
    report_row('cube (4,3)-design', p, q, a, b, mu_commuting_exact(blocks, p, b))
    blocks, p, q, a, b = Kmn(3, 4)
    report_row('K_{3,4}', p, q, a, b, mu_commuting_exact(blocks, p, b))
