"""ineq2_ladder.py -- the moment / Newton ladder for INEQ-2 at b = 2.

CONTEXT.  P_1..P_q rank-2 orthogonal projections on R^p (or C^p), sum_k P_k = a I,
q = pa/2.  mu = MSS mixed characteristic polynomial.  Established earlier in this
project (dpp_rep.py, profile_pgf.py):

    y^{q-p} mu(y) = E_S prod_k (y - a s_k),   S ~ DPP(Pi),  s_k = |S cap B_k|,
    mu(y) = (y-a)^p Psi(theta(y)),  theta = 1 - a^2/(y-a)^2,  Psi(u) = E u^{n_2},
    n_2 = #{k : s_k = 2} = sum_i Bern(pi_i)  (independent; forced by real-rootedness),
    lambda_max = a(1 + sqrt(pi_max)),   lambda_min = a(1 - sqrt(pi_max)).

TARGET   (INEQ-2)   pi_max <= 4(a-1)/a^2.

WHAT THIS FILE ESTABLISHES (all verified below, exactly where possible).

  (L1)  e_r(pi) = E binom(n_2, r) = sum_{|T|=r} det Pi[B_T].          [B_T = union of blocks]
  (L2)  BASIS-FREE FORM.  a^{2r} det Pi[B_T] = e_{2r}( sum_{k in T} P_k ),
        e_m(A) = m-th elementary symmetric function of the spectrum of A
              = sum of the m x m principal minors of A.
        Hence, with   M_r := a^{2r} e_r(pi) = sum_{|T|=r} e_{2r}( sum_{k in T} P_k ),

  (L3)  THE MATCHING FORM.     mu(x + a) = sum_{r=0}^{p/2} (-1)^r M_r x^{p-2r},
        M_r >= 0, M_0 = 1, M_1 = q, and mu's roots are symmetric about a.
        The roots of mu(x+a) are  +- a sqrt(pi_i), together with p - 2N zeros.
        In the commuting (graph) case M_r = # of r-matchings of the multigraph H
        whose edges are the blocks; INEQ-2 is then EXACTLY Heilmann-Lieb.

  (L4)  M_1 = q  (i.e. E n_2 = q/a^2 = p/(2a)).
  (L5)  sum_{j != k} ||Pi[B_j,B_k]||_F^2 = 2 q (a-1)/a^2   (the "degree a" identity).
  (L6)  M_2 = C(q,2) - q(a-1) + a^4 sum_{j<k} |det(Pi[B_j,B_k])|^2 ;
        equivalently   sum_i pi_i^2 = q(2a-1)/a^4 - 2 sum_{j<k} |det(Pi[B_j,B_k])|^2,
        Var n_2 = q/a^2 - q(2a-1)/a^4 + 2 sum_{j<k} |det(Pi[B_j,B_k])|^2.

  (L7)  TWO-MOMENT BOUND.  pi_max^2 <= sum_i pi_i^2 <= q(2a-1)/a^4 = p(2a-1)/(2a^3),
        so INEQ-2 follows whenever   p <= 32 (a-1)^2 / (a(2a-1)),  i.e. p <= 8 (a=3),
        p <= 10 (a=4), ... , p <= 15 (a -> infinity).  Nothing more.

  (L8)  power sums:   p_j := sum_i pi_i^j = P_{2j} / (2 a^{2j}),
        P_m = sum over roots of mu(x+a) of x^m,  and  P_{2j} = -2j [t^j] log Q(t),
        Q(t) = sum_r (-1)^r M_r t^r.   pi_max = lim_j p_j^{1/j}, monotone from above.
"""
import sys
import numpy as np
from itertools import combinations
from math import comb
from fractions import Fraction

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from mcp2 import mcp, restore_proj, rand_X, proj_from_X                    # noqa
from frac_naimark import GRAPHS, degrees_ok, graph_kernel, det_frac, sub   # noqa
from dpp_rep import naimark_slots, dpp_data, graph_family                  # noqa


# ------------------------------------------------------------------ families
def realify(M):
    """complex d x d -> real 2d x 2d, C-linear map as a real matrix."""
    d = M.shape[0]
    R = np.zeros((2 * d, 2 * d))
    R[0::2, 0::2] = M.real
    R[1::2, 1::2] = M.real
    R[1::2, 0::2] = M.imag
    R[0::2, 1::2] = -M.imag
    return R


def mub_family(a):
    """EXACT RATIONAL non-commuting rank-2 families on R^4.
    Rank-1 projections in C^2 realified.  a=3: the 6 MUB vectors (q=6);
    a=4: those plus the two standard basis vectors (q=8)."""
    h = Fraction(1, 2)
    Pc = [np.array([[1, 0], [0, 0]], dtype=complex),
          np.array([[0, 0], [0, 1]], dtype=complex),
          np.array([[.5, .5], [.5, .5]], dtype=complex),
          np.array([[.5, -.5], [-.5, .5]], dtype=complex),
          np.array([[.5, -.5j], [.5j, .5]], dtype=complex),
          np.array([[.5, .5j], [-.5j, .5]], dtype=complex)]
    if a == 4:
        Pc = Pc + [Pc[0], Pc[1]]
    P = np.array([realify(M) for M in Pc])
    # exact rational copy (entries are multiples of 1/2)
    Pq = [[[Fraction(int(round(2 * x)), 2) for x in row] for row in Pk] for Pk in P]
    return P, Pq, 4, len(Pc), a, 2


def rand_family(p, q, a, seed, complex_=False):
    rng = np.random.default_rng(seed)
    best = None
    for _ in range(60):
        X = rand_X(q, p, 2, rng, complex_)
        A, r = restore_proj(proj_from_X(X), q, p, a, 2, iters=6000, tol=1e-15)
        if best is None or r < best[1]:
            best = (A, r)
        if r < 1e-14:
            break
    return best


def multigraph_family(edges, p):
    """P_k = projection onto span(e_u,e_v) for edge k = (u,v)."""
    q = len(edges)
    P = np.zeros((q, p, p))
    for k, (u, v) in enumerate(edges):
        P[k, u, u] = 1.0
        P[k, v, v] = 1.0
    return P


def matchings_of_multigraph(edges, p):
    """# of r-matchings, r = 0..p//2, of the multigraph on p vertices."""
    q = len(edges)
    out = [0] * (p // 2 + 1)
    for r in range(p // 2 + 1):
        cnt = 0
        for T in combinations(range(q), r):
            used = set()
            ok = True
            for k in T:
                u, v = edges[k]
                if u in used or v in used:
                    ok = False
                    break
                used.add(u)
                used.add(v)
            cnt += ok
        out[r] = cnt
    return out


# ------------------------------------------------------- symmetric functions
def esym_of_matrix(A, m):
    """e_m(spec A) = sum of m x m principal minors, exact if A is Fractions."""
    if isinstance(A, np.ndarray):
        w = np.linalg.eigvalsh(A)
        e = np.zeros(len(w) + 1)
        e[0] = 1.0
        for lam in w:
            e[1:] = e[1:] + lam * e[:-1]
        return float(e[m])
    n = len(A)
    e = [Fraction(0)] * (n + 1)
    e[0] = Fraction(1)
    # exact: char poly by Faddeev-LeVerrier would be cleaner; use minors for small m
    tot = Fraction(0)
    for T in combinations(range(n), m):
        tot += det_frac(sub(A, list(T)))
    return tot


def M_numbers_from_projections(P, a, rmax=None, exact=None):
    """M_r = sum_{|T|=r} e_{2r}( sum_{k in T} P_k ).  exact = list-of-lists Fractions."""
    q, p, _ = (P.shape if exact is None else (len(exact), len(exact[0]), 0))
    rmax = p // 2 if rmax is None else rmax
    out = []
    for r in range(rmax + 1):
        if exact is None:
            tot = 0.0
            for T in combinations(range(q), r):
                tot += esym_of_matrix(np.sum(P[list(T)], axis=0), 2 * r)
        else:
            tot = Fraction(0)
            for T in combinations(range(q), r):
                S = [[sum(exact[k][i][j] for k in T) for j in range(p)]
                     for i in range(p)]
                tot += esym_of_matrix(S, 2 * r)
        out.append(tot)
    return out


def M_numbers_from_kernel(Pi, q, a, rmax, exact=False):
    """M_r = a^{2r} sum_{|T|=r} det Pi[B_T]."""
    out = []
    for r in range(rmax + 1):
        if exact:
            tot = Fraction(0)
            for T in combinations(range(q), r):
                idx = [2 * k + j for k in T for j in (0, 1)]
                tot += det_frac(sub(Pi, idx))
            out.append(Fraction(a) ** (2 * r) * tot)
        else:
            tot = 0.0
            for T in combinations(range(q), r):
                idx = [2 * k + j for k in T for j in (0, 1)]
                tot += np.linalg.det(Pi[np.ix_(idx, idx)])
            out.append(a ** (2 * r) * tot)
    return out


def shift_poly(mu, a):
    """mu given as c[m] = coeff of y^{p-m}; return d[m] = coeff of x^{p-m} of mu(x+a)."""
    p = len(mu) - 1
    d = np.zeros(p + 1)
    for m in range(p + 1):
        c = mu[m]                      # coeff of y^{p-m}
        n = p - m
        for i in range(n + 1):         # (x+a)^n
            d[p - i] += c * comb(n, i) * a ** (n - i)
    return d


# ------------------------------------------------------------------- checks
def full_check(name, P, a, Pq=None, do_dpp=True):
    q, p, _ = P.shape
    b = 2
    rmax = p // 2
    print(f"--- {name}:  p={p} q={q} a={a}")

    U, Pi = naimark_slots(P, a, b)
    # (L5) degree identity
    tot = 0.0
    for j in range(q):
        for k in range(q):
            if j != k:
                tot += np.linalg.norm(Pi[2 * j:2 * j + 2, 2 * k:2 * k + 2]) ** 2
    print(f"    (L5) sum_{{j!=k}}||Pi[B_j,B_k]||_F^2 = {tot:.10f}   "
          f"2q(a-1)/a^2 = {2*q*(a-1)/a**2:.10f}   err {abs(tot-2*q*(a-1)/a**2):.2e}")

    Mk = M_numbers_from_kernel(Pi, q, a, rmax)          # via kernel dets
    Mp = M_numbers_from_projections(P, a, rmax)          # basis-free, via e_{2r}
    print(f"    (L2) max |a^2r det Pi[B_T] sum  -  sum e_2r(S_T)| = "
          f"{max(abs(x-y) for x, y in zip(Mk, Mp)):.3e}")

    mu = mcp(P)
    d = shift_poly(mu, a)          # d[m] = coeff of x^{p-m}
    # coefficient of x^{p-2r} should be (-1)^r M_r ; odd coefficients should vanish
    odd = max(abs(d[m]) for m in range(p + 1) if m % 2) if p else 0.0
    err3 = max(abs(d[2 * r] - (-1) ** r * Mp[r]) for r in range(rmax + 1))
    print(f"    (L3) mu(x+a) = sum (-1)^r M_r x^(p-2r):  max coeff err {err3:.3e}"
          f"   max |odd coeff| {odd:.3e}")
    print(f"         M = {np.array2string(np.array(Mp), precision=6)}")
    print(f"    (L4) M_1 = {Mp[1]:.10f}  vs q = {q}   err {abs(Mp[1]-q):.2e}")

    # (L6)
    Ddet = sum(abs(np.linalg.det(Pi[2 * j:2 * j + 2, 2 * k:2 * k + 2])) ** 2
               for j in range(q) for k in range(q) if j < k)
    pred = comb(q, 2) - q * (a - 1) + a ** 4 * Ddet
    print(f"    (L6) M_2 = {Mp[2]:.10f}   C(q,2)-q(a-1)+a^4*sum det^2 = {pred:.10f}"
          f"   err {abs(Mp[2]-pred):.2e}    (sum_{{j<k}} det^2 = {Ddet:.3e})")

    # pi's from the roots
    rts = np.sort(np.roots(mu).real)
    # roots of mu(x+a) come in pairs +- a sqrt(pi_i): take the upper half only
    pis = np.sort(((rts[-rmax:] - a) / a) ** 2)[::-1] if rmax else np.array([])
    pimax = pis[0] if len(pis) else 0.0
    s1, s2 = pis.sum(), (pis ** 2).sum()
    print(f"    pi's = {np.array2string(np.sort(pis)[::-1], precision=6)}")
    print(f"         sum pi = {s1:.10f} (q/a^2 = {q/a**2:.10f})   "
          f"sum pi^2 = {s2:.10f}   q(2a-1)/a^4 - 2*sumdet^2 = "
          f"{q*(2*a-1)/a**4 - 2*Ddet:.10f}")
    bound = 4.0 * (a - 1) / a ** 2
    print(f"    pi_max = {pimax:.10f}   4(a-1)/a^2 = {bound:.10f}   "
          f"ratio {pimax/bound:.5f}  {'OK' if pimax <= bound + 1e-9 else '*** VIOLATION'}")
    print(f"    two-moment bound sqrt(sum pi^2) = {np.sqrt(s2):.6f}  "
          f"{'settles INEQ-2' if np.sqrt(s2) <= bound else 'does NOT settle'}")

    if do_dpp and comb(2 * q, p) <= 400000:
        w, svec, _ = dpp_data(U, p, q, b)
        n2 = (svec == 2).sum(axis=1)
        En2 = float((w * n2).sum())
        Vn2 = float((w * n2 ** 2).sum() - En2 ** 2)
        er = [float((w * np.array([comb(int(x), r) for x in n2])).sum())
              for r in range(rmax + 1)]
        err1 = max(abs(er[r] * a ** (2 * r) - Mp[r]) for r in range(rmax + 1))
        print(f"    (L1) E binom(n_2,r) = sum_T det Pi[B_T] : max err {err1:.3e}")
        print(f"         E n_2 = {En2:.10f} (q/a^2={q/a**2:.10f})  Var n_2 = {Vn2:.10f}"
              f"  pred {q/a**2 - q*(2*a-1)/a**4 + 2*Ddet:.10f}")

    if Pq is not None:
        Me = M_numbers_from_projections(None, a, rmax, exact=Pq)
        print(f"    EXACT M_r (rational arithmetic) = {Me}")
        ok = all(abs(float(Me[r]) - Mp[r]) < 1e-8 for r in range(rmax + 1))
        print(f"         agrees with float: {ok}")
    return Mp, pis


if __name__ == '__main__':
    print("=" * 92)
    print("PART 1 -- commuting (graph / multigraph) families at b = 2")
    print("=" * 92)
    GR = {
        'S(K_4)  [K_4]': ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 4, 3),
        '(4,8,4,2) [K_4 + perfect matching]':
            ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 1), (2, 3)], 4, 4),
        '(6,9,3,2) [K_{3,3}]':
            ([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
              (2, 3), (2, 4), (2, 5)], 6, 3),
        '(6,9,3,2) [prism]':
            ([(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
              (0, 3), (1, 4), (2, 5)], 6, 3),
        '(8,12,3,2) [cube Q_3]':
            ([(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
              (0, 4), (1, 5), (2, 6), (3, 7)], 8, 3),
    }
    for name, (edges, p, a) in GR.items():
        P = multigraph_family(edges, p)
        Pq = [[[Fraction(int(x)) for x in row] for row in Pk] for Pk in P]
        Mp, pis = full_check(name, P, a, Pq=Pq)
        mm = matchings_of_multigraph(edges, p)
        print(f"    (L6') r-matchings of H = {mm}   "
              f"{'MATCH' if all(abs(Mp[r]-mm[r])<1e-6 for r in range(len(mm))) else 'MISMATCH'}")
        print()

    print("=" * 92)
    print("PART 2 -- genuinely NON-COMMUTING families (exact rational: realified C^2)")
    print("=" * 92)
    for a in (3, 4):
        P, Pq, p, q, a_, b = mub_family(a)
        nc = max(np.linalg.norm(P[j] @ P[k] - P[k] @ P[j], 2)
                 for j in range(q) for k in range(q))
        print(f"    [noncommutativity max||[P_j,P_k]|| = {nc:.4f}]")
        full_check(f"MUB C^2 realified, a={a}", P, a, Pq=Pq)
        print()

    print("=" * 92)
    print("PART 3 -- random NON-COMMUTING families")
    print("=" * 92)
    for (p, q, a, cx) in [(4, 6, 3, False), (6, 9, 3, False), (4, 8, 4, False),
                          (6, 12, 4, False), (4, 6, 3, True)]:
        P, res = rand_family(p, q, a, seed=90210 + 13 * p + 7 * q + a, complex_=cx)
        if res > 1e-11:
            print(f"  [skip ({p},{q},{a}) residual {res:.1e}]")
            continue
        nc = max(np.linalg.norm(P[j] @ P[k] - P[k] @ P[j], 2)
                 for j in range(q) for k in range(q))
        print(f"    [feasibility residual {res:.1e}, noncommutativity {nc:.4f}]")
        full_check(("cx " if cx else "") + f"random({p},{q},{a})", P, a)
        print()
