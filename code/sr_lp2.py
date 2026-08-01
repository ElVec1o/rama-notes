"""sr_lp2.py -- the LP over ALL laws satisfying (i) sum = p and (ii) marginals
= Bin(b,1/a), done properly and at LARGE q.

KEY SIMPLIFICATION.  The objective  f_x(y) = E prod_k (y - a s_k)  and both
constraints are S_q-invariant, so w.l.o.g. the law is exchangeable, and an
exchangeable law is a distribution over ORBITS.  An orbit is a partition of p
into at most q parts of size <= b, and such a partition is determined by its
PROFILE  n = (n_0,...,n_b),  n_j = #{k : s_k = j}, subject to

        sum_j n_j = q,        sum_j j n_j = p.

So the variables are indexed by profiles, and

        f_n(y) = prod_j (y - a j)^{n_j},
        P(s_1 = j) = E[n_j]/q .

Hence the LP is
        min_x  sum_n x_n f_n(y0)
        s.t.   x >= 0,   sum_n x_n (n_j/q) = C(b,j) a^{-j}(1-1/a)^{b-j}, j=0..b.
(mass is implied by summing the b+1 marginal rows).  Only b+1 equalities, so
every BASIC feasible solution is supported on at most b+1 profiles, and the
vertices can be ENUMERATED exactly.  This makes q = 27, 64, 100 trivial.

f_x(y0) < 0 certifies a real root of f_x above y0 (f_x is monic of degree q).
"""
import sys
import numpy as np
from math import comb
from fractions import Fraction
from itertools import combinations
from scipy.optimize import linprog

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def profiles(p, q, b):
    """all (n_0..n_b) >= 0 with sum n_j = q, sum j n_j = p.
    Enumerate (n_1..n_b) with sum j n_j = p and sum n_j <= q; n_0 is the rest."""
    out = []

    def rec(j, used, restp, cur):
        if j > b:
            if restp == 0:
                out.append(tuple([q - used] + cur))
            return
        maxn = min(q - used, restp // j)
        for nj in range(maxn + 1):
            rec(j + 1, used + nj, restp - j * nj, cur + [nj])
    rec(1, 0, p, [])
    return out


def fprofile(n, a, y0):
    """prod_j (y0 - a j)^{n_j} in float."""
    v = 1.0
    for j, nj in enumerate(n):
        if nj:
            v *= (y0 - a * j) ** nj
    return v


def fprofile_mp(n, a, y0, dps=80):
    from mpmath import mp, mpf
    mp.dps = dps
    v = mpf(1)
    for j, nj in enumerate(n):
        if nj:
            v *= (mpf(y0) - a * j) ** nj
    return v


def marg_rows(profs, q, b):
    return np.array([[n[j] / q for n in profs] for j in range(b + 1)])


def marg_rhs(a, b):
    return np.array([comb(b, j) * (1.0 / a) ** j * (1 - 1.0 / a) ** (b - j)
                     for j in range(b + 1)])


def lp_min(profs, A, rhs, a, y0, scale=None):
    c = np.array([fprofile(n, a, y0) for n in profs])
    s = np.abs(c).max()
    if s > 0:
        c = c / s
    r = linprog(c, A_eq=A, b_eq=rhs, bounds=(0, None), method='highs')
    if not r.success:
        return None, None, None
    return r.fun * s, r.x, s


def enumerate_vertices(profs, a, b, q, rhs, maxcomb=4_000_000):
    """All basic feasible solutions: pick b+1 profiles, solve, keep x >= 0."""
    N = len(profs)
    A = marg_rows(profs, q, b)
    verts = []
    m = b + 1
    cnt = 0
    for T in combinations(range(N), m):
        cnt += 1
        if cnt > maxcomb:
            break
        M = A[:, list(T)]
        try:
            x = np.linalg.solve(M, rhs)
        except np.linalg.LinAlgError:
            continue
        if np.all(x >= -1e-12):
            verts.append((T, np.maximum(x, 0.0)))
    return verts, cnt


def eval_f(profs, T, x, a, y, dps=60):
    from mpmath import mp, mpf
    mp.dps = dps
    s = mpf(0)
    for i, t in zip(T, range(len(T))):
        if x[t] <= 0:
            continue
        s += mpf(float(x[t])) * fprofile_mp(profs[i], a, y, dps)
    return s


def largest_root(profs, T, x, a, b, q, lo_scan, hi_scan, ngrid=4000, dps=60):
    """largest y in (lo_scan, hi_scan] with a sign change of f."""
    ys = np.linspace(hi_scan, lo_scan, ngrid)
    prev_y, prev_v = None, None
    for y in ys:
        v = eval_f(profs, T, x, a, float(y))
        if prev_v is not None and (v > 0) != (prev_v > 0):
            a_, b_ = float(y), float(prev_y)
            for _ in range(80):
                m = 0.5 * (a_ + b_)
                vm = eval_f(profs, T, x, a, m)
                if (vm > 0) == (prev_v > 0):
                    b_ = m
                else:
                    a_ = m
            return 0.5 * (a_ + b_)
        prev_y, prev_v = y, v
    return None


def run(p, q, a, b, do_vertices=True, quiet=False):
    lo, hi = band(a, b)
    profs = profiles(p, q, b)
    N = len(profs)
    A = marg_rows(profs, q, b)
    rhs = marg_rhs(a, b)
    r0 = linprog(np.zeros(N), A_eq=A, b_eq=rhs, bounds=(0, None), method='highs')
    if not r0.success:
        print(f"({p},{q},{a},{b}) INFEASIBLE")
        return None
    rk = np.linalg.matrix_rank(A, tol=1e-11)
    print(f"({p},{q},{a},{b})  band=[{lo:.5f},{hi:.5f}]  ab={a*b}  "
          f"profiles={N}  rank={rk}  poly-dim<={N-rk}")

    # ---- upper edge: largest y0 with min_x f_x(y0) < 0
    ys = np.linspace(hi + 1e-9, a * b - 1e-9, 200)
    best = None
    for y0 in ys[::-1]:
        v, x, s = lp_min(profs, A, rhs, a, y0)
        if v is not None and v < -1e-13 * max(1.0, abs(s)):
            best = (y0, x)
            break
    if best is None:
        print(f"    UPPER: min_x f_x(y0) >= 0 for every y0 in (hi, ab]  "
              f"==>  (i)+(ii) ALONE force lambda_max <= hi = {hi:.5f}")
        up = None
    else:
        y0, x = best
        supp = [(profs[i], float(x[i])) for i in range(N) if x[i] > 1e-10]
        print(f"    UPPER: certified real root > {y0:.5f}  "
              f"(hi={hi:.5f}, excess {y0-hi:+.5f})")
        print(f"       witness profiles (n_0..n_b), weight: {supp}")
        up = y0
    # ---- lower edge
    lowres = None
    if lo > 1e-12:
        sgn = (-1.0) ** p   # f = y^(q-p) mu(y): the sign below all
        # roots of mu is (-1)^p, NOT (-1)^q -- the y^(q-p) factor is positive
        ys = np.linspace(1e-9, lo - 1e-9, 200)
        for y0 in ys:
            c = np.array([sgn * fprofile(n, a, y0) for n in profs])
            s = np.abs(c).max()
            r = linprog(c / s, A_eq=A, b_eq=rhs, bounds=(0, None), method='highs')
            if r.success and r.fun * s < -1e-13 * max(1.0, s):
                supp = [(profs[i], float(r.x[i])) for i in range(N)
                        if r.x[i] > 1e-10]
                print(f"    LOWER: certified real root < {y0:.5f}  "
                      f"(lo={lo:.5f}, deficit {lo-y0:+.5f})")
                print(f"       witness profiles: {supp}")
                lowres = y0
                break
        if lowres is None:
            print(f"    LOWER: (i)+(ii) ALONE force lambda_min >= lo = {lo:.5f}")
    else:
        print(f"    LOWER: lo = 0, nothing to prove")
    return dict(p=p, q=q, a=a, b=b, up=up, low=lowres, profs=profs, A=A,
                rhs=rhs, lo=lo, hi=hi, N=N)


if __name__ == '__main__':
    np.set_printoptions(linewidth=160)
    print("=" * 78)
    print("b = 2 :  where does (i)+(ii) stop forcing the band?   a^b = q_crit?")
    print("=" * 78)
    for q in [6, 8, 9, 10, 12, 15, 18, 27]:
        p = 2 * q // 3
        if 3 * p != 2 * q:
            continue
        run(p, q, 3, 2)
    print()
    for q in [8, 12, 16, 20, 24, 32]:
        p = 2 * q // 4
        run(p, q, 4, 2)
    print()
    print("=" * 78)
    print("b = 3, a = 3  (band [0,8], ab = 9;  a^b = 27)")
    print("=" * 78)
    for q in [4, 6, 8, 10, 12, 15, 18, 21, 24, 27, 30, 36, 45, 54]:
        run(q, q, 3, 3)
    print()
    print("=" * 78)
    print("b = 3, a = 4  (band [0.101,9.899], ab = 12;  a^b = 64)")
    print("=" * 78)
    for q in [8, 12, 16, 24, 32, 40, 48, 64, 80]:
        p = 3 * q // 4
        if 4 * p != 3 * q:
            continue
        run(p, q, 4, 3)
    print()
    print("=" * 78)
    print("b = 4, a = 4  (band [0,12], ab = 16;  a^b = 256)")
    print("=" * 78)
    for q in [5, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]:
        run(q, q, 4, 4)
