"""na_lp.py -- is  (negative association) + (Bin(b,1/a) marginals) + (sum = p)
enough for the band?

The verified representation gives

    y^{q-p} mu[P](y) = E prod_k (y - a s_k),      s = (s_1..s_q),

with  (i) sum_k s_k = p a.s.,  (ii) s_k ~ Bin(b,1/a) exactly,  (iii) the law of
s is strong Rayleigh, hence negatively associated (Borcea-Branden-Liggett).

We ask: do (i)-(iii-weakened-to-NA) already force the band?

TEST.  f(y) := E prod_k (y - a s_k) is LINEAR in the law of s.  For a target
y0 > hi, "min f(y0) < 0 over the class" certifies a root > y0 (f -> +infty).
Symmetrising over S_q preserves every constraint and the objective, so the
optimum is attained at an EXCHANGEABLE law: variables = partitions of p into
at most q parts of size <= b.  Everything below is an exact LP on that
simplex.

Linear constraints imposed (all are consequences of NA, and all are linear
BECAUSE the one-dimensional marginals are pinned to Bin(b,1/a)):
   M   marginals          P(s_1 = j) = C(b,j) a^-j (1-1/a)^(b-j)
   P2  pairwise NA        E[u(s_1)v(s_2)] <= E[u] E[v]     u,v monotone same way
   Km  m-wise NA          E[prod_{k<=m} u(s_k)] <= (E u)^m , u >= 0 monotone
Lower-edge version: violation of the lower edge at y0 in (0,lo) is
(-1)^p f(y0) < 0.

RESULT (see na_counterexample.py for the clean family).  The answer is NO, and
the LP finds the same witness with and without every NA constraint: at
(p,q,a,b) = (6,9,3,2) the deterministic-up-to-permutation law with composition
(2,1,1,1,1,0,0,0,0) has exact Bin(2,1/3) marginals, sum = 6 = p, IS negatively
associated (permutation distributions are NA), and gives
    E prod_k (y - 3 s_k) = y^4 (y-3)^4 (y-6),
whose largest root 6 = ab exceeds hi = 5.8284.  So NA + marginals + the sum
constraint yield exactly lambda_max <= ab and nothing sharper.
"""
import sys
import numpy as np
from math import comb
from itertools import combinations
from scipy.optimize import linprog

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def partitions_fixed(p, q, b):
    """All non-increasing tuples of length q, entries in [0,b], summing to p."""
    out = []

    def rec(pos, remaining, cap, cur):
        if pos == q:
            if remaining == 0:
                out.append(tuple(cur))
            return
        lo = max(0, remaining - cap * (q - pos - 1))
        for v in range(min(cap, remaining), lo - 1, -1):
            cur.append(v)
            rec(pos + 1, remaining - v, v, cur)
            cur.pop()
    rec(0, p, b, [])
    return out


def orbit_stats(lams, q, b):
    """For each partition lam: counts c[j] = #{k : lam_k = j}."""
    return [np.array([sum(1 for v in lam if v == j) for j in range(b + 1)],
                     dtype=float) for lam in lams]


def build(p, q, a, b, use_pair=True, use_mwise=True, mono_grid=9, verbose=True):
    lams = partitions_fixed(p, q, b)
    N = len(lams)
    cnt = orbit_stats(lams, q, b)          # (b+1)-vector per partition
    binom = np.array([comb(b, j) * (1.0 / a) ** j * (1 - 1.0 / a) ** (b - j)
                      for j in range(b + 1)])

    A_eq, b_eq = [], []
    # total mass
    A_eq.append(np.ones(N)); b_eq.append(1.0)
    # marginals  E[ c_j / q ] = binom[j]
    for j in range(b + 1):
        A_eq.append(np.array([cnt[i][j] / q for i in range(N)]))
        b_eq.append(binom[j])

    A_ub, b_ub = [], []
    # monotone test functions on {0..b}, normalised, nonneg, increasing
    monos = []
    if b == 2:
        for t1 in np.linspace(0, 1, mono_grid):
            monos.append(np.array([0.0, t1, 1.0]))
            monos.append(np.array([1.0, t1, 0.0])[::-1] * 0 + np.array([1.0, 1 - t1, 0.0]))
    else:
        gr = np.linspace(0, 1, mono_grid)
        for _ in range(0):
            pass
        # increasing step functions and their smooth interpolants
        for thr in range(b + 1):
            monos.append(np.array([1.0 if j >= thr else 0.0 for j in range(b + 1)]))
            monos.append(np.array([1.0 if j <= thr else 0.0 for j in range(b + 1)]))
        for t in gr:
            monos.append(np.array([(j / b) ** (0.2 + 3 * t) for j in range(b + 1)]))
            monos.append(np.array([(1 - j / b) ** (0.2 + 3 * t) for j in range(b + 1)]))
    monos = [u for u in monos if u.max() > 0]

    # -- pairwise NA:  E[u(s_1) v(s_2)] <= E u * E v
    if use_pair:
        for u in monos:
            for v in monos:
                # both increasing or both decreasing?  check monotone direction
                du = np.sign(np.diff(u)); dv = np.sign(np.diff(v))
                du = du[du != 0]; dv = dv[dv != 0]
                if len(du) and len(np.unique(du)) > 1:
                    continue
                if len(dv) and len(np.unique(dv)) > 1:
                    continue
                if len(du) and len(dv) and du[0] != dv[0]:
                    continue
                row = np.zeros(N)
                for i, lam in enumerate(lams):
                    tot = 0.0
                    for k1 in range(q):
                        for k2 in range(q):
                            if k1 != k2:
                                tot += u[lam[k1]] * v[lam[k2]]
                    row[i] = tot / (q * (q - 1))
                A_ub.append(row)
                b_ub.append(float(binom @ u) * float(binom @ v))

    # -- m-wise NA:  E[prod_{k in A} u(s_k)] <= (E u)^{|A|}
    if use_mwise:
        for u in monos:
            for m in range(2, q + 1):
                row = np.zeros(N)
                for i, lam in enumerate(lams):
                    tot = 0.0
                    for A in combinations(range(q), m):
                        pr = 1.0
                        for k in A:
                            pr *= u[lam[k]]
                        tot += pr
                    row[i] = tot / comb(q, m)
                A_ub.append(row)
                b_ub.append(float(binom @ u) ** m)

    if verbose:
        print(f"    LP: {N} orbits, {len(A_eq)} eq, {len(A_ub)} ineq")
    return lams, np.array(A_eq), np.array(b_eq), \
        (np.array(A_ub) if A_ub else None), (np.array(b_ub) if b_ub else None)


def objective(lams, y0, a):
    return np.array([float(np.prod([y0 - a * v for v in lam])) for lam in lams])


def run(p, q, a, b, tag='', **kw):
    lo, hi = band(a, b)
    lams, Ae, be, Au, bu = build(p, q, a, b, **kw)
    print(f"  ({p},{q},{a},{b})  band [{lo:.5f},{hi:.5f}]  {tag}")
    res = {}
    for label, sgn, y0 in [('upper', 1.0, hi + 1e-9),
                           ('upper+', 1.0, hi + 0.02),
                           ('lower', (-1.0) ** p, max(lo - 1e-9, 0.0)),
                           ('lower-', (-1.0) ** p, max(lo * 0.9, 1e-6))]:
        if y0 <= 0:
            continue
        c = sgn * objective(lams, y0, a)
        r = linprog(c, A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be,
                    bounds=(0, 1), method='highs')
        if not r.success:
            print(f"    {label:7s} y0={y0:9.5f}  LP infeasible/failed ({r.message[:40]})")
            continue
        val = r.fun
        w = r.x
        f = np.zeros(q + 1)
        for wi, lam in zip(w, lams):
            if wi <= 1e-14:
                continue
            poly = np.array([1.0])
            for v in lam:
                poly = np.convolve(poly, [1.0, -a * float(v)])
            f += wi * poly
        rts = np.roots(f)
        maxim = np.abs(rts.imag).max()
        rr = np.sort(rts.real)
        print(f"    {label:7s} y0={y0:9.5f}  min sgn*f(y0) = {val: .6e}"
              f"   {'VIOLATION' if val < -1e-9 else 'ok (>=0)'}")
        if val < -1e-9:
            print(f"        witness roots {np.array2string(rr, precision=5)}"
                  f"  max|Im|={maxim:.2e}")
            supp = [(lams[i], w[i]) for i in range(len(w)) if w[i] > 1e-10]
            print(f"        support: {supp}")
        res[label] = val
    return res


if __name__ == '__main__':
    CASES = [(4, 6, 3, 2), (3, 6, 4, 2), (4, 8, 4, 2), (6, 9, 3, 2),
             (5, 10, 4, 2), (6, 8, 4, 3), (4, 5, 5, 4), (3, 4, 4, 3)]
    print("=" * 78)
    print("A. marginals + fixed sum ONLY (no negative association)")
    print("=" * 78)
    for (p, q, a, b) in CASES:
        run(p, q, a, b, tag='(no NA)', use_pair=False, use_mwise=False)
    print()
    print("=" * 78)
    print("B. + pairwise NA")
    print("=" * 78)
    for (p, q, a, b) in CASES:
        run(p, q, a, b, tag='(pairwise NA)', use_pair=True, use_mwise=False)
    print()
    print("=" * 78)
    print("C. + all m-wise NA products  E prod_{k in A} u(s_k) <= (E u)^|A|")
    print("=" * 78)
    for (p, q, a, b) in CASES:
        run(p, q, a, b, tag='(full NA family)', use_pair=True, use_mwise=True)
