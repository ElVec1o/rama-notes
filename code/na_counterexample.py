"""na_counterexample.py -- the explicit NA counterexample, checked from the
definition, and the certificate that it is NOT strong Rayleigh.

THE FAMILY.  Fix a >= 2, b >= 2.  Put q = a^b, p = b a^{b-1} (so pa = qb).
Let lambda be the composition of p into q parts that realises the Binomial
profile exactly:  exactly  n_j = C(b,j) (a-1)^{b-j}  parts equal to j,
j = 0..b   (so sum_j n_j = a^b = q  and  sum_j j n_j = b a^{b-1} = p).
Let s = (s_1..s_q) be lambda in a uniformly random order.

Then
   (1) sum_k s_k = p  a.s.
   (2) s_k ~ Binomial(b, 1/a) exactly, for every k
   (3) s is NEGATIVELY ASSOCIATED  (permutation distributions are NA:
       Joag-Dev & Proschan 1983, Thm 2.11)
   (4) E prod_k (y - a s_k) = prod_j (y - a j)^{n_j}, whose largest root is
       a*b -- the TRIVIAL bound -- and  ab - hi = (sqrt((a-1)(b-1)) - 1)^2 > 0
       whenever (a,b) != (2,2).

So NA + exact Binomial marginals + exact sum constraint cannot give ANY bound
better than lambda_max <= ab, which is what the representation gives for free.

We check (1)(2)(3)(4) numerically, and we check that the law is NOT strong
Rayleigh by exhibiting a two-block sum whose pgf has non-real roots (for a
strong Rayleigh process every subset count is a sum of independent Bernoullis,
Feder-Mihail / Borcea-Branden-Liggett, hence has a real-rooted pgf).
"""
import sys
import numpy as np
from math import comb
from itertools import combinations, permutations
from fractions import Fraction

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def profile(a, b):
    """n_j = C(b,j)(a-1)^{b-j}, j = 0..b."""
    return [comb(b, j) * (a - 1) ** (b - j) for j in range(b + 1)]


def composition(a, b):
    n = profile(a, b)
    lam = []
    for j in range(b, -1, -1):
        lam += [j] * n[j]
    return lam


def check_family(a, b):
    n = profile(a, b)
    q = sum(n)
    p = sum(j * n[j] for j in range(b + 1))
    lam = composition(a, b)
    assert q == a ** b and p == b * a ** (b - 1) and p * a == q * b
    # (2) marginals
    binom = [Fraction(comb(b, j) * (a - 1) ** (b - j), a ** b)
             for j in range(b + 1)]
    marg = [Fraction(n[j], q) for j in range(b + 1)]
    ok2 = marg == binom
    # (4) polynomial
    lo, hi = band(a, b)
    roots = sorted(set(a * j for j in range(b + 1) if n[j] > 0))
    lam_max = a * b
    return dict(a=a, b=b, p=p, q=q, ok2=ok2, lo=lo, hi=hi,
                lam_max=lam_max, roots=roots,
                gap=lam_max - hi,
                gap_formula=(np.sqrt((a - 1.0) * (b - 1.0)) - 1.0) ** 2)


# ---------------------------------------------------- NA check from definition
def na_check(lam, trials=4000, seed=0):
    """Monte-Carlo-free exact check of  E[f(s_A) g(s_B)] <= E f E g  for random
    disjoint A,B and random monotone f,g, over the exact permutation law.
    We enumerate the law exactly when q <= 9 by grouping permutations."""
    q = len(lam)
    rng = np.random.default_rng(seed)
    # exact law: uniform over distinct permutations of lam
    perms = sorted(set(permutations(lam)))
    W = 1.0 / len(perms)
    Sm = np.array(perms, dtype=float)          # (M, q)
    worst = -np.inf
    for _ in range(trials):
        k = rng.integers(1, q // 2 + 1)
        idx = rng.permutation(q)
        A = idx[:k]
        B = idx[k:2 * k]
        # random nonneg increasing functions on {0..b}
        b = int(max(lam))
        fv = np.sort(rng.random(b + 1))
        gv = np.sort(rng.random(b + 1))
        if rng.random() < 0.5:
            fv = fv[::-1].copy()
            gv = gv[::-1].copy()          # both decreasing
        # increasing functions of the vector: use min / max / sum aggregates
        agg = rng.integers(0, 3)
        def apply(vals, fun):
            V = fun[vals.astype(int)]
            if agg == 0:
                return V.prod(axis=1)
            if agg == 1:
                return V.min(axis=1)
            return V.max(axis=1)
        FA = apply(Sm[:, A], fv)
        GB = apply(Sm[:, B], gv)
        cov = W * float(FA @ GB) - (W * FA.sum()) * (W * GB.sum())
        worst = max(worst, cov)
    return worst


def two_block_pgf(lam, k1=0, k2=1):
    """exact law of s_{k1}+s_{k2} under the permutation distribution, as a
    coefficient list; returns (coeffs, roots)."""
    q = len(lam)
    from collections import Counter
    cnt = Counter(lam)
    vals = sorted(cnt)
    tot = 0
    dist = {}
    for u in vals:
        for v in vals:
            m = cnt[u] * (cnt[v] - (1 if u == v else 0))
            if m == 0:
                continue
            dist[u + v] = dist.get(u + v, 0) + m
            tot += m
    assert tot == q * (q - 1)
    deg = max(dist)
    c = [Fraction(dist.get(j, 0), tot) for j in range(deg + 1)]
    r = np.roots([float(x) for x in c[::-1]])
    return c, r


if __name__ == '__main__':
    print("=" * 78)
    print("The NA counterexample family:  q = a^b, p = b a^(b-1),")
    print("  s = uniformly random ordering of the exact binomial profile")
    print("=" * 78)
    for a in range(2, 8):
        for b in range(2, min(a, 4) + 1):
            d = check_family(a, b)
            print(f"  a={a} b={b}: p={d['p']:4d} q={d['q']:4d}  "
                  f"band=[{d['lo']:.4f},{d['hi']:.4f}]  roots {d['roots']}  "
                  f"lambda_max={d['lam_max']}  "
                  f"exceeds hi by {d['gap']:.6f}  "
                  f"= (sqrt((a-1)(b-1))-1)^2 = {d['gap_formula']:.6f}  "
                  f"marginals exact: {d['ok2']}")
    print()
    print("=" * 78)
    print("Smallest instance a=3,b=2:  q=9, p=6, lambda=(2,1,1,1,1,0,0,0,0)")
    print("=" * 78)
    lam = composition(3, 2)
    print(f"  composition {lam}   sum={sum(lam)}  band={band(3,2)}")
    print(f"  E prod (y - 3 s_k) = y^4 (y-3)^4 (y-6):  largest root 6 > "
          f"{band(3,2)[1]:.6f}")
    w = na_check(lam, trials=3000, seed=1)
    print(f"  NA check (worst Cov(f(s_A),g(s_B)) over 3000 random disjoint "
          f"A,B and monotone f,g): {w:.3e}   "
          f"{'NA holds' if w <= 1e-12 else 'NA VIOLATED'}")
    c, r = two_block_pgf(lam)
    print(f"  pgf of s_1+s_2 : {[str(x) for x in c]}")
    print(f"     roots {np.array2string(r, precision=5)}   "
          f"max|Im| = {np.abs(r.imag).max():.4f}")
    print("     => NOT a sum of independent Bernoullis => the law is NOT")
    print("        strong Rayleigh (although it IS negatively associated).")
    print()
    print("For comparison, the same two-block pgf for the honest projection")
    print("families is real-rooted (checked in dpp_sr_check).")
