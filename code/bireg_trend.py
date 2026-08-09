"""Does the biregular margin go to zero with size?  If it does, D3 is false.

The complete bipartite graph is NOT extremal: random (3,q)-biregular graphs have margins near
0.37 against 0.63 for K_{3,q} (code/biregmargin.py), and the margin FELL as the number of
right vertices rose, 0.405 at r=6 and 0.367 at r=7. That is the only downward trend in the
whole programme, and if it continues to zero then

  * D3 is false, and
  * Song, Fan and Miao's Problem 1 is settled in the negative,

since the biregular case of Conjecture 10 is exactly that problem. So this is the experiment
worth doing properly, which means going far enough in r to see whether the trend flattens.

FROZEN BEFORE THE DATA:
  P3. The minimum margin over (d,q)-biregular graphs is bounded below by a positive constant
      as the number of vertices grows.

P3 is the conservative reading: the decline flattens. Its negation is a refutation of D3.

THE METHOD, and it is what makes the range possible. For a bipartite graph with a small right
side, count matchings by a bitmask permanent instead of vertex deletion. Processing left
vertices one at a time with dp[S] = the number of matchings using exactly the right-vertices S,

    dp_new[S] = dp[S] + sum over j in S adjacent to l of dp[S - j],

so m_k is the sum of dp[S] over |S| = k, in exact integers, at cost 2^r m r rather than the
exponential blow-up of deletion on a graph with no low-degree vertex to recurse on. That takes
n from about 30 up to 70 and makes the trend visible.

The gap edge is g = sqrt(q-1) - sqrt(d-1), the inner edge of the (d,q)-biregular tree spectrum;
x_min is the smallest positive root of mu_G, from the degree-r polynomial in x^2.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import random
import numpy as np
import sympy as sp

y = sp.Symbol('y')
BUDGET = 1500.0
CKPT = 'private/bireg_trend_ckpt.txt'


def rand_biregular(d, q, r, seed):
    """m = r q / d left vertices of degree d, r right of degree q; simple and connected."""
    if (r * q) % d:
        return None
    m = (r * q) // d
    rng = random.Random(seed * 7919 + r * 101 + q)
    for _ in range(600):
        stubs = [j for j in range(r) for _ in range(q)]
        rng.shuffle(stubs)
        nbr, ok = [], True
        for i in range(m):
            take = stubs[i * d:(i + 1) * d]
            if len(set(take)) != d:
                ok = False; break
            nbr.append(sorted(take))
        if not ok:
            continue
        deg = [0] * r
        for s in nbr:
            for j in s:
                deg[j] += 1
        if any(t != q for t in deg):
            continue
        adj = {i: set() for i in range(m + r)}
        for i, s in enumerate(nbr):
            for j in s:
                adj[i].add(m + j); adj[m + j].add(i)
        st, vis = [0], {0}
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in vis:
                    vis.add(w); st.append(w)
        if len(vis) == m + r:
            return m, nbr
    return None


def matching_counts(m, r, nbr):
    """m_k for k = 0..r, exactly, by a bitmask permanent over the small side."""
    size = 1 << r
    dp = [0] * size
    dp[0] = 1
    for s in nbr:
        mask_bits = [1 << j for j in s]
        for S in range(size - 1, -1, -1):
            v = dp[S]
            if not v:
                continue
            for b in mask_bits:
                if not (S & b):
                    dp[S | b] += v
    out = [0] * (r + 1)
    for S in range(size):
        out[bin(S).count('1')] += dp[S]
    return out


def xmin_from_counts(mk, r):
    """smallest positive root of mu, from Q(y) = sum_k (-1)^k m_k y^{r-k}, y = x^2."""
    co = [((-1) ** k) * mk[k] for k in range(r + 1)]
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return None
    try:
        rs = sorted(sp.re(t) for t in sp.Poly(co, y).nroots(n=30, maxsteps=6000)
                    if abs(sp.im(t)) < 1e-18 and sp.re(t) > 1e-14)
    except Exception:
        return None
    return float(sp.sqrt(rs[0])) if rs else None


def main():
    print("P3 (frozen): the minimum biregular margin stays bounded away from zero.\n")
    print(f"{'d':>3}{'q':>4}{'r':>4}{'m':>5}{'n':>5}{'gap edge':>10}"
          f"{'best x_min':>12}{'min margin':>12}{'seeds':>7}")
    t0 = time.time()
    table = {}
    for (d, q) in ((3, 6), (3, 9), (3, 12), (4, 8)):
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        prev = None
        for r in range(4, 17):
            if (r * q) % d or time.time() - t0 > BUDGET:
                continue
            m = (r * q) // d
            n = m + r
            if r > 16 or n > 76:
                continue
            best, used = None, 0
            for seed in range(14):
                if time.time() - t0 > BUDGET:
                    break
                R = rand_biregular(d, q, r, seed)
                if R is None:
                    continue
                mm, nbr = R
                xm = xmin_from_counts(matching_counts(mm, r, nbr), r)
                if xm is None:
                    continue
                used += 1
                if best is None or xm < best:
                    best = xm
            if best is None:
                continue
            marg = best - g
            table.setdefault((d, q), []).append((r, n, marg))
            arrow = ""
            if prev is not None:
                arrow = "  down" if marg < prev - 1e-9 else "  up"
            prev = marg
            print(f"{d:>3}{q:>4}{r:>4}{m:>5}{n:>5}{g:>10.5f}{best:>12.6f}"
                  f"{marg:>12.6f}{used:>7}{arrow}", flush=True)
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"d={d} q={q} r={r} margin={marg:.6f}\n")
            os.replace(CKPT + '.tmp', CKPT)
        print()

    print(f"{time.time()-t0:.0f}s\n")
    print("  trend in the number of right vertices, per family:")
    print(f"{'family':>10}{'points':>8}{'first':>11}{'last':>11}{'min':>11}{'slope/r':>10}")
    dying = []
    for (d, q), rows in sorted(table.items()):
        if len(rows) < 3:
            continue
        rs = np.array([t[0] for t in rows], float)
        ms = np.array([t[2] for t in rows], float)
        slope = np.polyfit(rs, ms, 1)[0]
        print(f"{f'({d},{q})':>10}{len(rows):>8}{ms[0]:>11.5f}{ms[-1]:>11.5f}"
              f"{ms.min():>11.5f}{slope:>10.5f}")
        if slope < -0.002 and ms[-1] < ms[0] - 0.02:
            dying.append(((d, q), slope, ms[-1]))
    if any(m < 0 for _, rows in table.items() for _, _, m in rows):
        print("\n  MARGIN WENT NEGATIVE: D3 is false and Problem 1 is settled.")
    elif dying:
        print(f"\n  the margin is still FALLING in {len(dying)} families; P3 is not yet safe.")
        for (dq, sl, last) in dying:
            need = last / (-sl)
            print(f"    {dq}: slope {sl:+.5f} per right vertex, last {last:.5f}; "
                  f"linear extrapolation hits zero near r = {need + 16:.0f}")
        print("  Linear extrapolation of a decaying quantity is weak evidence; what matters is "
              "whether it flattens.")
    else:
        print("\n  P3 holds: the decline flattens and the margin stays positive.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
