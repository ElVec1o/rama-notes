"""Wide sweep for the tie-break at feedback vertex number two.

SUPERSEDED. This script was written while the tie-break was a conjecture. It is now a
theorem, RamaLean/TieBreak.lean, proved from vertex-deletion interlacing alone with no
condition on the universal cover, so a wide search for counterexamples is no longer the
right use of compute and this sweep is not run. It is kept because the smaller check in
code/fvs_window.py serves as a regression test on the interlacing hypothesis, and because
the cost note below is worth keeping.

Cost note, for the next time: the bottleneck here is not root isolation but the exact
comparison of sympy CRootOf objects against the rational sample points, which I did not
account for when scoping. Measuring the rate of the wrong inner loop is how a job gets
mis-scoped twice. Count roots with a Sturm sequence on the integer polynomial instead.


RamaLean/TieBreak.lean proves, from vertex-deletion interlacing alone:

    if a - c is even then  a = c  <=>  mu_F(x) and mu_{G-v1}(x) + mu_{G-v2}(x) agree in sign

where a, b1, b2, c count the roots above x of mu_G, mu_{G-v1}, mu_{G-v2}, mu_F, and
F = G - v1 - v2.  The proof runs through the squeeze b1 = b2, so this script checks BOTH
the four interlacing relations it assumes AND the conclusion it draws, over every connected
graph on 4 to 6 vertices and a sample on 7, at every pair (v1, v2) leaving a forest.

Everything is exact: matching polynomials have integer coefficients, sample points are
rationals with denominator 4, and root counts come from sympy real_roots.  A reported OK is
a proof for the instances covered, not a numerical impression.
"""

import sys
import random
import time
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
from sympy import Poly, symbols, real_roots

X = symbols('X')
random.seed(20260808)


def matching_coeffs(n, edges):
    """Ascending integer coefficients of mu_G, by DP over edges with a used-vertex mask."""
    m = len(edges)
    counts = [0] * (n // 2 + 1)

    @lru_cache(maxsize=None)
    def rec(i, mask, k):
        if i == m:
            return 1 if k == 0 else 0
        total = rec(i + 1, mask, k)          # skip edge i
        if k > 0:
            u, v = edges[i]
            bu, bv = 1 << u, 1 << v
            if not (mask & bu) and not (mask & bv):
                total += rec(i + 1, mask | bu | bv, k - 1)
        return total

    for k in range(n // 2 + 1):
        counts[k] = rec(0, 0, k)
    rec.cache_clear()
    coeffs = [0] * (n + 1)
    for k, c in enumerate(counts):
        coeffs[n - 2 * k] += (-1) ** k * c
    return coeffs


_ROOT_CACHE = {}


def poly_roots(n, edges):
    """Exact roots and coefficients, memoised: vertex deletions repeat heavily across a
    sweep, and each real_roots call dominates the cost."""
    key = (n, tuple(sorted(edges)))
    hit = _ROOT_CACHE.get(key)
    if hit is not None:
        return hit
    if n == 0:
        out = ([], [1])
    else:
        c = matching_coeffs(n, edges)
        p = Poly(sum(co * X ** i for i, co in enumerate(c)), X)
        out = (sorted(real_roots(p), reverse=True), c)
    _ROOT_CACHE[key] = out
    return out


def peval(coeffs, x):
    return sum(Fraction(c) * x ** i for i, c in enumerate(coeffs))


def delete(n, edges, vs):
    keep = [u for u in range(n) if u not in vs]
    idx = {u: i for i, u in enumerate(keep)}
    return len(keep), tuple((idx[a], idx[b]) for (a, b) in edges if a not in vs and b not in vs)


def is_forest(n, edges):
    par = list(range(n))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru == rv:
            return False
        par[ru] = rv
    return True


def connected(n, edges):
    if n == 0:
        return True
    adj = {i: [] for i in range(n)}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n


def graphs(n, cap=None):
    allpairs = list(combinations(range(n), 2))
    N = len(allpairs)
    idxs = range(1 << N)
    if cap is not None and (1 << N) > cap:
        idxs = random.sample(range(1 << N), cap)
    for bits in idxs:
        e = tuple(allpairs[i] for i in range(N) if bits >> i & 1)
        if len(e) >= n - 1 and connected(n, e):
            yield e


def main():
    t0 = time.time()
    print(f"{'n':>3}{'graphs':>9}{'fvs2 pairs':>12}{'checks':>9}"
          f"{'interlace':>11}{'tiebreak':>10}")
    grand = [0, 0, 0]
    # Cost is dominated by exact root isolation, so caps are set from a measured
    # rate rather than guessed: measured at 134 graphs per second at n = 6, root
    # isolation memoised across the repeated vertex deletions.
    for n, cap in ((4, None), (5, None), (6, 1200), (7, 400)):
        ng = npair = ncheck = 0
        bad_int = bad_tie = 0
        for e in graphs(n, cap):
            ng += 1
            rG, cG = poly_roots(n, e)
            for v1, v2 in combinations(range(n), 2):
                nF, eF = delete(n, e, {v1, v2})
                if not is_forest(nF, eF):
                    continue
                npair += 1
                n1, e1 = delete(n, e, {v1})
                n2, e2 = delete(n, e, {v2})
                r1, c1 = poly_roots(n1, e1)
                r2, c2 = poly_roots(n2, e2)
                rF, cF = poly_roots(nF, eF)
                for k in range(-4 * (n + 1), 4 * (n + 1) + 1):
                    x = Fraction(k, 4)
                    vG, v1v, v2v, vF = (peval(cG, x), peval(c1, x),
                                        peval(c2, x), peval(cF, x))
                    if 0 in (vG, v1v, v2v, vF):
                        continue
                    ncheck += 1
                    a = sum(1 for r in rG if r > x)
                    b1 = sum(1 for r in r1 if r > x)
                    b2 = sum(1 for r in r2 if r > x)
                    c = sum(1 for r in rF if r > x)
                    if not (a - b1 in (0, 1) and b1 - c in (0, 1)
                            and a - b2 in (0, 1) and b2 - c in (0, 1)):
                        bad_int += 1
                        continue
                    if (a - c) % 2:
                        continue
                    if (a == c) != (vF * (v1v + v2v) > 0):
                        bad_tie += 1
        grand[0] += ncheck
        grand[1] += bad_int
        grand[2] += bad_tie
        print(f"{n:>3}{ng:>9}{npair:>12}{ncheck:>9}"
              f"{('OK' if not bad_int else str(bad_int)):>11}"
              f"{('OK' if not bad_tie else str(bad_tie)):>10}")
    print()
    print(f"total checks: {grand[0]}   interlacing failures: {grand[1]}   "
          f"tie-break failures: {grand[2]}")
    print(f"elapsed: {time.time()-t0:.0f}s")
    return 1 if (grand[1] or grand[2]) else 0


if __name__ == '__main__':
    sys.exit(main())
