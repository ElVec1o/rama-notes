"""Check the window hypothesis behind GAPCOUNT at feedback vertex number one.

The proof needs mu_{G-v} to interlace mu_G, so that

    N_G(x) - N_{G-v}(x)  in  {0, 1}   for every x,

where N_p(x) counts roots of p above x.  Equivalently the roots alternate:

    theta_1(G) >= theta_1(G-v) >= theta_2(G) >= theta_2(G-v) >= ...

Classically this is Cauchy interlacing transported through Godsil's path tree, which
realises mu_G and mu_{G-v} as the characteristic polynomials of a tree and of that tree
with its root deleted.  This script checks it directly, over every vertex of every test
graph, so that the hypothesis carried by RamaLean/FeedbackGapCount.lean is not taken on
trust.

Graphs with feedback vertex number one are included on purpose (flowers, theta graphs,
K_{2,q}, bowtie), since those are the ones the theorem applies to, but the check is run on
everything.
"""

import sys
import itertools
from sympy import Poly, symbols, real_roots, Rational

X = symbols('X')


def matching_poly_coeffs(n, edges):
    """Coefficients of mu_G, ascending, exact integers."""
    m = len(edges)
    coeffs = [0] * (n + 1)
    for k in range(0, n // 2 + 1):
        c = 0
        for S in itertools.combinations(range(m), k):
            used = set()
            ok = True
            for i in S:
                u, v = edges[i]
                if u in used or v in used:
                    ok = False
                    break
                used.add(u)
                used.add(v)
            if ok:
                c += 1
        coeffs[n - 2 * k] += (-1) ** k * c
    return coeffs


def roots_desc(n, edges):
    """Exact real roots, descending, with multiplicity.  Exact arithmetic is required:
    3K_2 has triple roots at +-1, where floating point loses six digits."""
    if n == 0:
        return []
    c = matching_poly_coeffs(n, edges)
    p = Poly(sum(co * X ** i for i, co in enumerate(c)), X)
    rs = real_roots(p)
    assert len(rs) == n, (n, len(rs))
    return sorted(rs, reverse=True)


def delete_vertex(n, edges, v):
    """Return (n-1, edges) with v removed and vertices renumbered."""
    keep = [u for u in range(n) if u != v]
    idx = {u: i for i, u in enumerate(keep)}
    e2 = [(idx[a], idx[b]) for (a, b) in edges if a != v and b != v]
    return n - 1, e2


def interlaces(big, small):
    """big has n roots, small has n-1; check big_1 >= small_1 >= big_2 >= ...
    Comparisons are exact, so the verdict is a proof for these instances."""
    n = len(big)
    if len(small) != n - 1:
        return False, None
    ok = True
    worst = None
    for k in range(n - 1):
        if not (big[k] >= small[k] and small[k] >= big[k + 1]):
            ok = False
        for d in (big[k] - small[k], small[k] - big[k + 1]):
            fd = float(d)
            worst = fd if worst is None else min(worst, fd)
    return ok, worst


GRAPHS = {
    'flower3': (7, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0),
                    (0, 5), (5, 6), (6, 0)]),
    'theta': (5, [(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4)]),
    'bowtie': (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]),
    'K25': (7, [(0, 2 + j) for j in range(5)] + [(1, 2 + j) for j in range(5)]),
    'K23': (5, [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]),
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K4+leaf': (8, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                    (0, 4), (1, 5), (2, 6), (3, 7)]),
    'K34': (7, [(i, 3 + j) for i in range(3) for j in range(4)]),
    'petersen': (10, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
                      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
                      (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]),
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)]),
    'prism': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                  (0, 3), (1, 4), (2, 5)]),
}


def main():
    print(f"{'graph':<15}{'n':>3}{'vertices tested':>17}{'window':>9}{'min slack':>12}")
    fails = 0
    tested = 0
    globalworst = None
    for name, (n, edges) in GRAPHS.items():
        big = roots_desc(n, edges)
        ok_all = True
        worst = None
        for v in range(n):
            n2, e2 = delete_vertex(n, edges, v)
            small = roots_desc(n2, e2)
            ok, w = interlaces(big, small)
            worst = w if worst is None else (worst if w is None else min(worst, w))
            tested += 1
            if not ok:
                ok_all = False
                print(f"   FAIL {name} at v={v}: slack {w}")
        globalworst = worst if globalworst is None else (globalworst if worst is None else min(globalworst, worst))
        if not ok_all:
            fails += 1
        print(f"{name:<15}{n:>3}{n:>17}{('OK' if ok_all else 'FAIL'):>9}{worst:>12.2e}")
    print()
    print(f"(graph, vertex) pairs tested: {tested}   failing graphs: {fails}")
    print(f"smallest interlacing slack anywhere: {globalworst:.3e}")
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
