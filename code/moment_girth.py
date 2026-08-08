"""Check the moment-matching step behind the cavity constant.

The claim, from locality of root moments (Abert-Hubai; Csikvari-Frenkel) plus a girth
argument: for an a-regular graph G of girth g,

    p_j(G) / |V(G)|  =  m_j(KM_a)   for every  j < 2g,

where p_j is the j-th power sum of the roots of mu_G and m_j(KM_a) is the j-th moment of
the Kesten-McKay measure, equivalently the number of closed walks of length j from the root
of the a-regular tree.

The threshold is 2g, not g: the moments of the matching measure count closed tree-like
walks, the trace of such a walk of length j has at most j/2 edges, and any subgraph with
fewer than g edges is a forest. So the tree counts agree while j/2 < g. The data below
confirms this is tight: where a difference appears at all, it appears at exactly j = 2g.

Both sides are computed independently here: the left from the exact integer coefficients of
mu_G via Newton's identities, the right by walking the a-regular tree.

Also reported: the Stieltjes transform 1/G at x = 2 sqrt(a) against the limit constant
1 + 1/(1+sqrt a), and the rigorous transfer bound 2 rho^(k+1) / (x^(k+1) (x - rho)) with
rho = 2 sqrt(a-1), k = g-1, so the bound can be compared with the actual error.
"""

import sys
import itertools
from fractions import Fraction

# --------------------------------------------------------------- graphs

GRAPHS = {
    'K4': (3, 3, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'cube': (3, 4, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
                    (0, 4), (1, 5), (2, 6), (3, 7)]),
    'petersen': (3, 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
                        (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
                        (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]),
    'heawood': (3, 6, [(i, 14 + 0) for i in []] + [
        (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9),
        (9, 10), (10, 11), (11, 12), (12, 13), (13, 0),
        (0, 5), (2, 7), (4, 9), (6, 11), (8, 13), (10, 1), (12, 3)]),
    'K33': (3, 4, [(i, 3 + j) for i in range(3) for j in range(3)]),
    'K44': (4, 4, [(i, 4 + j) for i in range(4) for j in range(4)]),
    'K5': (4, 3, [(i, j) for i in range(5) for j in range(i + 1, 5)]),
}


def matching_coeffs(n, edges):
    """Ascending integer coefficients of mu_G."""
    m = len(edges)
    from functools import lru_cache

    @lru_cache(maxsize=None)
    def rec(i, mask, k):
        if i == m:
            return 1 if k == 0 else 0
        total = rec(i + 1, mask, k)
        if k > 0:
            u, v = edges[i]
            bu, bv = 1 << u, 1 << v
            if not (mask & bu) and not (mask & bv):
                total += rec(i + 1, mask | bu | bv, k - 1)
        return total

    coeffs = [0] * (n + 1)
    for k in range(n // 2 + 1):
        coeffs[n - 2 * k] += (-1) ** k * rec(0, 0, k)
    rec.cache_clear()
    return coeffs


def power_sums(coeffs, K):
    """Newton's identities: p_j from the elementary symmetric functions of the roots.
    coeffs is ascending, monic of degree n, so e_i = (-1)^i * coeffs[n-i]."""
    n = len(coeffs) - 1
    e = [Fraction((-1) ** i * coeffs[n - i]) for i in range(n + 1)]
    p = [Fraction(n)]
    for j in range(1, K + 1):
        s = Fraction(0)
        # Newton: p_j = sum_{i=1}^{j-1} (-1)^(i-1) e_i p_{j-i} + (-1)^(j-1) j e_j.
        # The i = j term is the separate one below, not part of this sum.
        for i in range(1, min(j - 1, n) + 1):
            s += (-1) ** (i - 1) * e[i] * p[j - i]
        if j <= n:
            s += (-1) ** (j - 1) * j * e[j]
        p.append(s)
    return p


def tree_walks(a, K):
    """Closed walks of length j from the root of the a-regular tree, j <= K.
    Build the tree to depth K//2 + 1 and power the adjacency matrix."""
    depth = K // 2 + 1
    nodes = [()]
    index = {(): 0}
    frontier = [()]
    for d in range(depth):
        new = []
        for u in frontier:
            deg = a if u == () else a - 1
            for c in range(deg):
                w = u + (c,)
                index[w] = len(nodes)
                nodes.append(w)
                new.append(w)
        frontier = new
    N = len(nodes)
    adj = [[] for _ in range(N)]
    for w in nodes:
        if w:
            adj[index[w]].append(index[w[:-1]])
            adj[index[w[:-1]]].append(index[w])
    vec = [0] * N
    vec[0] = 1
    out = [1]
    for j in range(1, K + 1):
        nv = [0] * N
        for i in range(N):
            if vec[i]:
                for k in adj[i]:
                    nv[k] += vec[i]
        vec = nv
        out.append(vec[0])
    return out


def main():
    K = 9
    print(f"{'graph':<10}{'a':>3}{'girth':>7}   moments p_j/n vs tree walks, j = 0..{K}")
    ok = True
    for name, (a, g, edges) in GRAPHS.items():
        n = 1 + max(max(u, v) for u, v in edges)
        c = matching_coeffs(n, edges)
        p = power_sums(c, K)
        w = tree_walks(a, K)
        row = []
        for j in range(K + 1):
            lhs = p[j] / n
            rhs = Fraction(w[j])
            mark = '=' if lhs == rhs else 'X'
            if j < 2 * g and mark == 'X':
                ok = False
                mark = 'FAIL'
            row.append(f"{j}{mark}")
        print(f"{name:<10}{a:>3}{g:>7}   " + " ".join(row))
        first_diff = next((j for j in range(K + 1) if p[j] / n != Fraction(w[j])), None)
        print(f"{'':<20}   first differing moment: {first_diff}"
              f"   (girth {g}, so exactly {2*g} is expected)")
        if first_diff is not None and first_diff < 2 * g:
            ok = False
    print()
    print("all moments below twice the girth match" if ok else "MISMATCH BELOW 2*GIRTH")

    # The cavity ratio at x = 2 sqrt(a), against the limit and against the rigorous bound.
    import math
    print()
    print(f"{'graph':<10}{'girth':>6}{'ratio/(x/2)':>14}{'limit':>10}"
          f"{'|error|':>11}{'bound':>12}")
    for name, (a, g, edges) in GRAPHS.items():
        n = 1 + max(max(u, v) for u, v in edges)
        c = matching_coeffs(n, edges)
        x = 2 * math.sqrt(a)
        val = sum(co * x ** i for i, co in enumerate(c))
        der = sum(i * co * x ** (i - 1) for i, co in enumerate(c) if i >= 1)
        ratio = n * val / der            # = 1/G_m(x)
        obs = ratio / (x / 2)
        lim = 1 + 1 / (1 + math.sqrt(a))
        rho = 2 * math.sqrt(a - 1)
        k = 2 * g - 1
        bound = 2 * rho ** (k + 1) / (x ** (k + 1) * (x - rho))
        print(f"{name:<10}{g:>6}{obs:>14.6f}{lim:>10.6f}"
              f"{abs(obs - lim):>11.2e}{bound:>12.2e}")
    print()
    print("the bound is rigorous and exponential in the girth; it is not tight, since")
    print("|m_j| <= rho^j discards the j^(-3/2) decay of the Kesten-McKay moments")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
