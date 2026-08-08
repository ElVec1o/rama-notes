"""A combinatorial meaning for mu_G(2 sqrt(d-1)), and its verification.

Peter Csikvari asked whether mu_G(2 sqrt(d-1)) has a combinatorial meaning for a d-regular
graph G of even order. It does, and it comes out of his own paper with Ferenc Bencs,
"Evaluations of Tutte polynomials of regular graphs" (arXiv:2105.06798).

Their polynomial is

    R_G(z) = sum over matchings M of (-z)^|M| prod_{v not covered} (z + d_v - 1).

For d-regular G this is a transformation of the matching polynomial: comparing coefficients,

    R_G(z) = z^(n/2) mu_G( (z + d - 1) / sqrt z ).                        (*)

The substitution has a double root exactly where we want it. Solving
(u^2 + d - 1)/u = 2 sqrt(d-1) for u = sqrt z gives u = sqrt(d-1) twice, so

    x = 2 sqrt(d-1)   corresponds to   z = d - 1.

Their Corollary 2.7 expands R_G at shifted argument as a weighted pseudo-forest count,

    R_G(w) = sum over pseudo-forests A of 2^{c(A)} (w-1)^{n - |A|},

where a pseudo-forest is an edge set each of whose components has at most one cycle, and
c(A) is the number of cycles. Putting w = d - 1 into that and (*) at z = d - 1:

    mu_G(2 sqrt(d-1)) = (d-1)^{-n/2} * sum over pseudo-forests A of 2^{c(A)} (d-2)^{n-|A|}

This script checks that identity by brute force: the left side from the matching counts,
the right side by enumerating every edge subset and testing the pseudo-forest condition.
Both sides are exact integers times an exact power, so the comparison is exact.

At d = 3 the weight (d-2)^{n-|A|} is 1 and the statement reduces to
    2^{n/2} mu_G(2 sqrt 2) = number of pseudo-forests counted with 2^{cycles}.
"""

import sys
from fractions import Fraction
from functools import lru_cache
from itertools import combinations


def matching_counts(n, edges):
    m = len(edges)

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

    out = [rec(0, 0, k) for k in range(n // 2 + 1)]
    rec.cache_clear()
    return out


def mu_at_edge_times_scale(n, edges, d):
    """(d-1)^(n/2) * mu_G(2 sqrt(d-1)), an exact integer for n even."""
    assert n % 2 == 0
    ms = matching_counts(n, edges)
    y = 4 * (d - 1)
    val = sum((-1) ** k * ms[k] * y ** ((n - 2 * k) // 2) for k in range(len(ms)))
    return val * (d - 1) ** (n // 2)


def components_and_cycles(n, subset):
    """Return (is_pseudo_forest, number_of_cycles) for an edge subset.

    A component with V vertices and E edges is a tree when E = V-1 and unicyclic when
    E = V; anything with E > V has more than one independent cycle."""
    par = list(range(n))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    for u, v in subset:
        ru, rv = find(u), find(v)
        if ru != rv:
            par[ru] = rv
    verts = {}
    edgec = {}
    used = set()
    for u, v in subset:
        used.add(u)
        used.add(v)
    for x in used:
        r = find(x)
        verts[r] = verts.get(r, 0) + 1
    for u, v in subset:
        r = find(u)
        edgec[r] = edgec.get(r, 0) + 1
    cycles = 0
    for r, ve in verts.items():
        ee = edgec.get(r, 0)
        if ee > ve:
            return False, 0
        if ee == ve:
            cycles += 1
    return True, cycles


def pseudoforest_sum(n, edges, d):
    """sum over pseudo-forests A of 2^{c(A)} (d-2)^{n-|A|}, exact."""
    total = 0
    m = len(edges)
    for bits in range(1 << m):
        sub = [edges[i] for i in range(m) if bits >> i & 1]
        ok, c = components_and_cycles(n, sub)
        if ok:
            total += 2 ** c * (d - 2) ** (n - len(sub))
    return total


GRAPHS = {
    'K4': (3, 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K33': (3, 6, [(i, 3 + j) for i in range(3) for j in range(3)]),
    'prism': (3, 6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                     (0, 3), (1, 4), (2, 5)]),
    'cube': (3, 8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
                    (0, 4), (1, 5), (2, 6), (3, 7)]),
    'petersen': (3, 10, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
                         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
                         (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]),
    'K44': (4, 8, [(i, 4 + j) for i in range(4) for j in range(4)]),
    'C8sq': (4, 8, [(i, (i + 1) % 8) for i in range(8)]
             + [(i, (i + 2) % 8) for i in range(8)]),
    # cubic on 6 vertices; d = 3, not 4.  Mislabelling the degree makes the identity
    # fail loudly, since R_G is built from the actual degrees while the transformation
    # to mu_G assumes regularity.  Kept as a sensitivity check.
    'cubic6': (3, 6, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5),
                      (3, 4), (3, 5), (4, 5)]),
    'wagner': (3, 8, [(i, (i + 1) % 8) for i in range(8)]
               + [(i, (i + 4) % 8) for i in range(4)]),
}


def main():
    print(f"{'graph':<12}{'d':>3}{'n':>4}{'(d-1)^(n/2) mu':>18}"
          f"{'pseudo-forest sum':>20}{'':>4}")
    ok = True
    for name, (d, n, edges) in GRAPHS.items():
        if n % 2:
            continue
        # The identity needs d-regularity: R_G is built from the actual degrees while the
        # transformation to mu_G assumes they are all d.  Assert it rather than trust the
        # label, since a mislabelled degree looks exactly like a counterexample.
        deg = [0] * n
        for u, v in edges:
            deg[u] += 1
            deg[v] += 1
        assert all(t == d for t in deg), (name, d, deg)
        lhs = mu_at_edge_times_scale(n, edges, d)
        rhs = pseudoforest_sum(n, edges, d)
        match = (lhs == rhs)
        ok = ok and match
        print(f"{name:<12}{d:>3}{n:>4}{lhs:>18}{rhs:>20}{'  OK' if match else '  FAIL':>4}")
    print()
    print("identity verified on all cases" if ok else "IDENTITY FAILS")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
