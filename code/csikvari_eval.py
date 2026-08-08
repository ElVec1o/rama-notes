"""mu_G(2 sqrt(d-1)) for d-regular graphs with an even number of vertices.

Peter Csikvari asks (personal communication, August 2026) whether this value has a
combinatorial meaning, noting it should be a positive integer. The integrality and
positivity are settled in RamaLean/EvenEval.lean: with |V(G)| even every exponent in
mu_G is even, so mu_G is a polynomial in x^2 with integer coefficients, and x^2 = 4(d-1)
is an integer; positivity holds because Heilmann-Lieb is strict on a finite graph, so the
evaluation point is above every root of a monic polynomial.

What is NOT settled is any combinatorial meaning. This script just computes the numbers
exactly, with their factorisations, so that a pattern can be looked for.

All arithmetic is exact integer arithmetic: the value is P(4(d-1)) where
P(y) = sum_k (-1)^k m_k y^((n-2k)/2), and m_k are the matching counts.
"""

import sys
from functools import lru_cache
from sympy import factorint


def matching_counts(n, edges):
    """m_k = number of k-matchings, exact."""
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


def eval_at_edge(n, edges, d):
    """mu_G(2 sqrt(d-1)) as an exact integer, requires n even."""
    assert n % 2 == 0, "vertex count must be even"
    y = 4 * (d - 1)
    ms = matching_counts(n, edges)
    return sum((-1) ** k * ms[k] * y ** ((n - 2 * k) // 2) for k in range(len(ms)))


def cycle(n):
    return [(i, (i + 1) % n) for i in range(n)]


CUBIC = {
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K33': (6, [(i, 3 + j) for i in range(3) for j in range(3)]),
    'prism': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                  (0, 3), (1, 4), (2, 5)]),
    'cube': (8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
                 (0, 4), (1, 5), (2, 6), (3, 7)]),
    'petersen': (10, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
                      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
                      (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]),
    'heawood': (14, cycle(14) + [(0, 5), (2, 7), (4, 9), (6, 11), (8, 13),
                                 (10, 1), (12, 3)]),
    'moebius-kantor': (16, cycle(16) + [(i, (i + 5) % 16) for i in range(0, 16, 2)]),
    'pappus': (18, cycle(18) + [(0, 5), (6, 11), (12, 17), (2, 13), (8, 1), (14, 7),
                                (4, 9), (10, 15), (16, 3)]),
}

QUARTIC = {
    'K5': (5, [(i, j) for i in range(5) for j in range(i + 1, 5)]),          # odd, skipped
    'K44': (8, [(i, 4 + j) for i in range(4) for j in range(4)]),
    'C8^2': (8, cycle(8) + [(i, (i + 2) % 8) for i in range(8)]),
    'K33xK2': (12, None),
}


def show(name, n, edges, d):
    if n % 2:
        print(f"{name:<16}{n:>4}   skipped, odd vertex count")
        return
    v = eval_at_edge(n, edges, d)
    f = factorint(v)
    fs = " * ".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(f.items()))
    print(f"{name:<16}{n:>4}{v:>16}   = {fs}")


def main():
    print("d = 3, evaluation at 2*sqrt(2), so x^2 = 8")
    print(f"{'graph':<16}{'n':>4}{'mu_G(2 sqrt 2)':>16}")
    for name, (n, edges) in CUBIC.items():
        show(name, n, edges, 3)
    print()
    print("d = 4, evaluation at 2*sqrt(3), so x^2 = 12")
    print(f"{'graph':<16}{'n':>4}{'mu_G(2 sqrt 3)':>16}")
    for name, val in QUARTIC.items():
        if val[1] is None:
            continue
        n, edges = val
        show(name, n, edges, 4)
    print()
    print("integrality and positivity: RamaLean/EvenEval.lean")
    print("combinatorial meaning: open, nothing here bears on it")
    return 0


if __name__ == '__main__':
    sys.exit(main())
