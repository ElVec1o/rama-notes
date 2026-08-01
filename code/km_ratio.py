"""The cavity ratio at the threshold is 1 + 1/(1+sqrt a).  Backs prop:km.

Averaging the vertex identity over directions gives E_e F_{A^(e)} = F_A'/m, so the
direction-averaged ratio is Rbar = m F_A / F_A' = 1/G(x), G the Stieltjes transform of
the root measure of F_A.  For a coordinate family F_A is the matching polynomial, and for
a-regular graphs of growing girth its root measure tends to Kesten-McKay, with

    G(z) = 2(a-1) / ((a-2) z + a sqrt(z^2 - 4(a-1))).

At z = 2 sqrt a the radical is exactly 2, so 1/G = ((a-2) sqrt a + a)/(a-1) and, in units
of the threshold x/2 = sqrt a,

    Rbar/(x/2)  ->  (sqrt a + 2)/(sqrt a + 1)  =  1 + 1/(1 + sqrt a).

This script computes the left side exactly for regular graphs and shows the error decaying
with the girth.  Machine-checked arithmetic: RamaLean/KestenMcKay.lean.

Usage:  python3 km_ratio.py
"""
import math

import numpy as np


def matching_counts(n, edges):
    """m_k, the number of k-matchings, by DP over the set of covered vertices."""
    mk = [1] + [0] * (n // 2)
    cur = {0: 1}
    for k in range(1, n // 2 + 1):
        nxt = {}
        for mask, c in cur.items():
            for (u, v) in edges:
                bu, bv = 1 << u, 1 << v
                if mask & bu or mask & bv:
                    continue
                nm = mask | bu | bv
                nxt[nm] = nxt.get(nm, 0) + c
        if not nxt:
            break
        cur = nxt
        mk[k] = sum(nxt.values()) // math.factorial(k)   # each k-set counted k! times
    return mk


def mu_and_deriv(n, edges, x):
    """mu_G(x) = sum_k (-1)^k m_k x^{n-2k}, and its derivative."""
    co = np.zeros(n + 1)
    for k, v in enumerate(matching_counts(n, edges)):
        if n - 2 * k >= 0:
            co[2 * k] = ((-1) ** k) * v
    return float(np.polyval(co, x)), float(np.polyval(np.polyder(co), x))


def lcf(n, pat):
    E = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
    for i in range(n):
        E.add(tuple(sorted((i, (i + pat[i % len(pat)]) % n))))
    return sorted(E)


def circ(n, S):
    return sorted({tuple(sorted((i, (i + s) % n))) for i in range(n) for s in S})


def hypercube(k):
    n = 1 << k
    return sorted({tuple(sorted((i, i ^ (1 << b)))) for i in range(n) for b in range(k)})


FAMILIES = [
    ("cube Q3", hypercube(3), 4),
    ("Petersen", [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
                  (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)], 5),
    ("Heawood", lcf(14, [5, -5]), 6),
    ("Mobius-Kantor", lcf(16, [5, -5]), 6),
    ("Pappus", lcf(18, [5, 7, -7, 7, -7, -5]), 6),
    ("Desargues", lcf(20, [5, -5, 9, -9]), 6),
    ("Q4", hypercube(4), 4),
    ("C16(1,7)", circ(16, [1, 7]), 4),
    ("C20(1,9)", circ(20, [1, 9]), 4),
    ("C18(1,7,9)", circ(18, [1, 7, 9]), 4),
]


def main():
    print("Rbar/(x/2) = m mu(x) / (mu'(x) sqrt a) at x = 2 sqrt a, against 1 + 1/(1+sqrt a)")
    print(f"{'graph':22} {'m':>3} {'a':>2} {'girth':>5} {'exact':>11} {'predicted':>11} {'err':>10}")
    for nm, ed, g in FAMILIES:
        n = 1 + max(max(e) for e in ed)
        deg = [0] * n
        for u, v in ed:
            deg[u] += 1
            deg[v] += 1
        if min(deg) != max(deg):
            print(f"{nm:22} not regular")
            continue
        a = deg[0]
        x = 2 * math.sqrt(a)
        mu, dmu = mu_and_deriv(n, ed, x)
        ratio = (n * mu / dmu) / (x / 2)
        pred = 1 + 1 / (1 + math.sqrt(a))
        print(f"{nm:22} {n:3} {a:2} {g:5} {ratio:11.6f} {pred:11.6f} {ratio - pred:+10.2e}")
    print()
    print("The error decays with the girth, as Kesten-McKay convergence requires.")


if __name__ == "__main__":
    main()
