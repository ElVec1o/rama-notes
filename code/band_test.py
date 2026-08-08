"""Adversarial check of BAND, the step the abelian GAPCOUNT rests on.

BAND says the k-th largest root theta_k of mu_G lies in the k-th Floquet band
B_k = lam_k(T^b).  The proof draws on Marcus-Spielman-Srivastava: the +-1 edge
signings form an interlacing family averaging to mu_G, so the common
interlacing lemma brackets theta_k between lam_k(A_s) and lam_k(A_s') for two
signings, at EVERY index k, not only k = 1.  The general-k form is the load
bearing part and is what this script attacks.

For each graph it computes

    lo_k = min over signings of lam_k(A_s),
    hi_k = max over signings of lam_k(A_s),

and checks lo_k <= theta_k <= hi_k for every k.  A failure at any k would kill
the argument in RamaLean/BandTheorem.lean.

mu_G is built exactly from matching counts; the eigenvalue comparisons use a
tolerance of 1e-9, which is far above the conditioning of these matrices and far
below every observed slack.  The minimum observed slack is reported so the
tolerance can be judged rather than trusted.
"""

import sys
import itertools
import numpy as np
from numpy.polynomial import polynomial as P

TOL = 1e-9


def matching_poly_coeffs(n, edges):
    """Coefficients of mu_G, ascending, exact integers."""
    from itertools import combinations
    m = len(edges)
    coeffs = [0] * (n + 1)
    for k in range(0, n // 2 + 1):
        c = 0
        for S in combinations(range(m), k):
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


def roots_desc(coeffs):
    r = np.roots(list(reversed(coeffs)))
    assert np.max(np.abs(r.imag)) < 1e-7, "mu_G not real rooted numerically"
    return np.sort(r.real)[::-1]


def signing_bands(n, edges):
    """(lo, hi) arrays over all +-1 signings, eigenvalues sorted descending."""
    m = len(edges)
    lo = np.full(n, np.inf)
    hi = np.full(n, -np.inf)
    for bits in itertools.product((1.0, -1.0), repeat=m):
        A = np.zeros((n, n))
        for (u, v), s in zip(edges, bits):
            A[u, v] = s
            A[v, u] = s
        ev = np.sort(np.linalg.eigvalsh(A))[::-1]
        lo = np.minimum(lo, ev)
        hi = np.maximum(hi, ev)
    return lo, hi


GRAPHS = {
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K4+leaf': (8, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                    (0, 4), (1, 5), (2, 6), (3, 7)]),
    'C5': (5, [(i, (i + 1) % 5) for i in range(5)]),
    'K33': (6, [(i, 3 + j) for i in range(3) for j in range(3)]),
    'K34': (7, [(i, 3 + j) for i in range(3) for j in range(4)]),
    'bowtie': (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]),
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)]),
    'theta': (5, [(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4)]),
    'prism': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                  (0, 3), (1, 4), (2, 5)]),
    'cube': (8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
                 (0, 4), (1, 5), (2, 6), (3, 7)]),
    'petersen': (10, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
                      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
                      (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]),
}


def main():
    print(f"{'graph':<14}{'n':>3}{'|E|':>5}{'signings':>10}{'BAND':>7}{'min slack':>12}")
    worst = np.inf
    fails = 0
    for name, (n, edges) in GRAPHS.items():
        if len(edges) > 16:
            print(f"{name:<14}{n:>3}{len(edges):>5}{'skipped':>10}")
            continue
        theta = roots_desc(matching_poly_coeffs(n, edges))
        lo, hi = signing_bands(n, edges)
        slack = np.minimum(theta - lo, hi - theta)
        ok = np.all(slack > -TOL)
        worst = min(worst, slack.min())
        if not ok:
            fails += 1
            bad = np.where(slack <= -TOL)[0]
            for k in bad:
                print(f"   FAIL k={k+1}: lo={lo[k]:.9f} theta={theta[k]:.9f} hi={hi[k]:.9f}")
        print(f"{name:<14}{n:>3}{len(edges):>5}{2**len(edges):>10}"
              f"{('OK' if ok else 'FAIL'):>7}{slack.min():>12.2e}")
    print()
    print(f"failing graphs: {fails}   smallest slack anywhere: {worst:.3e}")
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
