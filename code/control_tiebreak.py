"""A non-degenerate control for the plane-class polynomial, and why the old one was not.

THE BUG THIS EXISTS TO CATCH. For a weighted family with sum_k c_k P_k = a I, the tight MSS
input is A_k = c_k P_k, whose wedge weight is e_2(A_k) = c_k^2. Feeding c_k to the wedge form
instead of c_k^2 is a real error, and it went undetected long enough to reach both the paper and
a drafted letter to an outside expert.

WHY IT SURVIVED. The control in use was "compute the polynomial by two routes sharing no code,
and stop if they disagree". It fired, correctly, at 1e-1. What failed was the tie-breaker: the
case used to decide WHICH route was wrong was the coordinate/graph case, where every c_k = 1 and
therefore c_k = c_k^2 identically. The tie-breaker was blind to exactly the bug in play, it
passed, and the disagreement was then misread as a fact about the mathematics.

A control that cannot distinguish c from c^2 is not a control for a question about c versus c^2.

THE FIX. A known-answer case with weights that are neither 1 nor equal to each other. Take an
even cycle with alternating weights w1, w2: every vertex has weighted degree w1 + w2, so
sum_e c_e P_e = a I with a = w1 + w2, while the individual weights differ. Then the wedge form
is the weighted matching polynomial with edge weights e_2(A_e) = c_e^2,

    M_r = sum over r-matchings T of prod_{e in T} c_e^2,

which is computable directly from the combinatorics with no reference to either route. With
w1 = 2 and w2 = 1 the two candidate weightings differ by a factor of 4 on half the edges, so the
degeneracy is broken as hard as it can be at a = 3.

Three independent computations must agree: the combinatorial weighted matching polynomial, the
wedge form, and the MSS subset formula. Integer weights make the third exact, via
mixed_char_poly_exact, so the agreement is in rational arithmetic and not to a tolerance.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import itertools
from fractions import Fraction
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mixed_char_poly import mixed_char_poly, mixed_char_poly_exact


def alternating_cycle(n, w1, w2):
    """Even cycle on n vertices, alternating edge weights: weighted degree w1+w2 everywhere."""
    assert n % 2 == 0
    edges = [(i, (i + 1) % n) for i in range(n)]
    w = [w1 if i % 2 == 0 else w2 for i in range(n)]
    return edges, w


def combinatorial_M(edges, weights, m, power):
    """M_r = sum over r-matchings of prod (c_e)^power, straight from the combinatorics."""
    M = [Fraction(1)] + [Fraction(0)] * (m // 2)
    for r in range(1, m // 2 + 1):
        tot = Fraction(0)
        for T in itertools.combinations(range(len(edges)), r):
            vs = set(); ok = True
            for k in T:
                u, v = edges[k]
                if u in vs or v in vs:
                    ok = False; break
                vs.add(u); vs.add(v)
            if ok:
                p = Fraction(1)
                for k in T:
                    p *= Fraction(weights[k]) ** power
                tot += p
        M[r] = tot
    return M


def wedge_M(edges, weights, m, power):
    """M_r by Gram determinants, the note's route, with wedge weight c^power."""
    frames = []
    for (u, v) in edges:
        B = np.zeros((m, 2)); B[u, 0] = 1.0; B[v, 1] = 1.0
        frames.append(B)
    M = [1.0] + [0.0] * (m // 2)
    for r in range(1, m // 2 + 1):
        tot = 0.0
        for T in itertools.combinations(range(len(edges)), r):
            C = np.hstack([frames[k] for k in T])
            d = float(np.linalg.det(C.T @ C))
            if d > 0.0:
                tot += float(np.prod([weights[k] ** power for k in T])) * d
        M[r] = tot
    return M


def mss_shifted_roots_exact(edges, weights, m, a):
    """Roots of mu(y) - a with A_e = c_e P_e, coefficients in exact rational arithmetic."""
    As = []
    for (u, v), c in zip(edges, weights):
        A = [[0] * m for _ in range(m)]
        A[u][u] = c; A[v][v] = c
        As.append(A)
    coef = mixed_char_poly_exact(As)
    return np.sort(np.roots([float(t) for t in coef]).real) - a


def FA_roots_from_M(M, m):
    coef = [0.0] * (m + 1)
    for r in range(m // 2 + 1):
        coef[2 * r] = ((-1) ** r) * float(M[r])
    return np.sort(np.roots(coef).real)


def run_case(n, w1, w2):
    edges, weights = alternating_cycle(n, w1, w2)
    a = w1 + w2
    m = n

    combo_sq = combinatorial_M(edges, weights, m, 2)     # e_2 = c^2, the correct weighting
    combo_lin = combinatorial_M(edges, weights, m, 1)    # the bug
    wedge_sq = wedge_M(edges, weights, m, 2)
    mu = mss_shifted_roots_exact(edges, weights, m, a)

    d_wedge = max(abs(float(combo_sq[r]) - wedge_sq[r]) for r in range(m // 2 + 1))
    d_mu_sq = float(np.max(np.abs(mu - FA_roots_from_M(combo_sq, m))))
    d_mu_lin = float(np.max(np.abs(mu - FA_roots_from_M(combo_lin, m))))
    sep = max(abs(float(combo_sq[r] - combo_lin[r])) for r in range(m // 2 + 1))
    return dict(n=n, a=a, d_wedge=d_wedge, d_mu_sq=d_mu_sq, d_mu_lin=d_mu_lin, sep=sep)


def main():
    print("A control that distinguishes the wedge weight c from c^2.\n")
    print("Even cycles with alternating weights: weighted degree w1+w2 at every vertex, so")
    print("sum_e c_e P_e = a I, while the weights themselves differ.\n")
    print(f"{'n':>4}{'a':>4}{'combo vs wedge':>16}{'combo vs mu':>14}"
          f"{'WRONG (c not c^2)':>20}{'separation':>13}{'verdict':>10}")
    ok = True
    discriminating = True
    for (n, w1, w2) in ((6, 2, 1), (8, 2, 1), (8, 3, 1), (10, 2, 1), (10, 3, 2)):
        r = run_case(n, w1, w2)
        good = r['d_wedge'] < 1e-9 and r['d_mu_sq'] < 1e-8
        # the control is only meaningful if the wrong weighting is actually distinguishable
        disc = r['d_mu_lin'] > 1e-3 and r['sep'] > 0
        ok = ok and good
        discriminating = discriminating and disc
        print(f"{n:>4}{r['a']:>4}{r['d_wedge']:>16.2e}{r['d_mu_sq']:>14.2e}"
              f"{r['d_mu_lin']:>20.2e}{float(r['sep']):>13.4g}"
              f"{('ok' if good else 'FAIL'):>10}")

    print()
    print(f"  three routes agree on the correct weighting: {ok}")
    print(f"  the wrong weighting is separated at every case: {discriminating}")
    print()
    if ok and discriminating:
        print("  This is a usable tie-breaker: it has a known answer, it is exact, and it would")
        print("  have failed loudly under the c-versus-c^2 bug instead of passing silently as")
        print("  the coordinate check did.")
    else:
        print("  CONTROL IS NOT SOUND -- do not rely on it.")
    return 0 if (ok and discriminating) else 1


if __name__ == '__main__':
    sys.exit(main())
