"""Adversarial check of the tie-break behind GAPCOUNT at feedback vertex number two.

At fvs 2 the Schur complement S(x) is 2x2 over C*_r(F_b), which is NOT projectionless, so
delta(x) = trace of its negative spectral projection can be 0, 1 or 2. Parity fixes the
count modulo 2 and therefore cannot separate delta = 0 from delta = 2. The claim is that
the sign of tau(S(x)) does, and that this trace is a matching-polynomial ratio:

    tau(S(x))  =  ( mu_{G-v1}(x) + mu_{G-v2}(x) ) / mu_{G-v1-v2}(x).

Combined with the target GAPCOUNT, delta(x) = N_G(x) - N_F(x), that yields a prediction
involving no operator algebra at all:

    whenever N_G(x) - N_F(x) is even, it is 0 exactly when tau(S(x)) > 0.

This script tests that. A failure would refute the tie-break in
RamaLean/FeedbackTwo.lean.

The prediction is only derived for x outside spec(T), where S(x) is invertible, and
spec(T) is not computable here. So violations are reported together with whether they lie
outside the Ramanujan interval [-rho, rho] of the universal cover, where the conclusion is
unconditional because S(x) is definite there. rho is bounded below by the largest root of
mu_G (Heilmann-Lieb), which is the best certificate available without building T.

All comparisons are exact: sample points are rationals, and matching polynomials have
integer coefficients.
"""

import sys
import itertools
from fractions import Fraction

FEEDBACK = {
    # name: (n, edges, (v1, v2)) with G - v1 - v2 a forest
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], (0, 1)),
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (0, 3)),
    'twotri_far': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (1, 4)),
    'K33': (6, [(i, 3 + j) for i in range(3) for j in range(3)], (0, 1)),
    'K34': (7, [(i, 3 + j) for i in range(3) for j in range(4)], (0, 1)),
    'prism': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                  (0, 3), (1, 4), (2, 5)], (0, 4)),
    'K5minus': (5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4),
                    (2, 3), (2, 4)], (0, 1)),
    'theta_plus': (6, [(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4), (4, 5), (5, 0)],
                   (0, 4)),
    'bowtie2': (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)], (2, 0)),
    'cube': (8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
                 (0, 4), (1, 5), (2, 6), (3, 7)], (0, 6)),
}


def matching_poly(n, edges):
    """Ascending integer coefficients of mu_G."""
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


def peval(coeffs, x):
    return sum(Fraction(c) * x ** i for i, c in enumerate(coeffs))


def delete(n, edges, vs):
    keep = [u for u in range(n) if u not in vs]
    idx = {u: i for i, u in enumerate(keep)}
    e2 = [(idx[a], idx[b]) for (a, b) in edges if a not in vs and b not in vs]
    return len(keep), e2


def is_forest(n, edges):
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru == rv:
            return False
        parent[ru] = rv
    return True


def count_above(coeffs, x):
    """Number of roots above x, via Sturm-free sign counting on an exact grid is not
    reliable; instead use the exact real-root isolation of sympy."""
    from sympy import Poly, symbols, real_roots
    X = symbols('X')
    p = Poly(sum(c * X ** i for i, c in enumerate(coeffs)), X)
    return sum(1 for r in real_roots(p) if r > x)


def main():
    print(f"{'graph':<14}{'forest?':>9}{'points':>8}{'even pts':>10}"
          f"{'viol':>6}{'viol outside HL':>17}")
    total_viol = 0
    total_outside = 0
    for name, (n, edges, (v1, v2)) in FEEDBACK.items():
        nF, eF = delete(n, edges, {v1, v2})
        forest = is_forest(nF, eF)
        cG = matching_poly(n, edges)
        cF = matching_poly(nF, eF)
        n1, e1 = delete(n, edges, {v1})
        n2, e2 = delete(n, edges, {v2})
        c1 = matching_poly(n1, e1)
        c2 = matching_poly(n2, e2)

        from sympy import Poly, symbols, real_roots
        X = symbols('X')
        rootsG = real_roots(Poly(sum(c * X ** i for i, c in enumerate(cG)), X))
        rho_lb = max([float(r) for r in rootsG]) if rootsG else 0.0

        pts = [Fraction(k, 8) for k in range(-8 * (n + 2), 8 * (n + 2) + 1)]
        npts = 0
        neven = 0
        viol = 0
        viol_out = 0
        for x in pts:
            vF = peval(cF, x)
            vG = peval(cG, x)
            if vF == 0 or vG == 0:
                continue
            npts += 1
            NG = count_above(cG, x)
            NF = count_above(cF, x)
            d = NG - NF
            if d % 2 != 0:
                continue
            neven += 1
            tr = (peval(c1, x) + peval(c2, x)) / vF
            pred = (d == 0)
            obs = (tr > 0)
            if pred != obs:
                viol += 1
                if abs(float(x)) > rho_lb:
                    viol_out += 1
        total_viol += viol
        total_outside += viol_out
        print(f"{name:<14}{str(forest):>9}{npts:>8}{neven:>10}{viol:>6}{viol_out:>17}")
    print()
    print(f"total tie-break violations: {total_viol}")
    print(f"of those, outside the Heilmann-Lieb interval (unconditional zone): "
          f"{total_outside}")
    return 1 if total_outside else 0


if __name__ == '__main__':
    sys.exit(main())
