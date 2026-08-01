"""ff_L6.py -- EXACT integer counterexamples to (L), checkable by hand.

Construction.  Look for a real-rooted
        rho(x) = x^{n0} (x - alpha)^{n1} (x - beta)^{n2} (x - gamma)^{n3},
                 n0 + n1 + n2 + n3 = p,
with alpha,beta,gamma positive INTEGERS and the three power sums forced:
        sum r_i   = p (a-1)
        sum r_i^2 = p [ (a-1)(b-1) + (a-1)^2 ]
        sum r_i^3 = p [ (a-1)(b-1)(b-2) + 3(a-1)^2(b-1) + (a-1)^3 ].
Those three linear equations in (n1,n2,n3) plus n0 = p - n1 - n2 - n3 fix the
multiplicities as rational multiples of p; choose p to clear denominators.

If in addition   n0 / p > 1/b,  then by Bercovici-Voiculescu
        (chi boxplus mu_rho)({0}) = (1 - 1/b) + n0/p - 1 > 0,
so min supp(chi boxplus mu_rho) = 0, i.e. L(mu_rho) = 0, while the tree edge
(sqrt(a-1)-sqrt(b-1))^2 is > 0 whenever a > b.  Claim (L) is FALSE.
"""
import sys
from fractions import Fraction
from itertools import combinations
from math import gcd, sqrt

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
import ff_L as X                                                               # noqa


def power_sum_targets(a, b):
    """per-root power sums S1/p, S2/p, S3/p forced by kappa_1,kappa_2,kappa_3."""
    m1 = Fraction(a - 1)
    mu2 = Fraction((a - 1) * (b - 1))
    mu3 = Fraction((a - 1) * (b - 1) * (b - 2))
    S1 = m1
    S2 = mu2 + m1 ** 2
    S3 = mu3 + 3 * m1 * mu2 + m1 ** 3
    return S1, S2, S3


def solve_mult(alpha, beta, gamma, a, b):
    """(n1,n2,n3,n0) as Fractions times p; None if singular."""
    S1, S2, S3 = power_sum_targets(a, b)
    A = [[Fraction(alpha), Fraction(beta), Fraction(gamma)],
         [Fraction(alpha) ** 2, Fraction(beta) ** 2, Fraction(gamma) ** 2],
         [Fraction(alpha) ** 3, Fraction(beta) ** 3, Fraction(gamma) ** 3]]
    rhs = [S1, S2, S3]
    # Gaussian elimination over Q
    M = [row[:] + [rhs[i]] for i, row in enumerate(A)]
    for c in range(3):
        piv = next((r for r in range(c, 3) if M[r][c] != 0), None)
        if piv is None:
            return None
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [M[r][k] - f * M[c][k] for k in range(4)]
    n = [M[i][3] for i in range(3)]
    n0 = Fraction(1) - sum(n)
    return n[0], n[1], n[2], n0


def search(a, b, hi=16, pmax=4000):
    """all integer triples giving a valid EXACT counterexample; smallest p first."""
    out = []
    for alpha, beta, gamma in combinations(range(1, hi + 1), 3):
        s = solve_mult(alpha, beta, gamma, a, b)
        if s is None:
            continue
        n1, n2, n3, n0 = s
        if min(n0, n1, n2, n3) <= 0:
            continue
        if n0 <= Fraction(1, b):
            continue
        den = 1
        for f in (n0, n1, n2, n3):
            den = den * f.denominator // gcd(den, f.denominator)
        p = den
        if p > pmax:
            continue
        mult = [int(n0 * p), int(n1 * p), int(n2 * p), int(n3 * p)]
        out.append((p, (alpha, beta, gamma), mult))
    out.sort()
    return out


def verify(p, pos, mult, a, b, verbose=True):
    """EXACT verification of everything that matters."""
    roots = ([Fraction(0)] * mult[0] + [Fraction(pos[0])] * mult[1]
             + [Fraction(pos[1])] * mult[2] + [Fraction(pos[2])] * mult[3])
    assert len(roots) == p
    e = F.signed_e_from_roots(roots)
    k = F.kappa(e, p, 4)
    k1t = Fraction(a - 1)
    k2t = (a - 1) * Fraction(p * (b - 1), p - 1)
    k3t = (a - 1) * Fraction(p * p * (b - 1) * (b - 2), (p - 1) * (p - 2))
    ok = (k[1] == k1t and k[2] == k2t and k[3] == k3t)
    lo, _ = X.tree_band(a, b)
    L = X.L_roots([float(r) for r in roots], b)
    atom_chi = Fraction(b - 1, b)
    atom_tau = Fraction(mult[0], p)
    surviving = atom_chi + atom_tau - 1
    if verbose:
        print("    rho(x) = x^%d (x-%d)^%d (x-%d)^%d (x-%d)^%d,  p = %d"
              % (mult[0], pos[0], mult[1], pos[1], mult[2], pos[2], mult[3], p))
        print("      forced kappa_1,2,3 EXACT : %s   (%s, %s, %s)"
              % (ok, k[1], k[2], k[3]))
        print("      kappa_4                  : %s = %.4f" % (k[4], float(k[4])))
        print("      roots in [0, ab=%d]       : %s   (max root %d)"
              % (a * b, max(pos) <= a * b, max(pos)))
        print("      chi({0}) + mu_rho({0}) - 1 = %s > 0  => atom of "
              "chi boxplus mu_rho at 0" % surviving)
        print("      L(mu_rho) = %.12f   tree edge = %.12f   (L) holds? %s"
              % (L, lo, L >= lo - 1e-9))
    return ok and surviving > 0 and L < lo - 1e-9


def main():
    print("=" * 100)
    print("[X] EXACT integer counterexamples to (L)")
    print("=" * 100)
    found = 0
    for (a, b) in [(4, 3), (5, 3), (6, 3), (6, 4), (10, 4), (9, 5), (12, 7),
                   (5, 4), (7, 5), (8, 6)]:
        lo, _ = X.tree_band(a, b)
        if lo <= 0:
            continue
        res = search(a, b)
        print("  (a,b) = (%d,%d)   tree edge = %.9f   1/b = %.6f"
              % (a, b, lo, 1.0 / b))
        if not res:
            print("    (no integer witness with alpha,beta,gamma <= 16, p <= 4000)")
            continue
        # prefer the smallest p that also fits inside [0, ab]
        inside = [r for r in res if max(r[1]) <= a * b]
        pick = inside[0] if inside else res[0]
        good = verify(*pick, a=a, b=b)
        found += good
        print("    VERIFIED counterexample:", good)
        print()
    print("  exact counterexamples verified:", found)


if __name__ == '__main__':
    main()
