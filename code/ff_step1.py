"""ff_step1.py -- the CONDITIONED finite free convolution.

STEP 0 killed  mu = box_p^q ( x^{p-b}(x-1)^b )  (independent Haar rotations of
the q slots).  The reason is structural, and it points at the right object.

THE REGROUPING.  Randomise each slot to rank one: w_k = sqrt(b) u_k with u_k
uniform on an orthonormal basis of range(P_k); then E w_k w_k^* = P_k and
mu(y) = E det( y I - sum_k w_k w_k^* ).
Suppose the frame splits into  a  ORTHOGONAL GROUPS  G_1..G_a, i.e.
sum_{k in G_i} P_k = I_p for each i (so |G_i| = p/b, and the ranges inside a
group are mutually orthogonal).  Within one group the chosen unit vectors u_k,
k in G_i, are MUTUALLY ORTHOGONAL, hence

        sum_{k in G_i} w_k w_k^*  =  b Q_i ,   Q_i a rank-(p/b) PROJECTION

DETERMINISTICALLY -- the randomness only moves Q_i around.  So

        mu(y) = E det( y I - b(Q_1 + ... + Q_a) ),   Q_i independent.

CONDITIONED FINITE FREE CONVOLUTION.  The Haar-independent version of that is

        Psi_{p,a,b}  :=  box_p^{ a } ( x^{p - p/b} (x - b)^{p/b} ) .

Its d->oo limit measure is  chi^{boxplus a},  chi = (1-1/b) delta_0 + (1/b) delta_b,
i.e.  delta_a  +  nu^{boxplus a}  with  nu = (1/b)delta_{b-1} + (1-1/b)delta_{-1}
-- exactly the centred slot spectrum from the crux -- and the support of that is
EXACTLY the tree band [ (sqrt(a-1)-sqrt(b-1))^2 , (sqrt(a-1)+sqrt(b-1))^2 ].

This file tests, numerically:
   (H1)  mu[P] == Psi_{p,a,b} ?
   (H2)  roots(mu[P]) contained in [minroot(Psi), maxroot(Psi)] ?
   (H3)  the cumulants of Psi vs the universal cumulants of mu.
   (H4)  the scalar family A_k = (b/p) I  must VIOLATE (H2)  (regression test).
"""
import sys
from fractions import Fraction
from math import comb

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from ff_boxp import (boxp_power, kappa, signed_e_from_roots,                  # noqa
                     poly_from_signed_e)
from mcp2 import mcp                                                          # noqa
from frac_naimark import GRAPHS, nu_coeffs, degrees_ok                        # noqa
from dpp_rep import rand_proj_family, graph_family, noncommutativity          # noqa
from mixed_char_poly import mixed_char_poly                                   # noqa


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def psi_poly(p, a, b):
    """box_p^a of  x^{p - p/b} (x-b)^{p/b}   (requires b | p)."""
    assert p % b == 0, (p, b)
    m = p // b
    roots = [Fraction(0)] * (p - m) + [Fraction(b)] * m
    e = signed_e_from_roots(roots)
    return boxp_power(e, p, a)


def signed_e_of_mu(mu):
    p = len(mu) - 1
    return [(-1) ** m * mu[m] for m in range(p + 1)]


def rootrange(e, p):
    r = np.roots(poly_from_signed_e(e, p))
    return float(np.min(r.real)), float(np.max(r.real)), float(np.max(np.abs(r.imag)))


# ------------------------------------------------------------------ families
def graph_fams():
    out = []
    for name, (adj, p, q, a, b) in GRAPHS.items():
        if p % b:
            continue
        c = nu_coeffs(adj, p, q)
        e = [Fraction((-1) ** m * c[p - m]) for m in range(p + 1)]
        out.append(('G ' + name, p, q, a, b, e))
    return out


def rand_fams():
    out = []
    for (p, q, a, b, seed) in [(4, 6, 3, 2, 5), (4, 6, 3, 2, 17), (4, 6, 3, 2, 101),
                               (6, 9, 3, 2, 3), (6, 9, 3, 2, 77),
                               (8, 12, 3, 2, 4), (6, 8, 4, 3, 9), (6, 8, 4, 3, 23),
                               (6, 12, 4, 2, 33), (4, 8, 4, 2, 31),
                               (6, 10, 5, 3, 12), (8, 12, 6, 4, 41),
                               (6, 15, 5, 2, 55), (8, 20, 5, 2, 66),
                               (6, 18, 6, 2, 71), (9, 12, 4, 3, 81),
                               (8, 16, 6, 3, 91), (10, 15, 3, 2, 13)]:
        if p % b or p * a != q * b:
            continue
        P, r = rand_proj_family(p, q, a, b, seed=seed)
        if r > 1e-10:
            continue
        e = [Fraction(x).limit_denominator(10 ** 10)
             for x in signed_e_of_mu(mcp(np.asarray(P, float)))]
        out.append(('R (%d,%d,%d,%d) s%d' % (p, q, a, b, seed), p, q, a, b, e))
    return out


def scalar_family(p, q, a, b):
    """A_k = (b/p) I -- rank p, trace b, sum = aI: satisfies every
    PSD+trace+sum hypothesis but is NOT a projection family.  Its roots reach
    the Marchenko-Pastur band, which is strictly wider than the tree band.
    Any machinery that 'proves' the tree band for this family is broken."""
    A = np.array([np.eye(p) * (b / p) for _ in range(q)])
    return signed_e_of_mu(mcp(A))


def main():
    print("=" * 92)
    print("STEP 1:   mu[P]   vs   Psi = box_p^a ( x^{p-p/b}(x-b)^{p/b} )")
    print("=" * 92)
    print("%-26s %-9s %-30s %-30s" % ("family", "(p,q,a,b)", "roots(mu)  [min,max]",
                                      "roots(Psi) [min,max]"))
    cache = {}
    ok_all = True
    eq_any = False
    for name, p, q, a, b, e in graph_fams() + rand_fams():
        key = (p, a, b)
        if key not in cache:
            cache[key] = psi_poly(p, a, b)
        ePsi = cache[key]
        lo_m, hi_m, im_m = rootrange(e, p)
        lo_P, hi_P, im_P = rootrange(ePsi, p)
        equal = all(abs(float(e[i] - ePsi[i])) < 1e-6 * max(1.0, abs(float(ePsi[i])))
                    for i in range(p + 1))
        eq_any |= equal
        inside = (lo_m >= lo_P - 1e-9) and (hi_m <= hi_P + 1e-9)
        ok_all &= inside
        tl, th = band(a, b)
        print("%-26s (%d,%d,%d,%d) [%9.5f,%9.5f]  [%9.5f,%9.5f]  "
              "tree[%8.5f,%8.5f]  equal=%s inside=%s"
              % (name, p, q, a, b, lo_m, hi_m, lo_P, hi_P, tl, th, equal, inside))
    print()
    print("  (H1) mu == Psi ever?          :", eq_any)
    print("  (H2) roots(mu) inside roots(Psi) for every family tested:", ok_all)
    print()

    print("=" * 92)
    print("(H4) REGRESSION: the scalar family A_k = (b/p) I  (violates the tree band)")
    print("=" * 92)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (8, 12, 6, 4),
                         (12, 18, 3, 2), (10, 15, 3, 2)]:
        if p % b or p * a != q * b:
            continue
        e = [Fraction(x).limit_denominator(10 ** 10) for x in scalar_family(p, q, a, b)]
        lo_m, hi_m, _ = rootrange(e, p)
        ePsi = psi_poly(p, a, b)
        lo_P, hi_P, _ = rootrange(ePsi, p)
        tl, th = band(a, b)
        mpl, mph = (np.sqrt(a) - np.sqrt(b)) ** 2, (np.sqrt(a) + np.sqrt(b)) ** 2
        print("  (p,q,a,b)=(%2d,%2d,%d,%d)  roots(scalar)=[%8.5f,%8.5f]  "
              "Psi=[%8.5f,%8.5f]  tree=[%8.5f,%8.5f]  MP=[%8.5f,%8.5f]  "
              "scalar inside Psi? %s"
              % (p, q, a, b, lo_m, hi_m, lo_P, hi_P, tl, th, mpl, mph,
                 lo_m >= lo_P - 1e-9 and hi_m <= hi_P + 1e-9))
    print()

    print("=" * 92)
    print("(H3) cumulants:  Psi   vs   mu (universal part)   vs   limit")
    print("=" * 92)
    for (p, a, b) in [(4, 3, 2), (6, 3, 2), (8, 3, 2), (12, 3, 2), (24, 3, 2),
                      (6, 4, 3), (12, 4, 3), (24, 4, 3), (8, 6, 4), (24, 6, 4)]:
        ePsi = psi_poly(p, a, b)
        kP = kappa(ePsi, p, min(6, p))
        # universal cumulants of mu
        k1 = Fraction(a)
        k2 = Fraction(a * p * (b - 1), p - 1)
        k3 = Fraction(a * p * p * (b - 1) * (b - 2), (p - 1) * (p - 2))
        print("  p=%2d a=%d b=%d  Psi kappa = %s" %
              (p, a, b, ["%.6g" % float(x) for x in kP[1:]]))
        print("               mu  kappa_1..3 = %s   (limit %s)" %
              (["%.6g" % float(x) for x in (k1, k2, k3)],
               ["%.6g" % float(x) for x in (a, a * (b - 1), a * (b - 1) * (b - 2))]))


if __name__ == '__main__':
    main()
