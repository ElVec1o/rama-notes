"""ff_step0.py -- STEP 0 kill test.

QUESTION.  Is  mu[P_1..P_q]  equal to the finite free convolution
box_p of the characteristic polynomials  x^{p-b}(x-1)^b  of the P_k ?

Also: self-tests of the box_p implementation.
"""
import sys
from fractions import Fraction
from math import comb

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from ff_boxp import (boxp, boxp_power, kappa, khat, signed_e_from_roots,       # noqa
                     poly_from_signed_e, proj_charpoly, moments_from_e)
from mixed_char_poly import mixed_char_poly, mixed_char_poly_exact             # noqa
from frac_naimark import GRAPHS, degrees_ok, nu_coeffs                         # noqa
from mcp2 import mcp                                                           # noqa
from dpp_rep import rand_proj_family, noncommutativity, graph_family           # noqa


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def mp_band(a, b):
    """Marchenko-Pastur band of the SCALAR family A_k = (b/p) I."""
    s, t = np.sqrt(a), np.sqrt(b)
    return (s - t) ** 2, (s + t) ** 2


def fp_band(a):
    """free Poisson rate a, jump 1: the box_p (independent Haar) limit."""
    return (np.sqrt(a) - 1) ** 2, (np.sqrt(a) + 1) ** 2


# =====================================================================
# 0.  self tests of box_p
# =====================================================================
def self_tests():
    print("=" * 72)
    print("SELF-TESTS of box_p")
    print("=" * 72)
    d = 6
    # (x-s)^d box (x-t)^d = (x-s-t)^d
    e1 = signed_e_from_roots([Fraction(3)] * d)
    e2 = signed_e_from_roots([Fraction(-5, 2)] * d)
    got = boxp(e1, e2, d)
    want = signed_e_from_roots([Fraction(1, 2)] * d)
    print("  (x-3)^d box (x+5/2)^d == (x-1/2)^d :", got == want)

    # identity element x^d
    ed = [Fraction(1)] + [Fraction(0)] * d
    r = signed_e_from_roots([Fraction(i) for i in range(1, d + 1)])
    print("  f box x^d == f                     :", boxp(r, ed, d) == r)

    # box_d against the Haar definition: E_U det(xI - A - U B U^*)
    rng = np.random.default_rng(11)
    dd = 4
    A = np.diag([1.0, 2.0, -1.0, 0.5])
    B = np.diag([3.0, 0.0, 0.0, -2.0])
    eA = signed_e_from_roots([Fraction(x).limit_denominator(10 ** 6)
                              for x in np.diag(A)])
    eB = signed_e_from_roots([Fraction(x).limit_denominator(10 ** 6)
                              for x in np.diag(B)])
    pred = poly_from_signed_e(boxp(eA, eB, dd), dd)
    acc = np.zeros(dd + 1)
    N = 400000
    for _ in range(N):
        X = rng.standard_normal((dd, dd))
        Q, R = np.linalg.qr(X)
        Q = Q * np.sign(np.diag(R))
        acc += np.poly(A + Q @ B @ Q.T)
    acc /= N
    print("  Haar Monte-Carlo (N=%d) vs box_d:" % N)
    print("     predicted:", np.array2string(pred, precision=5))
    print("     empirical:", np.array2string(acc, precision=5))
    print("     max |diff|: %.4g" % np.abs(pred - acc).max())

    # cumulant sanity
    d = 8
    roots = [Fraction(i) for i in [1, 1, 2, 3, 5, 8, 13, 21]]
    e = signed_e_from_roots(roots)
    k = kappa(e, d, 4)
    m = moments_from_e(e, d, 2)
    var = m[1] - m[0] ** 2
    print("  kappa_1 == mean of roots           :", k[1] == m[0])
    print("  kappa_2 == d/(d-1) * variance      :",
          k[2] == Fraction(d, d - 1) * var)
    # additivity
    e2 = signed_e_from_roots([Fraction(j) for j in range(8)])
    kc = kappa(boxp(e, e2, d), d, 5)
    ka = kappa(e, d, 5)
    kb = kappa(e2, d, 5)
    print("  additivity kappa(f box g) = ka + kb :",
          all(kc[n] == ka[n] + kb[n] for n in range(1, 6)))
    print()


# =====================================================================
# 1.  the families
# =====================================================================
def families():
    out = []

    # --- S(K_4): p=4, q=6, a=3, b=2  (graph / commuting)
    adj, p, q, a, b = GRAPHS['S(K_4)']
    P = graph_family(adj, p, q, a, b)
    out.append(('S(K_4) graph (p,q,a,b)=(4,6,3,2)', P, p, q, a, b))

    # --- cube design: p=6, q=8, a=4, b=3  (graph / commuting)
    adj, p, q, a, b = GRAPHS['cube (4,3)-design']
    P = graph_family(adj, p, q, a, b)
    out.append(('cube design (6,8,4,3)', P, p, q, a, b))

    # --- K_{3,4}:  p=3,q=4,a=4,b=3
    adj, p, q, a, b = GRAPHS['K_{3,4}']
    P = graph_family(adj, p, q, a, b)
    out.append(('K_{3,4} (3,4,4,3)', P, p, q, a, b))

    # --- noncommuting (4,6,3,2)
    Pn, r = rand_proj_family(4, 6, 3, 2, seed=5)
    out.append(('noncommuting (4,6,3,2) resid=%.1e' % r, Pn, 4, 6, 3, 2))

    # --- noncommuting (6,8,4,3)
    Pn, r = rand_proj_family(6, 8, 4, 3, seed=9)
    out.append(('noncommuting (6,8,4,3) resid=%.1e' % r, Pn, 6, 8, 4, 3))

    return out


def signed_e_of_mu(mu):
    """mcp returns c[0..p] with mu(y) = sum_m c[m] y^{p-m} and c[m] = (-1)^m e_m."""
    p = len(mu) - 1
    return [(-1) ** m * mu[m] for m in range(p + 1)]


def main():
    self_tests()

    print("=" * 72)
    print("STEP 0:   mu[P]   vs   box_p of  x^{p-b}(x-1)^b   (q factors)")
    print("=" * 72)
    for name, P, p, q, a, b in families():
        mu = mcp(np.asarray(P, dtype=float))
        e_mu = signed_e_of_mu(mu)
        e_box = boxp_power(proj_charpoly(p, b), p, q)
        box_num = poly_from_signed_e(e_box, p)
        mu_num = np.array([(-1) ** m * float(e_mu[m]) * (-1) ** m
                           for m in range(p + 1)])
        mu_num = np.array([float(mu[m]) for m in range(p + 1)])

        print("\n--- %s" % name)
        print("    e_i(mu) :", ["%.6g" % float(x) for x in e_mu])
        print("    e_i(box):", ["%.6g" % float(x) for x in e_box])
        eq = all(abs(float(e_mu[i]) - float(e_box[i])) < 1e-7 * max(1.0, abs(float(e_box[i])))
                 for i in range(p + 1))
        print("    EQUAL? ", eq)
        rm = np.sort(np.roots(mu_num).real)
        rb = np.sort(np.roots(box_num).real)
        lo, hi = band(a, b)
        print("    roots(mu) :", np.array2string(rm, precision=5))
        print("    roots(box):", np.array2string(rb, precision=5))
        print("    tree band [%.5f, %.5f]   MP band [%.5f, %.5f]  "
              "freePoisson(a) band [%.5f, %.5f]"
              % (lo, hi, *mp_band(a, b), *fp_band(a)))
        # first coefficient where they differ
        for i in range(p + 1):
            if abs(float(e_mu[i]) - float(e_box[i])) > 1e-7 * max(1.0, abs(float(e_box[i]))):
                print("    first differing coefficient: e_%d   mu=%.8g  box=%.8g"
                      % (i, float(e_mu[i]), float(e_box[i])))
                break


if __name__ == '__main__':
    main()
