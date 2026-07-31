"""ff_step3.py -- the payoff question.

(A)  LEMMA (proved here symbolically + numerically).  Let
         chi = (1 - 1/b) delta_0 + (1/b) delta_b .
     Then the support of the a-fold FREE convolution power chi^{boxplus a} is
     EXACTLY the tree band [ (sqrt(a-1)-sqrt(b-1))^2 , (sqrt(a-1)+sqrt(b-1))^2 ].
     (chi is the spectral distribution of b*Q, Q a rank-(1/b) projection; and
     chi = delta_1 + nu with nu = (1/b)delta_{b-1} + (1-1/b)delta_{-1}, exactly
     the centred slot spectrum of the crux.)

     CONSEQUENCE.  By the MSS finite-free bound
         lambda_max(f box_d g) <= right edge of supp(mu_f boxplus mu_g),
         lambda_min(f box_d g) >= left  edge of supp(mu_f boxplus mu_g),
     the polynomial  Psi = box_p^a ( x^{p-p/b}(x-b)^{p/b} )  satisfies the tree
     band FOR EVERY p.  Verified numerically here.

     So the tree band is EXACTLY "an a-fold free convolution POWER of chi",
     whereas every unconstrained method (barrier, compound free Poisson) yields
     a COMPOUND free Poisson of rate a with jump nu.  Those two agree only
     through the third cumulant; from the fourth on the power is strictly
     narrower.  That is the precise reason the closed routes overshoot.

(B)  The finite free a-th root of mu:  phi with kappa_n(phi) = kappa_n(mu)/a.
     If phi were real-rooted with root measure supported where chi is, MSS
     would give the band immediately.  Tested here.

(C)  Regression: the scalar family A_k = (b/p) I must FAIL.
"""
import sys
from fractions import Fraction

import numpy as np
import sympy as sp

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from ff_boxp import (boxp_power, kappa, poly_from_kappa, ff_root,             # noqa
                     signed_e_from_roots, poly_from_signed_e, moments_from_e)
from mcp2 import mcp                                                          # noqa
from frac_naimark import GRAPHS, nu_coeffs                                    # noqa
from dpp_rep import rand_proj_family, graph_family                            # noqa
from ff_step1 import psi_poly, signed_e_of_mu, rootrange, band, rand_fams, graph_fams  # noqa


# ======================================================================== (A)
def free_edges_chi_power(a, b):
    """edges of supp(chi^{boxplus a}) by solving K'(w) = 0,
    K(w) = 1/w + a R_chi(w),  R_chi(w) = 1 + (-1+(b-2)w+sqrt(b^2w^2+2(2-b)w+1))/(2w)."""
    w = sp.symbols('w', real=True)
    A, B = sp.Integer(a), sp.Integer(b)
    S = sp.sqrt(B ** 2 * w ** 2 + 2 * (2 - B) * w + 1)
    Rchi = 1 + (-1 + (B - 2) * w + S) / (2 * w)
    K = 1 / w + A * Rchi
    dK = sp.simplify(sp.diff(K, w))
    sols = sp.solve(sp.numer(sp.together(dK)), w)
    vals = []
    for s in sols:
        try:
            v = complex(sp.N(K.subs(w, s)))
            ws = complex(sp.N(s))
        except Exception:
            continue
        if abs(v.imag) < 1e-9 and abs(ws.imag) < 1e-9:
            vals.append(v.real)
    return sorted(set(round(v, 10) for v in vals))


def part_A():
    print("=" * 92)
    print("(A) supp( chi^{boxplus a} )  vs  the tree band")
    print("=" * 92)
    for (a, b) in [(3, 2), (4, 2), (5, 2), (4, 3), (5, 3), (6, 3), (6, 4), (7, 5),
                   (3, 3), (5, 5), (10, 3), (12, 7)]:
        v = free_edges_chi_power(a, b)
        lo, hi = band(a, b)
        print("  a=%2d b=%2d   K'(w)=0 critical values %s   tree band [%.8f, %.8f]  MATCH=%s"
              % (a, b, ["%.8f" % x for x in v], lo, hi,
                 (len(v) >= 2 and abs(min(v) - lo) < 1e-7 and abs(max(v) - hi) < 1e-7)))
    print()
    print("  Psi = box_p^a(x^{p-p/b}(x-b)^{p/b}) inside the tree band, for every p:")
    bad = 0
    for b in (2, 3, 4):
        for a in (b, b + 1, b + 2, b + 4):
            for p in [b * m for m in (1, 2, 3, 4, 6, 8, 12, 16, 24)]:
                e = psi_poly(p, a, b)
                lo_P, hi_P, im = rootrange(e, p)
                lo, hi = band(a, b)
                if im > 1e-6:
                    print("     !! Psi not real rooted a=%d b=%d p=%d" % (a, b, p))
                    bad += 1
                if lo_P < lo - 1e-9 or hi_P > hi + 1e-9:
                    print("     !! VIOLATION a=%d b=%d p=%d  [%.6f,%.6f] vs [%.6f,%.6f]"
                          % (a, b, p, lo_P, hi_P, lo, hi))
                    bad += 1
    print("     violations:", bad)
    # how tight is Psi at large p?
    print()
    print("  approach of lambda_min(Psi) to the tree edge:")
    for (a, b) in [(3, 2), (4, 3), (6, 4)]:
        lo, hi = band(a, b)
        row = "    a=%d b=%d edge=%.6f : " % (a, b, lo)
        for p in [b * m for m in (2, 4, 8, 16, 32, 64)]:
            e = psi_poly(p, a, b)
            lo_P, _, _ = rootrange(e, p)
            row += " p=%d:%.5f" % (p, lo_P)
        print(row)


# ======================================================================== (B)
def part_B():
    print()
    print("=" * 92)
    print("(B) the finite free a-th root phi of mu    (kappa_n(phi) = kappa_n(mu)/a)")
    print("=" * 92)
    print("%-26s %-11s %-24s %-26s" % ("family", "(p,q,a,b)", "roots(phi)",
                                       "chi support {0,b}"))
    for name, p, q, a, b, e in graph_fams() + rand_fams():
        phi = ff_root(e, p, a)
        r = np.roots(poly_from_signed_e(phi, p))
        im = float(np.max(np.abs(r.imag)))
        rr = np.sort(r.real)
        real = im < 1e-7 * max(1.0, float(np.max(np.abs(rr))))
        print("%-26s (%d,%d,%d,%d) real=%-5s [%9.5f,%9.5f] maxIm=%.2e   {0, %d}"
              % (name, p, q, a, b, real, rr.min(), rr.max(), im, b))


# ======================================================================== (C)
def part_C():
    print()
    print("=" * 92)
    print("(C) REGRESSION -- scalar family A_k = (b/p) I  (rank p, trace b, sum aI)")
    print("    it satisfies every PSD/trace/sum hypothesis and VIOLATES the tree band")
    print("=" * 92)
    for (p, a, b) in [(6, 3, 2), (12, 3, 2), (24, 3, 2), (48, 3, 2), (96, 3, 2),
                      (12, 4, 3), (24, 4, 3), (48, 4, 3)]:
        q = p * a // b
        A = np.array([np.eye(p) * (b / p) for _ in range(q)])
        mu = mcp(A)
        r = np.sort(np.roots(np.array([float(x) for x in mu])).real)
        lo, hi = band(a, b)
        mpl, mph = (np.sqrt(a) - np.sqrt(b)) ** 2, (np.sqrt(a) + np.sqrt(b)) ** 2
        print("  p=%3d a=%d b=%d  roots=[%8.5f,%8.5f]  tree=[%8.5f,%8.5f]  "
              "MP=[%8.5f,%8.5f]  VIOLATES tree band: lo=%s hi=%s"
              % (p, a, b, r.min(), r.max(), lo, hi, mpl, mph,
                 r.min() < lo - 1e-9, r.max() > hi + 1e-9))


if __name__ == '__main__':
    part_A()
    part_B()
    part_C()
