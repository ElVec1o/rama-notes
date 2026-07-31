"""ff_step4.py -- what the cumulants can and cannot do.

(1) EXACT identity (proved by hand, re-verified symbolically here):
        kappa_n(mu) = a * kappa_n(psi_0),   n = 1,2,3,
    psi_0(x) = x^{p-p/b}(x-b)^{p/b},  at EVERY finite p; and kappa_4 is the
    first cumulant that is not universal.

(2) COROLLARY (no-go).  Psi := psi_0^{box_p a}.  If mu != Psi there is NO
    real-rooted rho with  mu = Psi box_p rho: the finite free deconvolution has
    kappa_1 = kappa_2 = 0, and kappa_2 = p/(p-1) * Var(roots), so a real-rooted
    rho would have all roots 0, i.e. rho = x^p and mu = Psi.
    => mu is never box_p-divisible by Psi, so no free-subadditivity argument
       against Psi can reach the band.  Checked numerically here.

(3) PARTIAL divisibility: is mu = psi_0^{box j} box_p rho_j real-rooted for
    j < a?   (kappa_2(rho_j) = (a-j) kappa_2(psi_0) > 0, so (2) does not apply.)

(4) The conjecture itself: exact verification of the tree band, with margins,
    including an adversarial search at b >= 3, and the mandatory regression that
    the scalar family A_k = (b/p)I is NOT covered.
"""
import sys
from fractions import Fraction

import numpy as np
import sympy as sp

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
from mcp2 import mcp                                                           # noqa
from frac_naimark import GRAPHS, nu_coeffs                                     # noqa
from dpp_rep import rand_proj_family, noncommutativity                         # noqa
from ff_step1 import psi_poly, signed_e_of_mu, band, graph_fams, rand_fams     # noqa


def psi0(p, b):
    m = p // b
    return F.signed_e_from_roots([Fraction(0)] * (p - m) + [Fraction(b)] * m)


def deconv(e, f, d):
    """the unique rho with e = f box_d rho (formal; real-rootedness not implied)."""
    ke, kf = F.kappa(e, d, d), F.kappa(f, d, d)
    kr = [Fraction(0)] + [ke[n] - kf[n] for n in range(1, d + 1)]
    return F.poly_from_kappa(kr, d)


def realrooted(e, d, tol=1e-7):
    r = np.roots(F.poly_from_signed_e(e, d))
    sc = max(1.0, float(np.max(np.abs(r))))
    return float(np.max(np.abs(r.imag))) < tol * sc, np.sort(r.real), \
        float(np.max(np.abs(r.imag))) / sc


def part1():
    print("=" * 90)
    print("(1) kappa_n(mu) == a * kappa_n(psi_0) for n=1,2,3, symbolically")
    print("=" * 90)
    p, a, b = sp.symbols('p a b', positive=True)
    m = p / b
    # kappa_n(psi_0) from E_i = C(m,i) b^i / C(p,i)
    E = [sp.Integer(1)]
    for i in (1, 2, 3):
        Ei = sp.simplify(sp.rf(m - i + 1, i) / sp.factorial(i) * b ** i
                         / (sp.rf(p - i + 1, i) / sp.factorial(i)))
        E.append(sp.simplify(Ei))
    kh = [sp.Integer(0)] * 4
    for n in range(3):
        acc = sum(sp.binomial(n, i - 1) * kh[i] * E[n + 1 - i] for i in range(1, n + 1))
        kh[n + 1] = sp.simplify(E[n + 1] - acc)
    kpsi = [sp.Integer(0)] + [sp.simplify((-1) ** (n - 1) * p ** (n - 1) * kh[n]
                                          / sp.factorial(n - 1)) for n in (1, 2, 3)]
    kmu = [sp.Integer(0), a, a * p * (b - 1) / (p - 1),
           a * p ** 2 * (b - 1) * (b - 2) / ((p - 1) * (p - 2))]
    for n in (1, 2, 3):
        print("   kappa_%d(psi_0) = %-34s  a*that - kappa_%d(mu) = %s"
              % (n, sp.simplify(kpsi[n]), n,
                 sp.simplify(a * kpsi[n] - kmu[n])))
    print()


def part2():
    print("=" * 90)
    print("(2) rho = mu deconv Psi   -- must have kappa_1 = kappa_2 = kappa_3 = 0")
    print("=" * 90)
    for name, p, q, a, b, e in graph_fams() + rand_fams():
        Psi = F.boxp_power(psi0(p, b), p, a)
        rho = deconv(e, Psi, p)
        kr = F.kappa(rho, p, min(5, p))
        rr, roots, im = realrooted(rho, p)
        print("  %-24s (%d,%d,%d,%d) kappa(rho)=%s  real-rooted=%s"
              % (name, p, q, a, b,
                 ["%.4g" % float(x) for x in kr[1:]], rr))
    print("  -> kappa_1=kappa_2=kappa_3=0 always; kappa_2 = p/(p-1)Var forces")
    print("     rho = x^p if real-rooted, i.e. mu = Psi.  NO-GO confirmed.")
    print()


def part3():
    print("=" * 90)
    print("(3) partial divisibility: mu = psi_0^{box j} box_p rho_j, j = 1..a-1")
    print("=" * 90)
    for name, p, q, a, b, e in graph_fams() + rand_fams():
        row = "  %-24s (%d,%d,%d,%d) real-rooted rho_j for j =" % (name, p, q, a, b)
        good = []
        for j in range(1, a):
            f = F.boxp_power(psi0(p, b), p, j)
            rho = deconv(e, f, p)
            rr, _, _ = realrooted(rho, p)
            if rr:
                good.append(j)
        print(row, good if good else "NONE")
    print()


def part4():
    print("=" * 90)
    print("(4) the conjecture itself -- EXACT root localisation, with margins")
    print("=" * 90)
    print("%-26s %-11s %-11s %-11s %-9s %-8s" %
          ("family", "lambda_min", "tree lo", "lambda_max", "tree hi", "sd below mean"))
    worst = None
    for name, p, q, a, b, e in graph_fams() + rand_fams():
        lo, hi = band(a, b)
        mn = F.minroot_exact(e, p, iters=50)
        mx = F.maxroot_exact(e, p, iters=50)
        sd = np.sqrt(a * (b - 1))
        z = (a - mn) / sd
        ok = mn >= lo - 1e-9 and mx <= hi + 1e-9
        slack = (mn - lo) / (hi - lo)
        if worst is None or slack < worst[1]:
            worst = (name, slack)
        print("  %-24s %11.6f %11.6f %11.6f %11.6f  %8.3f  ok=%s slack=%.4f"
              % (name, mn, lo, mx, hi, z, ok, slack))
    print("  tightest relative slack at the lower edge:", worst)
    print()


def part5():
    print("=" * 90)
    print("(5) MANDATORY REGRESSION -- scalar family A_k = (b/p) I  must FAIL")
    print("=" * 90)
    for (p, a, b) in [(6, 3, 2), (12, 3, 2), (24, 3, 2), (48, 3, 2), (96, 3, 2),
                      (192, 3, 2), (12, 4, 3), (24, 4, 3), (48, 4, 3), (96, 4, 3),
                      (24, 6, 4), (96, 6, 4)]:
        q = p * a // b
        e = F.scalar_family_e(p, q, a, b)
        mn = F.minroot_exact(e, p, iters=45)
        mx = F.maxroot_exact(e, p, iters=45)
        lo, hi = band(a, b)
        mpl, mph = (np.sqrt(a) - np.sqrt(b)) ** 2, (np.sqrt(a) + np.sqrt(b)) ** 2
        print("  p=%3d a=%d b=%d roots=[%9.6f,%9.6f] tree=[%8.5f,%8.5f] MP=[%8.5f,%8.5f]"
              "  violates lower=%s upper=%s"
              % (p, a, b, mn, mx, lo, hi, mpl, mph, mn < lo - 1e-9, mx > hi + 1e-9))
    print()


if __name__ == '__main__':
    import sys as _s
    which = _s.argv[1] if len(_s.argv) > 1 else 'all'
    if which in ('all', '1'):
        part1()
    if which in ('all', '2'):
        part2()
    if which in ('all', '3'):
        part3()
    if which in ('all', '4'):
        part4()
    if which in ('all', '5'):
        part5()
