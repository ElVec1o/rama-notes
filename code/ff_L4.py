"""ff_L4.py -- (i) mandatory regression, (ii) what genuine rho actually look
like, (iii) how far the counterexamples can be pushed (LP over the moment
class), (iv) an adversarial re-verification of the MSS bound.
"""
import sys
from fractions import Fraction
from math import sqrt

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
import ff_L as X                                                               # noqa
import ff_L2 as Y                                                              # noqa
import ff_L3 as W                                                              # noqa
from mcp2 import mcp                                                           # noqa
from dpp_rep import rand_proj_family, noncommutativity                         # noqa
from ff_step1 import signed_e_of_mu                                            # noqa


# ============================================================ [R] REGRESSION
def regression():
    """A_k = (b/p) I_p: PSD, trace b, sum a I, but NOT projections; its roots
    reach the Marchenko-Pastur band, strictly wider than the tree band.
    Anything proved here must fail for it.  WHICH hypothesis fails?"""
    print("=" * 104)
    print("[R] MANDATORY REGRESSION -- the scalar family A_k = (b/p) I_p")
    print("=" * 104)
    print("  %-14s %-10s %-10s %-11s %-11s %-9s %s" %
          ("(p,a,b)", "lmin(mu)", "tree lo", "MP lo", "violates", "rho r.r.?",
           "L(mu_rho) / why the argument cannot apply"))
    for (p, a, b) in [(6, 3, 2), (12, 3, 2), (24, 3, 2), (48, 3, 2),
                      (12, 4, 3), (24, 4, 3), (48, 4, 3),
                      (24, 6, 4), (48, 6, 4), (30, 5, 3), (60, 5, 3)]:
        q = p * a // b
        e = F.scalar_family_e(p, q, a, b)
        lo, _ = X.tree_band(a, b)
        mpl = (sqrt(a) - sqrt(b)) ** 2
        mn = F.minroot_exact(e, p, iters=45)
        rho = Y.deconv(e, Y.psi0(p, b), p)
        r = np.roots(F.poly_from_signed_e(rho, p))
        sc = max(1.0, float(np.max(np.abs(r))))
        im = float(np.max(np.abs(r.imag)))
        rr = im / sc < 1e-7
        k = F.kappa(rho, p, 3)
        k1t, k2t = Fraction(a - 1), (a - 1) * Fraction(p * (b - 1), p - 1)
        k3t = (a - 1) * Fraction(p * p * (b - 1) * (b - 2), (p - 1) * (p - 2))
        forced = (k[1] == k1t and k[2] == k2t and k[3] == k3t)
        if rr:
            L = X.L_roots(np.sort(r.real), b)
            why = "L=%.5f (>= tree? %s)" % (L, L >= lo - 1e-9)
        else:
            why = "rho NOT real-rooted, max|Im|=%.3e -> (D) FAILS" % im
        which = "".join(("." if ok else str(i + 1))
                        for i, ok in enumerate([k[1] == k1t, k[2] == k2t,
                                                k[3] == k3t]))
        print("  (%2d,%d,%d)      %10.6f %10.6f %11.6f %-11s %-9s forced123=%-5s"
              "[bad:%s]  %s"
              % (p, a, b, mn, lo, mpl, mn < lo - 1e-9, "YES" if rr else "NO",
                 forced, which, why))
    print("  ([bad:...] lists which of kappa_1,kappa_2,kappa_3 of rho are NOT the")
    print("   forced value; '...' means all three are forced.)")
    print()


# ================================================== [G] genuine rho, b >= 3
def rand_families(specs):
    out = []
    for (p, q, a, b, seed) in specs:
        if p % b or p * a != q * b or q > 22:
            continue
        P, r = rand_proj_family(p, q, a, b, seed=seed)
        if r > 1e-10:
            continue
        e = [Fraction(x).limit_denominator(10 ** 12)
             for x in signed_e_of_mu(mcp(np.asarray(P, float)))]
        nc = noncommutativity(np.asarray(P, float))
        out.append(('R(%d,%d,%d,%d)s%d' % (p, q, a, b, seed), p, q, a, b, e, nc))
    return out


def genuine_survey():
    print("=" * 116)
    print("[G] genuine projection families: is (L) doing any work beyond "
          "min supp(mu_rho) >= tree edge?")
    print("=" * 116)
    specs = []
    for seed in (1, 2, 3, 4, 5, 6):
        specs += [(6, 8, 4, 3, seed), (9, 12, 4, 3, seed), (12, 16, 4, 3, seed),
                  (6, 10, 5, 3, seed), (9, 15, 5, 3, seed), (6, 12, 6, 3, seed),
                  (8, 12, 6, 4, seed), (8, 10, 5, 4, seed), (12, 15, 5, 4, seed),
                  (10, 12, 6, 5, seed), (12, 18, 6, 4, seed),
                  (4, 6, 3, 2, seed), (6, 9, 3, 2, seed), (8, 12, 3, 2, seed),
                  (6, 12, 4, 2, seed), (10, 15, 3, 2, seed)]
    cases = rand_families(specs)
    nrr = nL = nmin = ntot = 0
    rows = []
    for nm, p, q, a, b, e, nc in cases:
        rho = Y.deconv(e, Y.psi0(p, b), p)
        r = np.roots(F.poly_from_signed_e(rho, p))
        sc = max(1.0, float(np.max(np.abs(r))))
        rr = float(np.max(np.abs(r.imag))) / sc < 1e-7
        ntot += 1
        lo, _ = X.tree_band(a, b)
        if not rr:
            rows.append((nm, p, q, a, b, None, None, lo, nc))
            continue
        nrr += 1
        rts = np.sort(r.real)
        L = X.L_roots(rts, b)
        nL += (L >= lo - 1e-9)
        nmin += (rts.min() >= lo - 1e-9)
        rows.append((nm, p, q, a, b, rts.min(), L, lo, nc))
    print("  %-18s %-11s %-10s %-10s %-10s %-8s %-8s" %
          ("family", "(p,q,a,b)", "min rho", "L(mu_rho)", "tree lo",
           "gain", "noncomm"))
    for (nm, p, q, a, b, mn, L, lo, nc) in rows:
        if mn is None:
            print("  %-18s (%2d,%2d,%d,%d)  rho NOT real-rooted -> (D) fails"
                  % (nm, p, q, a, b))
            continue
        print("  %-18s (%2d,%2d,%d,%d) %10.5f %10.5f %10.5f %8.5f %8.2e  "
              "minsupp>=tree=%-5s (L)=%s"
              % (nm, p, q, a, b, mn, L, lo, L - mn, nc, mn >= lo - 1e-9,
                 L >= lo - 1e-9))
    print("  totals: %d families, %d with rho real-rooted, %d satisfy (L), "
          "%d already have min supp(mu_rho) >= tree edge"
          % (ntot, nrr, nL, nmin))
    print()


# ============================== [P] how far can the counterexample be pushed
def max_atom_lp(c, C, a, b, n=4001):
    """LP:  max tau({c})  over measures on the grid [c,C] with the forced
    m1, m2, m3.  (Exact truncated-Hausdorff answer up to grid resolution.)"""
    m1, mu2, mu3 = X.forced_moments(a, b)
    M1 = m1
    M2 = mu2 + m1 ** 2
    M3 = mu3 + 3 * m1 * mu2 + m1 ** 3
    xs = np.linspace(c, C, n)
    A = np.vstack([np.ones(n), xs, xs ** 2, xs ** 3])
    bvec = np.array([1.0, M1, M2, M3])
    obj = np.zeros(n)
    obj[0] = -1.0                                   # maximise weight at x = c
    res = linprog(obj, A_eq=A, b_eq=bvec, bounds=[(0, 1)] * n, method='highs')
    if not res.success:
        return None, None
    w = res.x
    keep = w > 1e-9
    return float(w[0]), (xs[keep], w[keep])


def push():
    print("=" * 104)
    print("[P] does an UPPER support bound rescue (L)?   supp(tau) in [c, ab]")
    print("=" * 104)
    print("  %-8s %-9s %-11s %-9s %-9s %s" %
          ("(a,b)", "c", "max atom@c", "1/b", "tree lo", "verdict"))
    for (a, b) in [(3, 2), (4, 2), (5, 2), (4, 3), (5, 3), (6, 3), (7, 3),
                   (6, 4), (10, 4), (9, 5), (12, 7), (20, 9)]:
        lo, _ = X.tree_band(a, b)
        C = float(a * b)
        best = None
        for c in np.linspace(max(0.0, lo - 1.2), lo * 0.999 - 1e-9, 25):
            if c >= lo:
                continue
            s, sup = max_atom_lp(c, C, a, b)
            if s is None:
                continue
            if s > 1.0 / b + 1e-9:
                best = (c, s, sup)
        if best is None:
            s0, _ = max_atom_lp(max(0.0, lo - 1e-9) if lo > 0 else lo - 1.0,
                                C, a, b)
            print("  (%2d,%d)   %-9s %-11s %-9.5f %-9.5f  no atom mechanism "
                  "inside [0,ab]" % (a, b, "-", "%.5f" % (s0 or -1), 1.0 / b, lo))
            continue
        c, s, sup = best
        print("  (%2d,%d)   %9.5f %11.5f %9.5f %9.5f  (L) FAILS with supp in "
              "[%.3f, %.3f]" % (a, b, c, s, 1.0 / b, lo, sup[0].min(), sup[0].max()))
    print()


# ============================== [M] adversarial re-verification of MSS
def verify_mss(trials=60, seed=11):
    """lambda_min(f box_d g) >= sup_{w<0}[K_f + K_g - 1/w], on hard instances:
    heavily clustered roots, near-degenerate spectra, and the psi_0 family."""
    print("=" * 104)
    print("[M] adversarial re-verification of the MSS free lower bound")
    print("=" * 104)
    rng = np.random.default_rng(seed)

    def edge(rf, rg, d):
        def Fv(ws):
            return (X.K_atomic(ws, rf, np.ones(len(rf)) / len(rf))
                    + X.K_atomic(ws, rg, np.ones(len(rg)) / len(rg)) - 1.0 / ws)
        lg_lo, lg_hi = np.log(1e-9), np.log(1e7)
        best = min(rf) + min(rg)
        for _ in range(7):
            lg = np.linspace(lg_lo, lg_hi, 700)
            v = Fv(-np.exp(lg))
            i = int(np.argmax(v))
            best = max(best, float(v[i]))
            lg_lo, lg_hi = lg[max(i - 1, 0)], lg[min(i + 1, 699)]
        return best

    fails, worst = 0, np.inf
    for t in range(trials):
        d = int(rng.integers(3, 11))
        style = t % 3
        if style == 0:
            rf = np.sort(rng.normal(0, 1, d))
            rg = np.sort(rng.normal(0, 1, d))
        elif style == 1:                     # heavy clustering (atoms)
            rf = np.sort(rng.choice([0.0, 1.0, 3.0], d))
            rg = np.sort(rng.choice([0.0, 2.0], d))
        else:                                # projection-like
            rf = np.sort(np.concatenate([np.zeros(d - max(1, d // 3)),
                                         np.full(max(1, d // 3), 3.0)]))
            rg = np.sort(rng.uniform(0, 4, d))
        ef = F.signed_e_from_roots([Fraction(x).limit_denominator(10 ** 9)
                                    for x in rf])
        eg = F.signed_e_from_roots([Fraction(x).limit_denominator(10 ** 9)
                                    for x in rg])
        conv = F.boxp(ef, eg, d)
        lmin = float(np.min(np.roots(F.poly_from_signed_e(conv, d)).real))
        bnd = edge(rf, rg, d)
        slack = lmin - bnd
        worst = min(worst, slack)
        if slack < -1e-7:
            fails += 1
            print("   FAIL d=%d  lmin=%.8f  bound=%.8f" % (d, lmin, bnd))
    # the sharp case: psi_0 box_p psi_0 ... a times
    print("   random/clustered trials=%d failures=%d  min slack=%.3e"
          % (trials, fails, worst))
    print("   sharp case  Psi = psi_0^{box_p a}:  lambda_min(Psi) vs tree edge")
    for (a, b) in [(3, 2), (4, 3), (6, 4)]:
        lo, _ = X.tree_band(a, b)
        for p in (b * 2, b * 6, b * 20):
            e = F.boxp_power(Y.psi0(p, b), p, a)
            mn = F.minroot_exact(e, p, iters=50)
            print("      (a,b)=(%d,%d) p=%3d  lambda_min=%.8f  free edge=%.8f"
                  "  slack=%.2e" % (a, b, p, mn, lo, mn - lo))
    print()


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', 'R'):
        regression()
    if which in ('all', 'G'):
        genuine_survey()
    if which in ('all', 'P'):
        push()
    if which in ('all', 'M'):
        verify_mss()
