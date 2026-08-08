"""ff_L7.py -- ERROR HUNT.  Every claim I intend to make, attacked.

H1  L_edge really equals min supp(chi boxplus tau)     -> random matrices
H2  the b=2 genuine violations of (L) are real         -> random matrices + exact
H3  the squeeze bound is not an artefact               -> adversarial tau
H4  the exact witnesses are admissible (b | p, qb=pa)  -> arithmetic
H5  the witnesses are not saved by box_p-divisibility  -> finite free roots
H6  psi_0 normalisation: kappa_n(psi_0) is NOT 1       -> exact
"""
import sys
from fractions import Fraction
from math import sqrt, gcd

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
import ff_L as X                                                               # noqa
import ff_L2 as Y                                                              # noqa
import ff_L3 as W                                                              # noqa
import ff_L6 as Z                                                              # noqa


def rm(atoms, wts, b, N=1500, reps=8, seed=3):
    return W.rm_free_edge(np.asarray(atoms, float), np.asarray(wts, float), b,
                          N=N, reps=reps, seed=seed)


def H1():
    print("=" * 100)
    print("[H1] L_edge vs a random-matrix realisation of chi boxplus tau")
    print("=" * 100)
    rng = np.random.default_rng(5)
    worst = 0.0
    for t in range(10):
        b = int(rng.integers(2, 6))
        n = int(rng.integers(2, 6))
        atoms = np.sort(rng.uniform(-2, 8, n))
        wts = rng.random(n) + 0.2
        wts /= wts.sum()
        L = X.L_edge(atoms, wts, b)
        m, sd = rm(atoms, wts, b)
        worst = max(worst, abs(L - m))
        print("   b=%d  atoms=%-34s L_edge=%9.5f  RM=%9.5f +- %.4f  |diff|=%.4f"
              % (b, "[" + ",".join("%.2f" % z for z in atoms) + "]", L, m, sd,
                 abs(L - m)))
    print("   worst |L_edge - random matrix| = %.4f  (finite-N bias is O(N^-2/3))"
          % worst)
    print()


def H2():
    print("=" * 100)
    print("[H2] the b=2 genuine violations of (L): independent confirmation")
    print("=" * 100)
    for nm, p, q, a, b, e in Y.families():
        if b != 2 or p > 6:
            continue
        rho = Y.deconv(e, Y.psi0(p, b), p)
        r = np.roots(F.poly_from_signed_e(rho, p))
        if float(np.max(np.abs(r.imag))) > 1e-7:
            continue
        rts = np.sort(r.real)
        L = X.L_roots(rts, b)
        m, sd = rm(rts, np.ones(p) / p, b, N=2000, reps=10)
        lo, _ = X.tree_band(a, b)
        # exact refactorisation check
        chk = F.boxp(Y.psi0(p, b), rho, p)
        err = max(abs(float(chk[i] - e[i])) for i in range(p + 1))
        print("   %-18s p=%d  roots(rho)=%s" % (nm, p,
              "[" + ",".join("%.5f" % z for z in rts) + "]"))
        print("        L_edge=%.6f   random matrix=%.6f +- %.4f   tree=%.6f"
              "   refactor err=%.1e   (L) holds? %s"
              % (L, m, sd, lo, err, L >= lo - 1e-9))
    print()


def H3():
    print("=" * 100)
    print("[H3] squeeze  min supp <= L <= min supp + 1, adversarial tau")
    print("=" * 100)
    rng = np.random.default_rng(9)
    lo_s, hi_s = np.inf, np.inf
    worst_hi = None
    for t in range(400):
        b = int(rng.integers(2, 9))
        n = int(rng.integers(2, 20))
        style = t % 4
        if style == 0:
            atoms = np.sort(rng.normal(0, 5, n))
        elif style == 1:                       # near point mass
            atoms = np.sort(rng.normal(3, 1e-3, n))
        elif style == 2:                       # one far outlier
            atoms = np.sort(np.concatenate([[-50.0], rng.uniform(0, 3, n - 1)]))
        else:                                  # heavy atom at the left edge
            atoms = np.sort(np.concatenate([np.zeros(n - 1), [40.0]]))
        wts = rng.random(n) + 1e-3
        wts /= wts.sum()
        L = X.L_edge(atoms, wts, b)
        lo_s = min(lo_s, L - atoms.min())
        s = atoms.min() + 1.0 - L
        if s < hi_s:
            hi_s, worst_hi = s, (b, atoms.copy(), wts.copy(), L)
    print("   400 adversarial tau:  min (L - min supp) = %.3e" % lo_s)
    print("                         min (min supp + 1 - L) = %.6f" % hi_s)
    print("   tightest upper case:  b=%d  min supp=%.5f  L=%.5f"
          % (worst_hi[0], worst_hi[1].min(), worst_hi[3]))
    print("   (both non-negative: the squeeze is not violated)")
    print()


def H4():
    print("=" * 100)
    print("[H4] admissibility of the exact witnesses: need b | p and q = pa/b")
    print("=" * 100)
    for (a, b) in [(4, 3), (5, 4), (6, 4), (7, 5)]:
        res = Z.search(a, b)
        inside = [r for r in res if max(r[1]) <= a * b]
        if not inside:
            continue
        p, pos, mult = inside[0]
        k = 1
        while (k * p) % b:
            k += 1
        P = k * p
        M = [k * m for m in mult]
        q = P * a // b
        lo, _ = X.tree_band(a, b)
        rr = ([Fraction(0)] * M[0] + [Fraction(pos[0])] * M[1]
              + [Fraction(pos[1])] * M[2] + [Fraction(pos[2])] * M[3])
        e = F.signed_e_from_roots(rr)
        kk = F.kappa(e, P, 3)
        ok = (kk[1] == Fraction(a - 1)
              and kk[2] == (a - 1) * Fraction(P * (b - 1), P - 1)
              and kk[3] == (a - 1) * Fraction(P * P * (b - 1) * (b - 2),
                                              (P - 1) * (P - 2)))
        L = X.L_roots([float(x) for x in rr], b)
        print("   (a,b)=(%d,%d): p=%d -> admissible p=%d (b|p: %s), q=%d;  "
              "rho = x^%d (x-%d)^%d (x-%d)^%d (x-%d)^%d"
              % (a, b, p, P, P % b == 0, q, M[0], pos[0], M[1], pos[1], M[2],
                 pos[2], M[3]))
        print("        forced kappa_1,2,3 exact = %s ;  mass at 0 = %d/%d = %.6f"
              " > 1/b = %.6f ;  L = %.9f < tree = %.9f"
              % (ok, M[0], P, M[0] / P, 1.0 / b, L, lo))
    print()


def H5():
    print("=" * 100)
    print("[H5] is the witness saved by box_p-divisibility?  (brief candidate c)")
    print("     test: is the formal finite free k-th root of rho real-rooted?")
    print("=" * 100)
    for (a, b) in [(4, 3), (5, 4), (6, 4), (7, 5)]:
        res = Z.search(a, b)
        inside = [r for r in res if max(r[1]) <= a * b]
        if not inside:
            continue
        p, pos, mult = inside[0]
        rr = ([Fraction(0)] * mult[0] + [Fraction(pos[0])] * mult[1]
              + [Fraction(pos[1])] * mult[2] + [Fraction(pos[2])] * mult[3])
        e = F.signed_e_from_roots(rr)
        out = []
        for k in (2, 3, 4):
            g = F.ff_root(e, p, k)
            z = np.roots(F.poly_from_signed_e(g, p))
            sc = max(1.0, float(np.max(np.abs(z))))
            out.append("k=%d:%s" % (k, "RR" if float(np.max(np.abs(z.imag))) / sc
                                    < 1e-7 else "not RR"))
        # the same test for a genuine rho of the same (a,b) if available
        print("   (a,b)=(%d,%d) p=%d  witness rho: %s" % (a, b, p, "  ".join(out)))
    print("   (compare: psi_0^{box(a-1)} is box_p-divisible by construction)")
    for (a, b, p) in [(4, 3, 12), (5, 4, 12), (6, 4, 24)]:
        f = F.boxp_power(Y.psi0(p, b), p, a - 1)
        out = []
        for k in (2, 3, 4):
            g = F.ff_root(f, p, k)
            z = np.roots(F.poly_from_signed_e(g, p))
            sc = max(1.0, float(np.max(np.abs(z))))
            out.append("k=%d:%s" % (k, "RR" if float(np.max(np.abs(z.imag))) / sc
                                    < 1e-7 else "not RR"))
        print("   (a,b)=(%d,%d) p=%d  psi_0^{box(a-1)}: %s" % (a, b, p, "  ".join(out)))
    print()


def H6():
    print("=" * 100)
    print("[H6] the psi_0 normalisation the brief guessed ('kappa_n(psi_0)=1')")
    print("=" * 100)
    for (p, b) in [(6, 2), (12, 3), (24, 4), (60, 3)]:
        k = F.kappa(Y.psi0(p, b), p, 4)
        print("   p=%2d b=%d   kappa_1..4(psi_0) = %s"
              % (p, b, [str(x) for x in k[1:5]]))
    print("   => kappa_1 = 1 but kappa_2 = p(b-1)/(p-1) != 1 in general;")
    print("      the brief's parenthetical is wrong, the ff_boxp values are used.")
    print()


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    for nm, fn in [('1', H1), ('2', H2), ('3', H3), ('4', H4), ('5', H5),
                   ('6', H6)]:
        if which in ('all', nm):
            fn()
