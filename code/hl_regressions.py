r"""hl_regressions.py -- the two mandatory regressions, plus the two
unconditional bounds proved in the report.

REGRESSION 1.  The SCALAR family A_k = (b/p) I_p with b = 2 has rank p, not 2.
It must NOT be covered.  Its mixed characteristic polynomial is computed exactly
from  mu(y) = sum_j (-1)^j C(q,j) (b/p)^j (p)_j y^{p-j}  (falling factorial),
and its largest root is compared with a + 2 sqrt(a).

REGRESSION 2.  Weighted K_p (in the class, Adj = a I exactly) must NOT be given
anything below 2 sqrt(a): its largest root tends to 2 sqrt(a) from below.

BOUND A (proved).  max root of F_A  <=  sqrt(tr Adj(A) / 2)  <=  sqrt(am/2):
                   the target band for m <= 8, unconditionally.
BOUND B (proved).  (max root)^4 <= sum_i z_i^2 = M_1^2 - 2 M_2
                                <= tr(Adj^2) - sum_k c_k^2  <= a^2 m - sum_k c_k^2:
                   the target band whenever m <= 16 + (sum_k c_k^2)/a^2, i.e.
                   m <= 32a/(2a-1) for a projection family.
"""
import numpy as np
from math import comb
from fractions import Fraction
import hl_planes as H


def scalar_family_mu(p, b, a):
    """exact coefficients (high->low) of mu for A_k = (b/p) I_p, q = ap/b."""
    q = a * p // b
    assert q * b == a * p
    c = [Fraction(0)] * (p + 1)
    for j in range(0, min(q, p) + 1):
        fall = Fraction(1)
        for i in range(j):
            fall *= (p - i)
        c[j] = Fraction((-1) ** j) * comb(q, j) * Fraction(b, p) ** j * fall
    return np.array([float(v) for v in c])


def bound_A(Bs, m):
    return float(np.sqrt(np.trace(H.Adj(Bs)) / 2.0))


def bound_B(Bs, m):
    cs = np.array([float(np.linalg.det(B.T @ B)) for B in Bs])
    Ad = H.Adj(Bs)
    val = float(np.trace(Ad @ Ad) - (cs ** 2).sum())
    return val ** 0.25


if __name__ == '__main__':
    print("=" * 104)
    print("REGRESSION 1 -- the scalar family A_k = (b/p) I_p, b = 2 (RANK p, not 2)")
    print("It violates even the sharp band for large p, and the class EXCLUDES it:")
    print("Theta_k = e_2(A_k) P_{range A_k} and omega_k in Lambda^2 are defined only for rank <= 2.")
    print("=" * 104)
    print(f"  {'p':>5s} {'a':>3s} {'q':>5s} | {'lam_max(mu)':>12s} {'a+2sqrt(a)':>12s} "
          f"{'a+2sqrt(a-1)':>13s} | verdict")
    for a in (3, 4):
        for p in (4, 8, 16, 32, 64, 128, 256):
            if (a * p) % 2:
                continue
            mu = scalar_family_mu(p, 2, a)
            lam = float(np.roots(mu).real.max())
            tgt = a + 2 * np.sqrt(a)
            shp = a + 2 * np.sqrt(a - 1)
            v = ('inside target band' if lam <= tgt + 1e-9
                 else 'OUTSIDE target band (as it must be: rank p)')
            print(f"  {p:5d} {a:3d} {a*p//2:5d} | {lam:12.5f} {tgt:12.5f} "
                  f"{shp:13.5f} | {v}")

    print()
    print("=" * 104)
    print("REGRESSION 2 -- weighted K_p is IN the class (Adj = aI) and rises to 2 sqrt(a)")
    print("=" * 104)
    from scipy.linalg import eigh_tridiagonal
    for a in (3, 5):
        for p in (6, 20, 60, 200, 2000, 200000, 20000000):
            lam = a / (p - 1)
            off = np.sqrt(np.arange(1, p) * lam)
            mr = float(eigh_tridiagonal(np.zeros(p), off, select='i',
                                        select_range=(p - 1, p - 1),
                                        eigvals_only=True)[-1])
            print(f"  weighted K_{p:<9d} a={a}  maxroot(F)={mr:10.6f}  "
                  f"2sqrt(a-1)={2*np.sqrt(a-1):9.6f}  2sqrt(a)={2*np.sqrt(a):9.6f}  "
                  f"{'OK' if mr < 2*np.sqrt(a) else '*** CEILING BROKEN ***'}")

    print()
    print("=" * 104)
    print("THE TWO UNCONDITIONAL BOUNDS, checked (they must never be below the truth)")
    print("=" * 104)
    print(f"  {'family':24s} {'m':>3s} {'a':>4s} | {'true maxroot':>13s} "
          f"{'BOUND A':>10s} {'BOUND B':>10s} {'2sqrt(a)':>10s}")
    cases = [('K_4', H.graph_blocks(H.Kn_edges(4), 4), 4, 3),
             ('K_{3,3}', H.graph_blocks(
                 [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3),
             ('cube Q_3', H.graph_blocks(H.cube_edges(), 8), 8, 3),
             ('Petersen', H.graph_blocks(H.petersen_edges(), 10), 10, 3),
             ('weighted K_8 a=3', H.graph_blocks(
                 H.Kn_edges(8), 8, [3.0 / 7] * 28), 8, 3),
             ('weighted K_10 a=3', H.graph_blocks(
                 H.Kn_edges(10), 10, [3.0 / 9] * 45), 10, 3)]
    for m, a, sd in [(6, 3, 5), (8, 3, 9)]:
        Bs, err = H.random_projection_family(m, a, seed=sd)
        if err < 1e-11:
            cases.append((f'randproj m{m} a{a}', Bs, m, a))
    for m, a, sd in [(5, 3, 3), (6, 3, 4)]:
        Bs, res = H.random_plane_family(m, a, seed=sd)
        if Bs is not None:
            cases.append((f'randplane m{m} a{a}', Bs, m, a))
    for nm, Bs, m, a in cases:
        F = H.F_dense(Bs, m)
        tr = float(np.abs(np.roots(F)).max())
        bA, bB = bound_A(Bs, m), bound_B(Bs, m)
        ok = tr <= min(bA, bB) + 1e-8
        print(f"  {nm:24s} {m:3d} {a:4.1f} | {tr:13.5f} {bA:10.5f} {bB:10.5f} "
              f"{2*np.sqrt(a):10.5f}  {'ok' if ok else '*** BOUND FALSE ***'}")

    print()
    print("  reach of BOUND B for projection families:  m <= 32a/(2a-1)")
    for a in (2, 3, 4, 5, 10, 100):
        print(f"    a={a:4d}   m <= {32*a/(2*a-1):8.3f}")
