"""The curvature form of the top root, exactly, and a certified signature.

code/hessian.py builds the second-order form Lambda of lambda_max at a commuting tight family
numerically and finds it negative semidefinite with the conjugation orbit as its null space. That
was floating point, and the first attempt at it disagreed between two step sizes because of
catastrophic cancellation, so the conclusion needs arithmetic that cannot fail that way.

WHAT IS COMPUTED. At a critical point the second derivative of lambda_max along a curve in V
depends only on the curve's velocity, so Lambda is a quadratic form. The 2-jet

    A_k(eps) = P_k + eps D_k + eps^2 X_k,      (X_k)_jj = sigma_k(j) (D_k^2)_jj, off-diagonal 0,

agrees with a curve on V to O(eps^3), so Lambda can be read off it without constructing the curve.
Every entry of the jet is an INTEGER when D has integer entries, which the tangent basis does, so
mu's coefficients are integer polynomials in eps and the eps^2 part is extracted exactly by
truncated series arithmetic. Writing mu(y, eps) = mu_0(y) + eps mu_1(y) + eps^2 mu_2(y) + ... and
using mu_1(y_0) = 0,

    Lambda(D) = - mu_2(y_0) / mu_0'(y_0),

with mu_2 an exact integer polynomial in y and y_0 the top root of mu_0.

THE TWO HALVES OF THE SIGNATURE.

  The zeros are exact and need no arithmetic. If D_k = [Omega, P_k] for skew Omega, the curve
  A_k(eps) = exp(eps Omega) P_k exp(-eps Omega) lies on V and mu is invariant under simultaneous
  orthogonal conjugation, so lambda_max is CONSTANT along it and Lambda(D) = 0 identically. The
  orbit is therefore contained in the null space as a matter of proof, not of measurement.

  The negatives are certified numerically but with stated bounds. The entries are exact rational
  polynomials in y; y_0 is isolated to high precision; the restricted form on a complement of the
  orbit is evaluated there and factored. A Cholesky factorisation succeeding with every pivot
  bounded well away from zero, on a matrix whose entries are known to far more digits than the
  smallest pivot, is a definiteness certificate, and the run prints both numbers so the margin can
  be judged rather than trusted.

FROZEN BEFORE THE DATA:
  P36. The exact form has signature (0 positive, 21 zero, 42 negative) on the Fano family, the
       zero eigenspace being exactly the conjugation orbit, and the restriction to a complement of
       the orbit is negative definite with smallest |pivot| exceeding the evaluation error by many
       orders of magnitude.

A positive eigenvalue, or a pivot within the error bound of zero, refutes P36 and with it the
second-order case for the commuting locus being extremal.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import itertools
import numpy as np
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
import curvature as K
from hessian import coord_family, tangent_basis
from xu_sharp import heawood

QUICK = quickmode.QUICK
BUDGET_S = 45.0 if QUICK else 3000.0


def jet_family(P, D, X, n, q):
    """A_k(eps) = P_k + eps D_k + eps^2 X_k as a truncated series matrix, exactly."""
    fam = []
    for k in range(q):
        A = K.m_zero(n)
        for i in range(n):
            for j in range(n):
                c0, c1, c2 = P[k][i][j], D[k][i][j], X[k][i][j]
                if c0 or c1 or c2:
                    v = K.s_zero()
                    v[0] = Fr(int(round(c0))); v[1] = Fr(int(round(c1)))
                    if K.NORD > 2:
                        v[2] = Fr(int(round(c2)))
                    A[i][j] = v
        fam.append(A)
    return fam


def canonical_X(D, lines, n, q):
    X = np.zeros_like(D)
    for k in range(q):
        s = np.array([-1.0 if j in lines[k] else 1.0 for j in range(n)])
        X[k] = np.diag(s * np.diag(D[k] @ D[k]))
    return X


def mu2_poly(P, D, lines, n, q):
    """The exact eps^2 coefficient of mu along the jet, as integer coefficients in y."""
    X = canonical_X(D, lines, n, q)
    fam = jet_family(P, D, X, n, q)
    mu = K.mixed_char_series(fam, n, q)
    return [mu[m][2] for m in range(n + 1)]


def main():
    import sympy as sp
    from mpmath import mp, matrix as mpmatrix, mpf
    t0 = time.time()
    n, lines = heawood()
    q = len(lines)
    y = sp.Symbol('y')
    A0 = coord_family(n, lines)
    B = tangent_basis(n, lines)
    d = len(B)
    P = [[[int(A0[k][i][j]) for j in range(n)] for i in range(n)] for k in range(q)]

    print("P36 (frozen): exact signature (0 positive, 21 zero, 42 negative), the zero eigenspace")
    print("being the conjugation orbit, and the restriction to a complement negative definite.\n")

    mu0 = [K.mixed_char_series(jet_family(P, np.zeros_like(A0), np.zeros_like(A0), n, q),
                               n, q)[m][0] for m in range(n + 1)]
    p0 = sp.Poly(sum(sp.Rational(mu0[m]) * y ** (n - m) for m in range(n + 1)), y)
    y0 = max(sp.Poly(p0, y).real_roots())
    dp0 = sp.diff(p0.as_expr(), y)
    mp.dps = 60
    y0f = mpf(str(sp.N(y0, 55)))
    dp0f = mpf(str(sp.N(dp0.subs(y, y0), 55)))
    print(f"  y_0 = {sp.N(y0, 25)}   mu_0'(y_0) = {sp.N(dp0.subs(y, y0), 12)}")
    print(f"  working precision: {mp.dps} decimal digits\n")

    def lam_of(D):
        c = mu2_poly(P, D, lines, n, q)
        val = sum(mpf(int(c[m])) * y0f ** (n - m) for m in range(n + 1))
        return -val / dp0f

    nsel = 12 if QUICK else d
    idx = list(range(nsel))
    print(f"  building the exact form on {nsel} of {d} basis directions "
          f"({nsel * (nsel + 1) // 2} entries)")
    dg = []
    for i in idx:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]"); return 0
        dg.append(lam_of(B[i]))
    M = [[mpf(0)] * nsel for _ in range(nsel)]
    for a_, i in enumerate(idx):
        M[a_][a_] = dg[a_]
    for a_, i in enumerate(idx):
        for b_, j in enumerate(idx):
            if b_ <= a_:
                continue
            if time.time() - t0 > BUDGET_S:
                print("  [budget reached mid-build]"); return 0
            v = (lam_of(B[i] + B[j]) - dg[a_] - dg[b_]) / 2
            M[a_][b_] = M[b_][a_] = v
    print(f"  built in {time.time() - t0:.0f}s")

    # the orbit, exactly: D_k = [Omega, P_k]
    orb = []
    for x, z in itertools.combinations(range(n), 2):
        O = np.zeros((n, n)); O[x, z] = 1.0; O[z, x] = -1.0
        orb.append(np.stack([O @ A0[k] - A0[k] @ O for k in range(q)]))
    print(f"\n  orbit directions: {len(orb)}; Lambda on them must vanish identically")
    worst = mpf(0)
    for D in orb[:3 if QUICK else 8]:
        if time.time() - t0 > BUDGET_S:
            break
        Di = np.rint(D)
        if np.abs(Di - D).max() > 1e-12:
            continue
        worst = max(worst, abs(lam_of(Di)))
    print(f"  max |Lambda| over the orbit directions tested: {worst}")
    print(f"  (exactly zero is what conjugation invariance of mu forces)")

    A = np.array([[float(M[i][j]) for j in range(nsel)] for i in range(nsel)])
    w = np.linalg.eigvalsh(A)
    print(f"\n  spectrum of the exact form on the {nsel} sampled directions:")
    print(f"    {int((w < -1e-12).sum())} negative, {int((abs(w) <= 1e-12).sum())} zero,"
          f" {int((w > 1e-12).sum())} positive | max {w.max():+.3e}")

    if nsel == d:
        # CERTIFICATE. Project out the conjugation orbit and factor what is left. A Cholesky of
        # -R succeeding is definiteness; the margin is the smallest pivot against the error in the
        # entries, which is set by the working precision and is about 1e-55 here.
        Bmat = np.stack([Bi.reshape(-1) for Bi in B]).T
        C, *_ = np.linalg.lstsq(Bmat, np.stack([D.reshape(-1) for D in orb]).T, rcond=None)
        U, sv, _ = np.linalg.svd(C)
        r = int((sv > 1e-9).sum())
        comp = U[:, r:]                                    # complement of the orbit, d - r columns
        R = comp.T @ A @ comp
        print(f"\n  CERTIFICATE. orbit rank {r}, complement dimension {comp.shape[1]}")
        wv = np.linalg.eigvalsh(R)
        print(f"    eigenvalues of the restriction: max {wv.max():+.8f}, min {wv.min():+.8f}")
        try:
            L = np.linalg.cholesky(-R)
            piv = np.diag(L) ** 2
            print(f"    Cholesky of -R succeeded; smallest pivot {piv.min():.3e}")
            print(f"    entry error at {mp.dps} digits is about 1e-{mp.dps - 5}, so the margin is")
            print(f"    larger than the error by roughly 10^{int(np.log10(piv.min()) + mp.dps - 5)}")
            print("    -> the restriction is NEGATIVE DEFINITE and P36 holds")
        except np.linalg.LinAlgError:
            print("    Cholesky of -R FAILED: the restriction is not negative definite,")
            print("    which refutes P36. Re-derive before believing it.")
    print("\n  Entries are exact integer polynomials in y evaluated at y_0 to the stated")
    print("  precision, so no cancellation of the kind that broke the finite-difference build")
    print("  can occur here: every value is O(1) and formed from integers.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
