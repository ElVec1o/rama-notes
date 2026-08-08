r"""fv_limits.py -- how far can the fractional-vertex induction possibly go?

(1) The neighbourhood is canonically the single PSD operator
        Phi_e = sum_k f_k f_k^T,   f_k = iota_e omega_k,   tr Phi_e = D_A(e),
    because  M_{r-1}(A^{(e,w)}) = sum_{T'} (||G_{T'}||^2 - ||iota_w G_{T'}||^2)
    is a QUADRATIC form in w.  Hence
        sum_k theta_k F_{A^{(e,fhat_k)}}  ==  sum_alpha nu_alpha F_{A^{(e,h_alpha)}}
    for the eigenpairs (nu_alpha,h_alpha) of Phi_e.  Verified here.

(2) The sharp constant needs  rho_k = <fhat_k, Phi_e fhat_k> >= 1; the weighted
    form of that is  ||Phi_e||_F^2 >= tr Phi_e = a.   Tested here.

(3) The class C(a) = {rank<=2 PSD, Adj(A) <= a I} that the induction is closed
    under CONTAINS weighted graphs with q tiny edges per vertex, whose matching
    polynomials converge to Hermite polynomials with roots -> +- 2 sqrt(a).
    So NO argument using only "Adj <= a I" can beat 2 sqrt(a).  Demonstrated.
"""
import numpy as np
import fv_setup as S
from fv_recursion import (F_poly, as_dense, compress, ortho_complement,
                          f_vectors)
from fv_induction import Adj, Theta


def phi_and_rho(As, p, e):
    fs = f_vectors(As, e)
    th = np.array([float(f @ f) for f in fs])
    Phi = sum(np.outer(f, f) for f in fs)
    rho = []
    for k in range(len(As)):
        if th[k] > 1e-12:
            fh = fs[k] / np.sqrt(th[k])
            rho.append(float(fh @ Phi @ fh))
    return Phi, th, np.array(rho)


def weighted_Kp(p, a):
    """Commuting member of C(a): K_p, every edge A_k = sqrt(lam) diag(1_i+1_j)
    with lam = a/(p-1).  Then e_2(A_k) = lam, R_k = diag(1_i+1_j),
    Adj = lam (p-1) I = a I exactly.  F_A is the Hermite polynomial
        F_A(x) = sum_r (-1)^r m_r lam^r x^{p-2r},  m_r = p!/((p-2r)! r! 2^r),
    whose largest root tends to 2 sqrt(a) from below as p -> infinity."""
    from math import factorial
    lam = a / (p - 1)
    c = np.zeros(p + 1)
    if p <= 40:
        for r in range(p // 2 + 1):
            m_r = factorial(p) // (factorial(p - 2 * r) * factorial(r) * 2 ** r)
            c[2 * r] = ((-1) ** r) * float(m_r) * lam ** r
    # roots via the Jacobi matrix of the (scaled) Hermite family: symmetric
    # tridiagonal, zero diagonal, off-diagonal sqrt(r*lam), r = 1..p-1.
    off = np.sqrt(np.arange(1, p) * lam)
    J = np.diag(off, 1) + np.diag(off, -1)
    return c, lam, np.linalg.eigvalsh(J)


def weighted_Kp_family(p, a):
    lam = a / (p - 1)
    As = []
    for i in range(p):
        for j in range(i + 1, p):
            B = np.zeros((p, p))
            B[i, i] = np.sqrt(lam)
            B[j, j] = np.sqrt(lam)
            As.append(B)
    return As, lam


if __name__ == '__main__':
    np.set_printoptions(precision=4, suppress=True)
    rng = np.random.default_rng(17)

    print("== (1)+(2)  Phi_e is the neighbourhood; is ||Phi_e||_F^2 >= a ? ==")
    print(f"{'family':10s} {'p':>2s} {'a':>2s} | {'sum thF=sum nuF':>15s} | "
          f"{'min ||Phi||_F^2':>15s} {'a':>4s} {'min rho':>8s}")
    cases = []
    for nm, f in [('K_4', S.K4), ('K_{3,3}', S.K33), ('cube', S.cube),
                  ('Petersen', S.petersen)]:
        Ps, p, a = f()
        cases.append((nm, [P for P in Ps], p, a, True))
    for nm, (n, aa, Ss) in [('circ16/4', (16, 4, [1, 15, 2, 14])),
                            ('circ24/3', (24, 3, [1, 23, 2, 22, 5, 19, 4, 20]))]:
        Ps, p, aa, Pi, U = S.family_circulant(n, aa, Ss)
        cases.append((nm, [P for P in Ps], p, aa, False))
    for sd in (1, 2):
        Ps, p, aa, _, _, _ = S.family_random(8, 3, seed=50 + sd)
        cases.append((f'r8/3.{sd}', [P for P in Ps], p, aa, False))
    Ps, p, aa, _, _, _ = S.family_random(10, 3, seed=60)
    cases.append(('r10/3', [P for P in Ps], p, aa, False))

    for nm, As, p, a, iscomm in cases:
        idm, fmin, rmin = 0.0, np.inf, np.inf
        for tr in range(20):
            e = np.eye(p)[0] if tr == 0 else rng.standard_normal(p)
            e = e / np.linalg.norm(e)
            Phi, th, rho = phi_and_rho(As, p, e)
            fmin = min(fmin, float((Phi ** 2).sum()))
            if len(rho):
                rmin = min(rmin, rho.min())
            if tr < 3 and p <= 8:
                fs = f_vectors(As, e)
                accf = np.zeros(p + 1)
                for k in range(len(As)):
                    if th[k] < 1e-12:
                        continue
                    fh = fs[k] / np.sqrt(th[k])
                    accf[2:] += th[k] * as_dense(
                        F_poly(compress(As, ortho_complement([e, fh], p)), p - 2), p - 2)
                w, V = np.linalg.eigh(Phi)
                acch = np.zeros(p + 1)
                for al in range(p):
                    if w[al] < 1e-12:
                        continue
                    h = V[:, al] - (V[:, al] @ e) * e
                    if np.linalg.norm(h) < 1e-9:
                        continue
                    h /= np.linalg.norm(h)
                    acch[2:] += w[al] * as_dense(
                        F_poly(compress(As, ortho_complement([e, h], p)), p - 2), p - 2)
                idm = max(idm, np.abs(accf - acch).max())
        print(f"{nm:10s} {p:2d} {a:2d} | {idm:15.2e} | {fmin:15.4f} {a:4d} "
              f"{rmin:8.4f}")

    print()
    print("== (3) C(a) contains weighted graphs whose roots -> 2 sqrt(a) ==")
    print(f"{'p':>4s} {'a':>2s} {'lam':>8s} | {'Adj-aI':>9s} {'Fpoly err':>10s} | "
          f"{'maxroot':>8s} {'2sq(a-1)':>9s} {'2sq(a)':>8s}")
    for a in (3, 5):
        for p in (6, 8, 20, 60, 200, 2000):
            c, lam, jrts = weighted_Kp(p, a)
            adjerr, fperr = np.nan, np.nan
            if p <= 8:
                As, _ = weighted_Kp_family(p, a)
                adjerr = np.abs(Adj(As) - a * np.eye(p)).max()
                fperr = np.abs(as_dense(F_poly(As, p), p) - c).max()
                # cross-check the Jacobi-matrix roots against the polynomial
                fperr = max(fperr, abs(np.sort(np.roots(c).real)[-1] - jrts.max()))
            print(f"{p:4d} {a:2d} {lam:8.4f} | {adjerr:9.1e} {fperr:10.1e} | "
                  f"{jrts.max():8.4f} {2*np.sqrt(a-1):9.4f} {2*np.sqrt(a):8.4f}")
