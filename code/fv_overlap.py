r"""fv_overlap.py -- structure of the overlap polynomial Y = -X_e.

    F_A(x) = x F_{A'}(x) - sum_k theta_k(e) F_{A^{(e,fhat_k)}}(x) + Y_e(x),
    Y_e(x) = sum_{r>=2} (-1)^r C_r x^{p-2r},
    C_r    = sum_{|T|=r} sum_{j != l in T} <f_j ^ G_{T\j}, f_l ^ G_{T\l}>.

Questions tested here:
  (a) is C_r >= 0 for every r (it is for r=2: Schur product theorem)?
  (b) is Y_e real-rooted, and are its roots inside the band?  If Y_e is a
      polynomial of the same type with roots <= 2 sqrt(a-1), then Y_e >= 0 on
      the tail and the induction closes.
  (c) does the orthogonalised decomposition (eigenvectors h_alpha of
      Phi_e = sum_k f_k f_k^T, eigenvalues nu_alpha, sum nu_alpha = D_A(e))
      give a smaller / better-signed remainder than the f_k decomposition?
"""
import numpy as np
import fv_setup as S
from fv_recursion import (F_poly, as_dense, compress, ortho_complement,
                          f_vectors)
from fv_induction import Adj


def decompositions(As, p, a, e):
    q = len(As)
    Q = ortho_complement([e], p)
    Ac = compress(As, Q)
    fs = f_vectors(As, e)
    th = np.array([float(f @ f) for f in fs])
    Phi = sum(np.outer(f, f) for f in fs)
    FA = as_dense(F_poly(As, p), p)
    FAc = as_dense(F_poly(Ac, p - 1), p - 1)
    xFAc = np.concatenate([FAc, [0.0]])

    accf = np.zeros(p + 1)
    for k in range(q):
        if th[k] < 1e-12:
            continue
        fh = fs[k] / np.sqrt(th[k])
        accf[2:] += th[k] * as_dense(F_poly(compress(As, ortho_complement([e, fh], p)),
                                            p - 2), p - 2)
    # orthogonalised version
    w, V = np.linalg.eigh(Phi)
    acch = np.zeros(p + 1)
    for al in range(p):
        if w[al] < 1e-12:
            continue
        h = V[:, al]
        h = h - (h @ e) * e
        nh = np.linalg.norm(h)
        if nh < 1e-9:
            continue
        h /= nh
        acch[2:] += w[al] * as_dense(F_poly(compress(As, ortho_complement([e, h], p)),
                                            p - 2), p - 2)
    Yf = accf + FA - xFAc          # Y = sum theta F'' + F_A - x F_A'
    Yh = acch + FA - xFAc
    return FA, xFAc, Yf, Yh, th


if __name__ == '__main__':
    np.set_printoptions(precision=4, suppress=True)
    cases = []
    for nm, f in [('K_{3,3}', S.K33), ('cube', S.cube)]:
        Ps, p, a = f()
        cases.append((nm, [P for P in Ps], p, a))
    for nm, (n, aa, Ss) in [('circ16/4', (16, 4, [1, 15, 2, 14])),
                            ('circ24/3', (24, 3, [1, 23, 2, 22, 5, 19, 4, 20]))]:
        Ps, p, aa, Pi, U = S.family_circulant(n, aa, Ss)
        cases.append((nm, [P for P in Ps], p, aa))
    for seed in (1, 2):
        Ps, p, aa, _, _, _ = S.family_random(6, 3, seed=30 + seed)
        cases.append((f'r6/3.{seed}', [P for P in Ps], p, aa))
    Ps, p, aa, _, _, _ = S.family_random(8, 3, seed=41)
    cases.append(('r8/3', [P for P in Ps], p, aa))

    rng = np.random.default_rng(5)
    print(f"{'family':10s} {'p':>2s} {'a':>2s} | {'C_r signs (r=2..)':28s} | "
          f"{'Y realroot':>10s} {'maxrootY':>9s} {'2sq(a-1)':>9s} | "
          f"{'|Yf|':>9s} {'|Yh|':>9s}")
    for nm, As, p, a in cases:
        for trial in range(3):
            e = rng.standard_normal(p)
            e /= np.linalg.norm(e)
            FA, xFAc, Yf, Yh, th = decompositions(As, p, a, e)
            # C_r = (-1)^r * coeff of x^{p-2r} in Y  -> Y[2r] index in dense array
            Cs = []
            for r in range(2, p // 2 + 1):
                Cs.append(((-1) ** r) * Yf[2 * r])
            Cs = np.array(Cs)
            nz = np.abs(Yf) > 1e-11
            if nz.any():
                Ypoly = Yf[np.argmax(nz):]
                rts = np.roots(Ypoly) if len(Ypoly) > 1 else np.array([0.0])
                realroot = np.max(np.abs(rts.imag)) < 1e-7 * max(1, np.max(np.abs(rts)))
                mr = np.max(rts.real)
            else:
                realroot, mr = True, -np.inf
            sgn = ' '.join(f"{c:+.2e}" for c in Cs[:3])
            print(f"{nm:10s} {p:2d} {a:2d} | {sgn:28s} | {str(realroot):>10s} "
                  f"{mr:9.4f} {2*np.sqrt(a-1):9.4f} | "
                  f"{np.abs(Yf).max():9.2e} {np.abs(Yh).max():9.2e}")
