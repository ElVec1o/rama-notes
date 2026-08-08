r"""fv_induction.py -- does the fractional-vertex cavity induction close?

CORRECTED incidence operator (fv_recursion.py used e_2(A)A^+, which is only
right for projections):

    Theta_k := e_2(A_k) * R_k,   R_k = orthogonal projection onto range(A_k),
    theta_k(w) := <w, Theta_k w> = ||iota_w omega_k||^2 .

Class  C(a) :  A_1..A_q PSD, rank <= 2, on R^m, with  Adj(A) := sum_k Theta_k <= a I.
Projection families with sum P_k = a I are in C(a) with Adj = a I.
C(a) is closed under compression:  Adj(A') = Adj(A) - Phi_e  restricted to e^perp,
Phi_e = sum_k f_k f_k^T,  f_k = iota_e omega_k,  tr Phi_e = D_A(e) = <e,Adj(A)e>.

Cavity induction (the target):
    x = t + (a-c)/t,  IH(m):  F_A(x) > 0 and  R_A(e) := F_A(x)/F_{A'}(x) >= x - D_A(e)/t
    step:  R_A(e) = x - sum_k theta_k(e)/R_{A'}(fhat_k) - X_e(x)/F_{A'}(x)
           R_{A'}(fhat_k) >= x - D_{A'}(fhat_k)/t = x - (D_A(fhat_k)-rho_k)/t >= t
    ==>    R_A(e) >= x - D_A(e)/t   PROVIDED  X_e(x) <= 0.
Conclusion would be: all roots of F_A in [-2 sqrt(a-c)), 2 sqrt(a-c)], c = inf rho_k.
c = 1 is the graph case (sharp).  c = 0 is free, and already gives 2 sqrt(a),
which beats the Marcus-Spielman-Srivastava/Marchenko-Pastur value 2 sqrt(2a) + 2.

THIS SCRIPT TESTS:  (i) the corrected Theta identities, (ii) sign of X_e(x),
(iii) the induction hypothesis itself, directly.

VERDICT (fv_attack.py, fv_limits.py, fv_ih_attack.py):
  * X_e(x) <= 0 survives adversarial optimisation over e on every PROJECTION
    family tested; C_2 = 1^T(F o G)1 >= 0 there is PROVED (Schur product).
  * X_e(x) > 0 DOES occur once the family is a compression (Adj != a I):
    doubly-compressed K_{3,3} at p=4,a=3 gives X == +2.33e-2 for all x, i.e.
    C_2 < 0, matching the -||P_{e^perp} Adj(A) e||^2 correction exactly.
  * c = 1 is unreachable: weighted K_p (Adj = a I exactly, edge weight
    a/(p-1)) lies in C(a) and its roots exceed 2 sqrt(a-1) from p = 20 on,
    tending to 2 sqrt(a).  So 2 sqrt(a) is the exact ceiling of this route.
"""
import numpy as np
from itertools import combinations
import fv_setup as S
from fv_recursion import (F_poly, as_dense, compress, ortho_complement,
                          f_vectors, e2, omega_vecs)


def Theta(A, tol=1e-11):
    w, V = np.linalg.eigh(A)
    if w[-2] <= tol:
        return np.zeros_like(A)
    R = V[:, -2:] @ V[:, -2:].T
    return (w[-1] * w[-2]) * R


def Adj(As):
    return sum(Theta(A) for A in As)


def rec_data(As, p, a, e):
    """Everything the recursion needs at direction e."""
    q = len(As)
    Q = ortho_complement([e], p)
    Ac = compress(As, Q)
    fs = f_vectors(As, e)
    th = np.array([float(f @ f) for f in fs])
    Phi = sum(np.outer(f, f) for f in fs)
    FA = as_dense(F_poly(As, p), p)
    FAc = as_dense(F_poly(Ac, p - 1), p - 1)
    return Q, Ac, fs, th, Phi, FA, FAc


def X_of(As, p, a, e):
    """Return polynomials FA, x*FAc, sum theta_k F''_k (all length p+1) and the
    rho's."""
    Q, Ac, fs, th, Phi, FA, FAc = rec_data(As, p, a, e)
    xFAc = np.concatenate([FAc, [0.0]])
    acc = np.zeros(p + 1)
    rho = {}
    for k in range(len(As)):
        if th[k] < 1e-12:
            continue
        fh = fs[k] / np.sqrt(th[k])
        rho[k] = float(fh @ Phi @ fh)
        A2 = compress(As, ortho_complement([e, fh], p))
        acc[2:] += th[k] * as_dense(F_poly(A2, p - 2), p - 2)
    X = xFAc - acc - FA
    return FA, xFAc, acc, X, th, rho


def check_theta_identities(As, p, a, e, rng):
    Q, Ac, fs, th, Phi, FA, FAc = rec_data(As, p, a, e)
    out = {}
    out['|f|^2 = theta'] = max(abs(th[k] - e @ Theta(As[k]) @ e)
                               for k in range(len(As)))
    out['e2 drop'] = max(abs(e2(Ac[k]) - (e2(As[k]) - th[k]))
                         for k in range(len(As)))
    w = rng.standard_normal(p)
    w -= (w @ e) * e
    w /= np.linalg.norm(w)
    wc = Q @ w
    out['Theta drop'] = max(abs(wc @ Theta(Ac[k]) @ wc
                                - (w @ Theta(As[k]) @ w - (w @ fs[k]) ** 2))
                            for k in range(len(As)))
    out['Adj drop'] = np.abs(Adj(Ac) - Q @ (Adj(As) - Phi) @ Q.T).max()
    out['Adj<=aI'] = float(np.linalg.eigvalsh(Adj(Ac)).max()) - a
    return out


# ----------------------------------------------------------------- families
def make_cases(rng, big=False):
    cases = []
    for nm, f in [('K_4', S.K4), ('K_{3,3}', S.K33), ('cube', S.cube)]:
        Ps, p, a = f()
        cases.append((nm, [P for P in Ps], p, a))
    for nm, (n, aa, Ss) in [('circ12/3', (12, 3, [1, 11, 2, 10])),
                            ('circ16/4', (16, 4, [1, 15, 2, 14])),
                            ('circ20/5', (20, 5, [1, 19, 2, 18])),
                            ('circ24/3', (24, 3, [1, 23, 2, 22, 5, 19, 4, 20]))]:
        Ps, p, aa, Pi, U = S.family_circulant(n, aa, Ss)
        cases.append((nm, [P for P in Ps], p, aa))
    for seed in range(1, 5):
        Ps, p, aa, _, _, _ = S.family_random(4, 3, seed=seed)
        cases.append((f'r4/3.{seed}', [P for P in Ps], p, aa))
    for seed in range(1, 3):
        Ps, p, aa, _, _, _ = S.family_random(6, 3, seed=10 + seed)
        cases.append((f'r6/3.{seed}', [P for P in Ps], p, aa))
    for seed in range(1, 3):
        Ps, p, aa, _, _, _ = S.family_random(4, 5, seed=20 + seed)
        cases.append((f'r4/5.{seed}', [P for P in Ps], p, aa))
    return cases


if __name__ == '__main__':
    np.set_printoptions(precision=5, suppress=True)
    rng = np.random.default_rng(11)
    cases = make_cases(rng)
    print("== identities (corrected Theta) and the sign of X_e ==")
    print(f"{'family':10s} {'p':>2s} {'a':>2s} | {'|f|=th':>8s} {'e2drop':>8s} "
          f"{'Thdrop':>8s} {'Adjdrop':>8s} {'Adj-aI':>8s} | "
          f"{'maxroot':>8s} {'2sq(a-1)':>8s} | {'minX@x*':>10s} {'maxX@x*':>10s} "
          f"{'rho_min':>8s}")
    for nm, As, p, a in cases:
        idm = {k: 0.0 for k in ['|f|^2 = theta', 'e2 drop', 'Theta drop',
                                'Adj drop', 'Adj<=aI']}
        xs = 2 * np.sqrt(a - 1) * np.array([1.0, 1.05, 1.3, 2.0])
        minX, maxX = np.inf, -np.inf
        rmin = np.inf
        FA0 = as_dense(F_poly(As, p), p)
        rts = np.sort(np.roots(FA0).real)
        for trial in range(12):
            if trial == 0:
                e = np.zeros(p)
                e[0] = 1.0
            else:
                e = rng.standard_normal(p)
                e /= np.linalg.norm(e)
            d = check_theta_identities(As, p, a, e, rng)
            for k in idm:
                idm[k] = max(idm[k], d[k])
            FA, xFAc, acc, X, th, rho = X_of(As, p, a, e)
            vals = [np.polyval(X, x) / max(1.0, abs(np.polyval(FA, x)))
                    for x in xs]
            minX = min(minX, min(vals))
            maxX = max(maxX, max(vals))
            if rho:
                rmin = min(rmin, min(rho.values()))
        print(f"{nm:10s} {p:2d} {a:2d} | {idm['|f|^2 = theta']:8.1e} "
              f"{idm['e2 drop']:8.1e} {idm['Theta drop']:8.1e} "
              f"{idm['Adj drop']:8.1e} {idm['Adj<=aI']:8.1e} | "
              f"{rts.max():8.4f} {2*np.sqrt(a-1):8.4f} | "
              f"{minX:10.3e} {maxX:10.3e} {rmin:8.4f}")
