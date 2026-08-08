r"""fv_attack.py -- ERROR HUNT on the one missing step.

The fractional-vertex induction closes iff, for every family A in the class and
every unit e,   X_e(x) <= 0  for x >= 2 sqrt(a-1).

DERIVED closed form for the leading coefficient (X_e(x) = -C_2 x^{p-4} + O(x^{p-6})):

    <u ^ alpha, v ^ beta> = <u,v><alpha,beta> - <iota_v alpha, iota_u beta>
    iota_{f_l} omega_l = -Theta_l e,      iota_{f_l} g_l = -n_l,  n_l := Theta_l e - theta_l e
    ==>   C_2 = 1^T (F o G) 1  -  || P_{e^perp} Adj(A) e ||^2
          F_{jl} = <f_j,f_l>,  G_{jl} = <g_j,g_l>   (both Gram, so F o G is PSD
          by Schur's product theorem, whence 1^T(F o G)1 >= 0).

So C_2 >= 0 for EVERY projection family (Adj = a I kills the correction), and in
the wider class only when e is an eigenvector of Adj(A).  This script
  (1) verifies that closed form,
  (2) hunts for X_e(x) > 0 by adversarial optimisation over e, on projection
      families AND on their compressions (the families the induction actually
      meets),
  (3) tests the induction hypothesis  R_A(e) >= x - D_A(e)/t  directly.
"""
import numpy as np
from itertools import combinations
import fv_setup as S
from fv_recursion import (F_poly, as_dense, compress, ortho_complement,
                          f_vectors, e2)
from fv_induction import Theta, Adj

try:
    from scipy.optimize import minimize
    HAVE_SCIPY = True
except Exception:
    HAVE_SCIPY = False


def bivec(A, tol=1e-11):
    """omega_A as an antisymmetric matrix b1 b2^T - b2 b1^T."""
    w, V = np.linalg.eigh(A)
    if w[-2] <= tol:
        return np.zeros_like(A)
    b1 = np.sqrt(w[-1]) * V[:, -1]
    b2 = np.sqrt(w[-2]) * V[:, -2]
    return np.outer(b1, b2) - np.outer(b2, b1)


def ip2(w1, w2):
    """<omega,eta> on Lambda^2 for antisymmetric matrix reps = tr(w1^T w2)/2."""
    return float((w1 * w2).sum() / 2.0)


def C2_closed(As, e):
    oms = [bivec(A) for A in As]
    fs = [om @ e for om in oms]                 # iota_e omega  (sign fixed below)
    fs = [-(f) for f in fs]                     # iota_e(b1^b2) = <e,b1>b2-<e,b2>b1
    gs = [oms[k] - (np.outer(e, fs[k]) - np.outer(fs[k], e)) for k in range(len(As))]
    F = np.array([[float(fi @ fj) for fj in fs] for fi in fs])
    G = np.array([[ip2(gi, gj) for gj in gs] for gi in gs])
    Ad = Adj(As)
    corr = Ad @ e - float(e @ Ad @ e) * e
    return float((F * G).sum()) - float(corr @ corr), F, G


def X_poly(As, p, e):
    """X_e as a dense coefficient array (high->low, length p+1)."""
    q = len(As)
    Q = ortho_complement([e], p)
    Ac = compress(As, Q)
    fs = f_vectors(As, e)
    th = np.array([float(f @ f) for f in fs])
    FA = as_dense(F_poly(As, p), p)
    FAc = as_dense(F_poly(Ac, p - 1), p - 1)
    xFAc = np.concatenate([FAc, [0.0]])
    acc = np.zeros(p + 1)
    Phi = sum(np.outer(f, f) for f in fs)
    rho = []
    for k in range(q):
        if th[k] < 1e-12:
            continue
        fh = fs[k] / np.sqrt(th[k])
        rho.append(float(fh @ Phi @ fh))
        A2 = compress(As, ortho_complement([e, fh], p))
        acc[2:] += th[k] * as_dense(F_poly(A2, p - 2), p - 2)
    return xFAc - acc - FA, FA, FAc, th, np.array(rho)


def worst_X(As, p, a, ntrial=40, seed=0, refine=True):
    """Maximise X_e(x)/|F_A(x)| over unit e and x in the tail."""
    rng = np.random.default_rng(seed)
    xs = 2 * np.sqrt(max(a - 1.0, 1e-9)) * np.array([1.0, 1.02, 1.1, 1.5, 3.0])

    def score(v):
        e = v / np.linalg.norm(v)
        X, FA, FAc, th, rho = X_poly(As, p, e)
        return max(np.polyval(X, x) / max(1e-12, abs(np.polyval(FA, x)))
                   for x in xs)
    best = -np.inf
    bestv = None
    for t in range(ntrial):
        v = rng.standard_normal(p) if t else np.eye(p)[0]
        s = score(v)
        if s > best:
            best, bestv = s, v
    if refine and HAVE_SCIPY:
        r = minimize(lambda v: -score(v), bestv, method='Nelder-Mead',
                     options=dict(maxiter=800, xatol=1e-8, fatol=1e-12))
        if -r.fun > best:
            best, bestv = -r.fun, r.x
    return best, bestv / np.linalg.norm(bestv)


def IH_violation(As, p, a, c=1.0, ntrial=25, seed=0):
    """max over unit e of  (x - D_A(e)/t) - F_A(x)/F_{A'}(x),  x = t+(a-c)/t,
    t = sqrt(a-c) (the extremal t).  Positive = induction hypothesis FALSE."""
    rng = np.random.default_rng(seed)
    t = np.sqrt(max(a - c, 1e-9))
    worst = -np.inf
    for tr in range(ntrial):
        e = np.eye(p)[0] if tr == 0 else rng.standard_normal(p)
        e = e / np.linalg.norm(e)
        Q = ortho_complement([e], p)
        Ac = compress(As, Q)
        FA = as_dense(F_poly(As, p), p)
        FAc = as_dense(F_poly(Ac, p - 1), p - 1)
        D = float(e @ Adj(As) @ e)
        for mult in (1.0, 1.05, 1.5, 3.0):
            x = mult * (t + (a - c) / t)
            num, den = np.polyval(FA, x), np.polyval(FAc, x)
            if abs(den) < 1e-12:
                continue
            worst = max(worst, (x - D / t) - num / den)
    return worst


def compress_random(As, p, k, seed):
    """k successive compressions along random directions -> a member of C(a)
    that is not a projection family."""
    rng = np.random.default_rng(seed)
    cur, m = [A.copy() for A in As], p
    for _ in range(k):
        e = rng.standard_normal(m)
        e /= np.linalg.norm(e)
        Q = ortho_complement([e], m)
        cur = compress(cur, Q)
        m -= 1
    return cur, m


if __name__ == '__main__':
    np.set_printoptions(precision=5, suppress=True)
    cases = []
    for nm, f in [('K_4', S.K4), ('K_{3,3}', S.K33), ('cube', S.cube)]:
        Ps, p, a = f()
        cases.append((nm, [P for P in Ps], p, a))
    for nm, (n, aa, Ss) in [('circ12/3', (12, 3, [1, 11, 2, 10])),
                            ('circ16/4', (16, 4, [1, 15, 2, 14])),
                            ('circ24/3', (24, 3, [1, 23, 2, 22, 5, 19, 4, 20]))]:
        Ps, p, aa, Pi, U = S.family_circulant(n, aa, Ss)
        cases.append((nm, [P for P in Ps], p, aa))
    for seed in (1, 2, 3):
        Ps, p, aa, _, _, _ = S.family_random(4, 3, seed=seed)
        cases.append((f'r4/3.{seed}', [P for P in Ps], p, aa))
    Ps, p, aa, _, _, _ = S.family_random(6, 3, seed=11)
    cases.append(('r6/3', [P for P in Ps], p, aa))
    Ps, p, aa, _, _, _ = S.family_random(4, 5, seed=21)
    cases.append(('r4/5', [P for P in Ps], p, aa))

    print("scipy:", HAVE_SCIPY)
    print(f"{'family':10s} {'p':>2s} {'a':>2s} {'lvl':>3s} | {'C2 closed':>10s} "
          f"{'C2 sign':>10s} | {'worst X':>11s} | {'IH viol c=1':>11s} "
          f"{'IH viol c=0':>11s}")
    import sys
    for nm, As0, p0, a in cases:
        for lvl in (0, 1, 2):
            if p0 - lvl < 4 or (p0 >= 8 and lvl > 0):
                continue
            As, p = (As0, p0) if lvl == 0 else compress_random(As0, p0, lvl, 5 + lvl)
            # C2 closed form vs the actual x^{p-4} coefficient of X
            rng = np.random.default_rng(3)
            cerr, csign = 0.0, np.inf
            for _ in range(5):
                e = rng.standard_normal(p)
                e /= np.linalg.norm(e)
                X, FA, FAc, th, rho = X_poly(As, p, e)
                c2c, F, G = C2_closed(As, e)
                cerr = max(cerr, abs(-X[4] - c2c) / max(1.0, abs(c2c)))
                csign = min(csign, c2c)
            wX, ev = worst_X(As, p, a, ntrial=30, seed=2)
            ih1 = IH_violation(As, p, a, c=1.0, seed=4)
            ih0 = IH_violation(As, p, a, c=0.0, seed=4)
            print(f"{nm:10s} {p:2d} {a:2d} {lvl:3d} | {cerr:10.2e} "
                  f"{csign:10.3e} | {wX:11.3e} | {ih1:11.3e} {ih0:11.3e}")
