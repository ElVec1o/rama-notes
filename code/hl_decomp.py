r"""hl_decomp.py -- THE DECOMPOSITION FREEDOM in the cavity step.

OBSERVATION (proved in the report).  The cavity induction step

    R_A(e) = x - sum_alpha nu_alpha / R_{A'}(h_alpha)  +  Y^h_e(x)/F_{A'}(x)

needs ONLY that  Phi_e = sum_alpha nu_alpha h_alpha h_alpha^T  with unit h_alpha,
because the step consumes nothing but  sum_alpha nu_alpha = tr Phi_e = D_A(e).
The identity that FIXES the remainder is

    Y^h_e(x) := F_A(x) - x F_{A'}(x) + sum_alpha nu_alpha F_{A^{(e,h_alpha)}}(x),

which for the canonical choice h_alpha = fhat_k, nu = theta_k is the overlap -X_e.
So the induction closes at 2 sqrt(a) as soon as SOME rank-1 decomposition of
Phi_e has Y^h_e >= 0 on x >= 2 sqrt(a).  This script asks whether the
EIGEN-decomposition of Phi_e does better than the canonical f-decomposition --
in particular on COMPRESSED families, where the canonical one is known to fail.
"""
import sys
import numpy as np
import hl_planes as H

np.set_printoptions(precision=5, suppress=True)


def Y_of(Bs, m, e, mode='f', tol=1e-12):
    """Y^h_e = F_A - x F_{A'} + sum_alpha nu_alpha F_{A^(e,h_alpha)}.
    mode 'f'  : canonical decomposition  nu = theta_k, h = fhat_k  (Y = -X_e)
    mode 'eig': eigen-decomposition of Phi_e."""
    e = e / np.linalg.norm(e)
    Q = H.ortho_complement([e], m)
    FA = H.F_dense(Bs, m)
    FAc = H.F_dense(H.compress(Bs, Q), m - 1)
    xFAc = np.concatenate([FAc, [0.0]])
    fs = [H.f_vec(B, e) for B in Bs]
    Phi = sum(np.outer(f, f) for f in fs)
    if mode == 'f':
        pairs = [(float(f @ f), f / np.linalg.norm(f))
                 for f in fs if f @ f > tol]
    else:
        w, V = np.linalg.eigh(Phi)
        pairs = [(float(w[i]), V[:, i]) for i in range(m) if w[i] > tol]
    acc = np.zeros(m + 1)
    for nu, h in pairs:
        h = h - (h @ e) * e
        nh = np.linalg.norm(h)
        if nh < 1e-9:
            continue
        h = h / nh
        Q2 = H.ortho_complement([e, h], m)
        acc[2:] += nu * H.F_dense(H.compress(Bs, Q2), m - 2)
    Y = FA - xFAc + acc
    return Y, FAc, sum(nu for nu, _ in pairs), float(np.trace(Phi))


def worst_over_e(Bs, m, a, mode, ntrial=8, seed=0, opt=True):
    """most negative value of  Y/F_{A'}  over unit e and x >= 2 sqrt(a).
    < 0  =>  the induction step BREAKS with this decomposition."""
    rng = np.random.default_rng(seed)
    xs = 2 * np.sqrt(a) * np.array([1.0, 1.01, 1.05, 1.2, 1.6, 3.0])

    def val(v):
        Y, FAc, s, tr = Y_of(Bs, m, v, mode)
        return min(np.polyval(Y, x) / np.polyval(FAc, x) for x in xs)

    best, bv = np.inf, None
    for tr in range(ntrial):
        v = np.eye(m)[tr % m] if tr < m else rng.standard_normal(m)
        g = val(v)
        if g < best:
            best, bv = g, v
    if opt:
        try:
            from scipy.optimize import minimize
            r = minimize(val, bv, method='Nelder-Mead',
                         options=dict(maxiter=400, xatol=1e-8, fatol=1e-12))
            best = min(best, r.fun)
        except Exception:
            pass
    return best


def compress_rand(Bs, m, levels, seed):
    rng = np.random.default_rng(seed)
    cur, mm = Bs, m
    for _ in range(levels):
        e = rng.standard_normal(mm)
        e /= np.linalg.norm(e)
        cur = H.compress(cur, H.ortho_complement([e / np.linalg.norm(e)], mm))
        mm -= 1
    return cur, mm


if __name__ == '__main__':
    print("=" * 120)
    print("Y^h_e / F_{A'} at its worst over e and over x >= 2 sqrt(a).")
    print("NEGATIVE = the cavity step breaks with that decomposition.")
    print("=" * 120)
    print(f"{'family':26s} {'m':>3s} {'a':>4s} | {'sum nu = tr Phi?':>16s} | "
          f"{'canonical f':>14s} {'eigen of Phi_e':>16s}")
    cases = []
    cases.append(('K_{3,3}', H.graph_blocks(
        [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3))
    cases.append(('weighted K_6 a=3', H.graph_blocks(
        H.Kn_edges(6), 6, [3.0 / 5] * 15), 6, 3))
    for m, a, sd in [(4, 3, 1), (6, 3, 5), (6, 3, 6)]:
        Bs, err = H.random_projection_family(m, a, seed=sd)
        if err < 1e-11:
            cases.append((f'randproj m{m} a{a} s{sd}', Bs, m, a))
    for m, a, sd in [(4, 3, 1), (5, 3, 3), (6, 3, 4)]:
        Bs, res = H.random_plane_family(m, a, seed=sd)
        if Bs is not None:
            cases.append((f'randplane m{m} a{a} s{sd}', Bs, m, a))

    allc = []
    for nm, Bs, m, a in cases:
        allc.append((nm, Bs, m, a))
    # compressed versions (Adj != aI): the regime where the canonical one fails
    src = [('K_{3,3}', H.graph_blocks(
        [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3),
        ('cube', H.graph_blocks(H.cube_edges(), 8), 8, 3),
        ('wK_8 a=3', H.graph_blocks(H.Kn_edges(8), 8, [3.0 / 7] * 28), 8, 3)]
    Bs, err = H.random_projection_family(8, 3, seed=9)
    if err < 1e-11:
        src.append(('randproj m8 a3', Bs, 8, 3))
    Bs, res = H.random_plane_family(6, 3, seed=4)
    if Bs is not None:
        src.append(('randplane m6 a3', Bs, 6, 3))
    for nm, Bs, m, a in src:
        for lvl in (1, 2):
            if 4 <= m - lvl <= 7:
                Bc, mc = compress_rand(Bs, m, lvl, seed=100 + lvl)
                allc.append((f'{nm} c{lvl}', Bc, mc, a))

    for nm, Bs, m, a in allc:
        _, _, s, tr = Y_of(Bs, m, np.eye(m)[0], 'eig')
        vf = worst_over_e(Bs, m, a, 'f', ntrial=6)
        ve = worst_over_e(Bs, m, a, 'eig', ntrial=6)
        print(f"{nm:26s} {m:3d} {a:4.1f} | {abs(s-tr):16.2e} | "
              f"{vf:14.4e} {ve:16.4e}   "
              f"{'both ok' if min(vf,ve)>=-1e-9 else ('EIG FIXES IT' if ve>=-1e-9 else ('f ok, eig breaks' if vf>=-1e-9 else 'BOTH BREAK'))}")
        sys.stdout.flush()
