r"""hl_gap.py -- THE EXACT REMAINING GAP.

The cavity step, written with no waste.  Let  Delta := a I - Adj(A) >= 0,
Phi_e = sum_k f_k f_k^T,  theta_k = ||f_k||^2,  fhat_k = f_k/||f_k||,
rho_k := <fhat_k, Phi_e fhat_k>,  delta_k := <fhat_k, Delta fhat_k>.
With  x = t + a/t,  t >= sqrt(a), the induction hypothesis at the child level gives

    R_{A'}(fhat_k) = F_{A'}/F_{A''_k}  >=  x - <fhat_k,Adj(A')fhat_k>/t
                                       =  t + (delta_k + rho_k)/t ,

so the step  R_A(e) >= x - <e,Adj(A)e>/t  closes  IF AND ONLY IF the RESERVE
INEQUALITY holds:

  (L*)   X_e(x) / F_{A^(e)}(x)   <=   sum_k theta_k (delta_k+rho_k)
                                       / ( t (t^2 + delta_k + rho_k) ) .

The naive sufficient condition  X_e <= 0  is FALSE on compressed families
(verified: K_{3,3} and the cube after enough compressions).  (L*) is what is
actually needed, and it is what this script tests.  Note rho_k >= theta_k > 0
always, so the right-hand side is strictly positive: there is always some slack,
and in the commuting (graph) case rho_k == 1, which is exactly where the sharp
constant 2 sqrt(a-1) comes from.
"""
import sys
import numpy as np
import hl_planes as H


def reserve_gap(Bs, m, a, v, ts=(1.0, 1.02, 1.1, 1.5, 3.0)):
    """max over t of  X_e/F_{A'} - reserve.   > 0  =>  (L*) FAILS."""
    e = v / np.linalg.norm(v)
    R = H.recursion(Bs, m, e)
    X, FAc, th, rho = R['X'], R['FAc'], R['th'], R['rho']
    Delta = a * np.eye(m) - H.Adj(Bs)
    fs = R['fs']
    out = -np.inf
    for mul in ts:
        t = np.sqrt(a) * mul
        x = t + a / t
        den = np.polyval(FAc, x)
        if abs(den) < 1e-14:
            continue
        lhs = np.polyval(X, x) / den
        res = 0.0
        for k in range(len(Bs)):
            if th[k] < 1e-12:
                continue
            fh = fs[k] / np.sqrt(th[k])
            dk = float(fh @ Delta @ fh)
            rk = float(rho[k])
            res += th[k] * (dk + rk) / (t * (t * t + dk + rk))
        out = max(out, lhs - res)
    return out


def worst(Bs, m, a, ntrial=8, seed=0):
    rng = np.random.default_rng(seed)
    best, bv = -np.inf, None
    for tr in range(ntrial):
        v = np.eye(m)[tr % m] if tr < m else rng.standard_normal(m)
        g = reserve_gap(Bs, m, a, v)
        if g > best:
            best, bv = g, v
    try:
        from scipy.optimize import minimize
        r = minimize(lambda u: -reserve_gap(Bs, m, a, u), bv,
                     method='Nelder-Mead',
                     options=dict(maxiter=500, xatol=1e-8, fatol=1e-12))
        best = max(best, -r.fun)
    except Exception:
        pass
    return best


def compress_rand(Bs, m, levels, seed):
    rng = np.random.default_rng(seed)
    cur, mm = Bs, m
    for _ in range(levels):
        e = rng.standard_normal(mm)
        e /= np.linalg.norm(e)
        cur = H.compress(cur, H.ortho_complement([e], mm))
        mm -= 1
    return cur, mm


if __name__ == '__main__':
    print("=" * 118)
    print("(L*) RESERVE INEQUALITY:  X_e/F_{A'}  <=  sum_k theta_k(delta_k+rho_k)"
          "/(t(t^2+delta_k+rho_k))")
    print("     positive number below  =>  (L*) FAILS and the cavity induction is broken")
    print("=" * 118)
    src = [('K_{3,3}', H.graph_blocks(
        [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3),
        ('cube', H.graph_blocks(H.cube_edges(), 8), 8, 3),
        ('wK_8 a=3', H.graph_blocks(H.Kn_edges(8), 8, [3.0 / 7] * 28), 8, 3),
        ('wK_7 a=3', H.graph_blocks(H.Kn_edges(7), 7, [3.0 / 6] * 21), 7, 3)]
    Bs, err = H.random_projection_family(6, 3, seed=5)
    if err < 1e-11:
        src.append(('randproj m6 a3', Bs, 6, 3))
    Bs, err = H.random_projection_family(8, 3, seed=9)
    if err < 1e-11:
        src.append(('randproj m8 a3', Bs, 8, 3))
    Bs, res = H.random_plane_family(5, 3, seed=3)
    if Bs is not None:
        src.append(('randplane m5 a3', Bs, 5, 3))
    for nm, Bs, m, a in src:
        for lvl in (0, 1, 2, 3):
            mc = m - lvl
            if mc < 4 or mc > 7:
                continue
            Bc, mc = compress_rand(Bs, m, lvl, seed=100 + lvl)
            dev = float(np.abs(H.Adj(Bc) - a * np.eye(mc)).max())
            g = worst(Bc, mc, a, ntrial=5)
            print(f"  {nm+' c'+str(lvl):24s} m={mc:2d} |Adj-aI|={dev:6.3f}  "
                  f"worst (L*) gap = {g:12.4e}   "
                  f"{'(L*) holds' if g <= 1e-9 else '*** (L*) FAILS ***'}")
            sys.stdout.flush()
