"""p = 4:  for rank-b projections with sum = aI, the coefficients E_0..E_3 of
mu(y) = y^4 - E_1 y^3 + E_2 y^2 - E_3 y + E_4  are universal (functions of
p,q,a,b only), so the ENTIRE question is the range of the single number E_4.
Smaller E_4  <=>  smaller least root AND larger greatest root.

This script (i) enumerates ALL (a,b)-biregular bipartite graphs on p=4 vertices
(as multisets of b-subsets of [4]) and gets the exact graph range of E_4, and
(ii) minimises / maximises E_4 over the projection manifold numerically."""
import sys
import numpy as np
from itertools import combinations, combinations_with_replacement
from mcp2 import mcp, roots, proj_from_X, restore_proj, rand_X
from mixed_char_poly import band, mixed_char_poly_exact

PARAMS = [(4, 6, 3, 2), (4, 8, 4, 2), (4, 10, 5, 2), (4, 12, 6, 2)]


def all_graphs(p, q, a, b):
    """all multisets of q b-subsets of [p] with every point covered a times"""
    subs = list(combinations(range(p), b))
    out = []
    for ms in combinations_with_replacement(range(len(subs)), q):
        deg = [0] * p
        for s in ms:
            for i in subs[s]:
                deg[i] += 1
        if all(d == a for d in deg):
            A = np.zeros((q, p, p))
            for k, s in enumerate(ms):
                for i in subs[s]:
                    A[k, i, i] = 1.0
            out.append((ms, A))
    return out, subs


def opt_E4(p, q, a, b, rng, sign=+1, n_restart=25, n_step=600, eps0=0.6):
    """minimise sign*E_4 over rank-b projections with sum=aI"""
    best, bestA = 1e18, None
    for rs in range(n_restart):
        X = rand_X(q, p, b, rng)
        A, r = restore_proj(proj_from_X(X), q, p, a, b)
        if r > 1e-9:
            continue
        val = sign * mcp(A)[p]
        eps, stall = eps0, 0
        for step in range(n_step):
            Y = X + eps * rand_X(q, p, b, rng)
            B, r2 = restore_proj(proj_from_X(Y), q, p, a, b)
            if r2 > 1e-9:
                stall += 1
                continue
            v2 = sign * mcp(B)[p]
            if v2 < val - 1e-13:
                X, A, val = Y, B, v2
                stall = 0
            else:
                stall += 1
                if stall > 20:
                    eps *= 0.6
                    stall = 0
                    if eps < 1e-7:
                        break
        if val < best:
            best, bestA = val, A.copy()
    return sign * best, bestA


if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or [0, 1, 2]
    rng = np.random.default_rng(4242)
    for idx in sel:
        p, q, a, b = PARAMS[idx]
        lo, hi = band(a, b)
        gl, subs = all_graphs(p, q, a, b)
        E4s = np.array([mcp(A)[p] for _, A in gl])
        Cs = np.array([mcp(A) for _, A in gl])
        print("=" * 78)
        print(f"p={p} q={q} (a,b)=({a},{b})  band=[{lo:.8f},{hi:.8f}]")
        print(f"   universal coefficients (E_0..E_3) = {Cs[0][:4]}  "
              f"(spread over graphs: {np.ptp(Cs[:,:4],axis=0)})")
        print(f"   {len(gl)} biregular bipartite graphs; E_4 in "
              f"[{E4s.min():.6f}, {E4s.max():.6f}]")
        imin = int(np.argmin(E4s))
        print(f"       argmin graph = {[subs[s] for s in gl[imin][0]]}")
        rmin_g = min(np.roots(c).real.min() for c in Cs)
        rmax_g = max(np.roots(c).real.max() for c in Cs)
        print(f"       graph roots: r_min={rmin_g:.9f} (margin {rmin_g-lo:+.9f}), "
              f"r_max={rmax_g:.9f} (margin {hi-rmax_g:+.9f})")
        e4min, Amin = opt_E4(p, q, a, b, rng, +1)
        e4max, Amax = opt_E4(p, q, a, b, rng, -1)
        print(f"   projection manifold: E_4 in [{e4min:.9f}, {e4max:.9f}]")
        r = roots(Amin)
        print(f"       at E_4 min: roots={np.array2string(r,precision=9)}  "
              f"margins {r.min()-lo:+.9f} / {hi-r.max():+.9f}")
        print(f"       graph min E_4 - projection min E_4 = {E4s.min()-e4min:+.3e}")
        sys.stdout.flush()
