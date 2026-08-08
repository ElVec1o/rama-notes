"""Adversarial search over FOUR classes:
   RPROJ : real rank-b orthogonal projections, sum = aI
   CPROJ : complex Hermitian rank-b orthogonal projections, sum = aI
   RPSD  : real rank-b PSD (not projections), sum = aI   [full parametrisation]
   CPSD  : complex Hermitian rank-b PSD, sum = aI        [full parametrisation]
against the tree band [(s-t)^2,(s+t)^2].
"""
import sys
import time
import numpy as np
from mcp2 import (mcp, roots, psd_from_X, proj_from_X, restore_proj, resid,
                  rand_X)
from mixed_char_poly import band
from tff import random_biregular, graph_to_projections


def make_family(X, cls, p, q, a, b):
    if cls in ('RPSD', 'CPSD'):
        return psd_from_X(X, a), 0.0
    A = proj_from_X(X)
    A, r = restore_proj(A, q, p, a, b)
    return A, r


def value(A, mode):
    r = roots(A)
    return (r.min() if mode == 'lo' else -r.max()), r


def search(p, q, a, b, cls, mode, rng, n_restart=8, n_step=400, eps0=0.5):
    cx = cls[0] == 'C'
    best, bestA = 1e18, None
    for rs in range(n_restart):
        X = rand_X(q, p, b, rng, cx)
        A, r = make_family(X, cls, p, q, a, b)
        if r > 1e-9:
            continue
        val, _ = value(A, mode)
        eps, stall = eps0, 0
        for step in range(n_step):
            Y = X + eps * rand_X(q, p, b, rng, cx)
            B, r2 = make_family(Y, cls, p, q, a, b)
            if r2 > 1e-9:
                stall += 1
                continue
            v2, _ = value(B, mode)
            if v2 < val - 1e-14:
                X, A, val = Y, B, v2
                stall = 0
            else:
                stall += 1
                if stall > 20:
                    eps *= 0.62
                    stall = 0
                    if eps < 1e-6:
                        break
        if val < best:
            best, bestA = val, A.copy()
    return best, bestA


PARAMS = [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (4, 8, 4, 2),
          (5, 10, 4, 2), (6, 10, 5, 3), (8, 10, 5, 4), (8, 12, 3, 2),
          (9, 12, 4, 3), (4, 10, 5, 2), (6, 12, 4, 2)]

if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(PARAMS)))
    rng = np.random.default_rng(20260731)
    for idx in sel:
        p, q, a, b = PARAMS[idx]
        lo, hi = band(a, b)
        t0 = time.time()
        print("=" * 80)
        print(f"[{idx}] p={p} q={q} (a,b)=({a},{b})  band=[{lo:.8f},{hi:.8f}]", flush=True)
        gmin, gmax, ng = 1e9, -1e9, 0
        for _ in range(400):
            adj = random_biregular(p, q, a, b, rng)
            if adj is None:
                continue
            ng += 1
            r = roots(graph_to_projections(adj, p, q))
            gmin, gmax = min(gmin, r.min()), max(gmax, r.max())
        print(f"   GRAPH ({ng} random): r_min={gmin:.9f} margin {gmin-lo:+.9f} | "
              f"r_max={gmax:.9f} margin {hi-gmax:+.9f}", flush=True)
        for cls in ('RPROJ', 'CPROJ', 'RPSD', 'CPSD'):
            vlo, _ = search(p, q, a, b, cls, 'lo', rng)
            vhi, _ = search(p, q, a, b, cls, 'hi', rng)
            flag = ''
            if vlo < lo - 1e-9 or -vhi > hi + 1e-9:
                flag = '   <<<<<< VIOLATION'
            print(f"   {cls:5s}: r_min={vlo:.9f} margin {vlo-lo:+.9f} | "
                  f"r_max={-vhi:.9f} margin {hi+vhi:+.9f}{flag}", flush=True)
        print(f"   ({time.time()-t0:.0f}s)", flush=True)
