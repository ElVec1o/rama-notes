"""Scaling study.  The tree band is asymptotically SHARP for graphs (large-girth
biregular graphs push the least root down to (s-t)^2), so the margin shrinks
with p.  If general projection families can beat graphs by any fixed amount,
a violation must show up as p grows.  Here we track, for increasing p:

    best graph   r_min, r_max     (over many random biregular graphs)
    best TFF     r_min, r_max     (random + short local search)

against the tree band [(s-t)^2,(s+t)^2] and the Marchenko-Pastur band
[(sqrt a - sqrt b)^2, (sqrt a + sqrt b)^2].
"""
import sys
import time
import numpy as np
from math import comb
from mixed_char_poly import band, _popcounts
from mcp2 import proj_from_X, restore_proj, rand_X
from tff import random_biregular, graph_to_projections


def mcp_chunked(A, chunk=1 << 14):
    """Same as mcp but bounded memory: enumerate subsets in chunks."""
    A = np.asarray(A, dtype=float)
    q, p, _ = A.shape
    N = 1 << q
    pc = _popcounts(q)
    Sr = np.zeros((q + 1, p + 1))
    base = np.zeros((chunk, p, p))
    for start in range(0, N, chunk):
        end = min(N, start + chunk)
        n = end - start
        S = base[:n]
        S[:] = 0.0
        # build by bit decomposition of (start..end-1)
        idx = np.arange(start, end)
        for k in range(q):
            sel = (idx >> k) & 1
            S[sel == 1] += A[k]
        eig = np.linalg.eigvalsh(S)
        E = np.zeros((n, p + 1))
        E[:, 0] = 1.0
        for j in range(p):
            E[:, 1:] = E[:, 1:] + eig[:, j][:, None] * E[:, :-1]
        w = pc[start:end]
        for m in range(p + 1):
            Sr[:, m] += np.bincount(w, weights=E[:, m], minlength=q + 1)
    mu = np.zeros(p + 1)
    for r in range(q + 1):
        sgn = -1.0 if (r & 1) else 1.0
        for m in range(r, p + 1):
            mu[m] += sgn * comb(q - r, m - r) * Sr[r, m]
    return mu


def rts(A):
    return np.sort(np.roots(mcp_chunked(A)).real)


CASES = [(4, 6, 3, 2), (6, 9, 3, 2), (8, 12, 3, 2), (10, 15, 3, 2),
         (6, 8, 4, 3), (9, 12, 4, 3), (5, 10, 4, 2), (8, 16, 4, 2)]

if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(CASES)))
    rng = np.random.default_rng(20260801)
    for idx in sel:
        p, q, a, b = CASES[idx]
        lo, hi = band(a, b)
        mplo, mphi = (np.sqrt(a) - np.sqrt(b)) ** 2, (np.sqrt(a) + np.sqrt(b)) ** 2
        t0 = time.time()
        ngr = 200 if q <= 12 else 60
        ntf = 60 if q <= 12 else 12
        nst = 120 if q <= 12 else 25
        gmin, gmax = 1e9, -1e9
        for _ in range(ngr):
            adj = random_biregular(p, q, a, b, rng)
            if adj is None:
                continue
            r = rts(graph_to_projections(adj, p, q))
            gmin, gmax = min(gmin, r.min()), max(gmax, r.max())
        pmin, pmax = 1e9, -1e9
        for _ in range(ntf):
            X = rand_X(q, p, b, rng)
            A, res = restore_proj(proj_from_X(X), q, p, a, b)
            if res > 1e-9:
                continue
            r = rts(A)
            cur_lo, cur_hi = r.min(), r.max()
            eps = 0.5
            stall = 0
            for st in range(nst):     # short local search on both objectives
                Y = X + eps * rand_X(q, p, b, rng)
                B, r2 = restore_proj(proj_from_X(Y), q, p, a, b)
                if r2 > 1e-9:
                    continue
                rr = rts(B)
                if rr.min() < cur_lo - 1e-13 or rr.max() > cur_hi + 1e-13:
                    X, cur_lo, cur_hi = Y, min(cur_lo, rr.min()), max(cur_hi, rr.max())
                    stall = 0
                else:
                    stall += 1
                    if stall > 15:
                        eps *= 0.65
                        stall = 0
            pmin, pmax = min(pmin, cur_lo), max(pmax, cur_hi)
        flag = ''
        if pmin < lo - 1e-9 or pmax > hi + 1e-9:
            flag = '   <<<<<< PROJECTION VIOLATION'
        print(f"p={p:3d} q={q:3d} (a,b)=({a},{b})  tree=[{lo:.6f},{hi:.6f}] "
              f"MP=[{mplo:.4f},{mphi:.4f}]")
        print(f"      GRAPH r_min={gmin:.8f} (marg {gmin-lo:+.8f})  "
              f"r_max={gmax:.8f} (marg {hi-gmax:+.8f})")
        print(f"      PROJ  r_min={pmin:.8f} (marg {pmin-lo:+.8f})  "
              f"r_max={pmax:.8f} (marg {hi-pmax:+.8f}){flag}   [{time.time()-t0:.0f}s]")
        sys.stdout.flush()
