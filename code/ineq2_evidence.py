"""ineq2_evidence.py -- numerical evidence for the reduced inequality at b=2.

At b = 2 the representation gives (see profile_pgf.py)

    mu(y) = (y-a)^p Psi(1 - a^2/(y-a)^2),   Psi(u) = E u^{n_2},
    n_2 = #{k : both slots of block k are occupied by S},

and MSS real-rootedness forces  n_2 = sum_i Bernoulli(pi_i)  with

    lambda_max = a(1 + sqrt(pi_max)),   lambda_min = a(1 - sqrt(pi_max)).

So the band  [(sqrt(a-1)-1)^2, (sqrt(a-1)+1)^2]  is EXACTLY

    (INEQ-2)   pi_max <= 4(a-1)/a^2 ,   equivalently   pi_max <= 1 - ((a-2)/a)^2.

pi_max is read off from the spectrum: pi_max = ((lambda_max - a)/a)^2, so this
sweep needs only mu, not the DPP enumeration.  Reported: the largest pi_max
found over random projection families and over random biregular graphs, as a
fraction of the bound.
"""
import sys
import time
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from mcp2 import mcp, restore_proj, proj_from_X, rand_X                  # noqa
from tff import random_biregular, graph_to_projections                   # noqa


def pimax_of(P, a):
    r = np.sort(np.roots(mcp(P)).real)
    return ((r.max() - a) / a) ** 2, r


def hill(p, q, a, rng, steps=350, restarts=5, eps0=0.6):
    """maximise lambda_max (equivalently pi_max) over rank-2 projection
    families with sum = a I."""
    b = 2
    best, bestP = -1.0, None
    for _ in range(restarts):
        X = rand_X(q, p, b, rng)
        P, res = restore_proj(proj_from_X(X), q, p, a, b, iters=3000, tol=1e-14)
        if res > 1e-11:
            continue
        cur, _ = pimax_of(P, a)
        eps = eps0
        for t in range(steps):
            w, V = np.linalg.eigh(P)
            U = V[:, :, -b:] + eps * rng.standard_normal((q, p, b))
            Q, _ = np.linalg.qr(U)
            cand, res = restore_proj(Q @ np.swapaxes(Q, 1, 2), q, p, a, b,
                                     iters=1500, tol=1e-13)
            if res > 1e-10:
                eps *= 0.9
                continue
            v, _ = pimax_of(cand, a)
            if v > cur:
                cur, P = v, cand
            else:
                eps *= 0.985
            if eps < 1e-4:
                break
        if cur > best:
            best, bestP = cur, P
    return best, bestP


if __name__ == '__main__':
    rng = np.random.default_rng(2718)
    print(f"{'(p,q,a)':>12} {'bound 4(a-1)/a^2':>17} {'best pi_max PROJ':>17} "
          f"{'ratio':>8} {'best pi_max GRAPH':>18} {'ratio':>8}")
    CASES = [(4, 6, 3), (6, 9, 3), (8, 12, 3),
             (4, 8, 4), (5, 10, 4), (6, 12, 4),
             (4, 10, 5), (4, 12, 6)]
    for (p, q, a) in CASES:
        if p * a != 2 * q:
            print(f"  skip ({p},{q},{a})")
            continue
        bound = 4.0 * (a - 1) / a ** 2
        t0 = time.time()
        bp, _ = hill(p, q, a, rng, steps=120, restarts=3)
        bg = -1.0
        for _ in range(400):
            adj = random_biregular(p, q, a, 2, rng)
            if adj is None:
                continue
            v, _ = pimax_of(graph_to_projections(adj, p, q), a)
            bg = max(bg, v)
        flag = '  <<< VIOLATION' if max(bp, bg) > bound + 1e-9 else ''
        print(f"{str((p,q,a)):>12} {bound:17.9f} {bp:17.9f} {bp/bound:8.4f} "
              f"{bg:18.9f} {bg/bound:8.4f}{flag}   ({time.time()-t0:.0f}s)",
              flush=True)
