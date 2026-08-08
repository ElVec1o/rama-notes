r"""Attack (WEAK-S): S = N_{M - vv^T/c}/N_M < y/b for legal bordered kernels.

Stronger search than upper_adv.senv: more steps, larger q', and graph-kernel
starts (near-extremal M) in addition to random class-K starts.
"""
import sys, time
import numpy as np
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from upper_edge import (band_edges, Lambda, feasible_Kclass, kclass_residual,
                        uniform_blocks, frac_to_np)
from upper_inv import N_coeffs_fast, polyvals
from upper_adv import feasible_border
from frac_naimark import graph_kernel
from tff import random_biregular

def S_of(c, v, M, blocks, a, ys):
    Md = M - np.outer(v, v) / c
    NM = polyvals(N_coeffs_fast(M, blocks, a), ys)
    ND = polyvals(N_coeffs_fast(Md, blocks, a), ys)
    return ND / NM, NM

def attack(a, b, qprime, y_off, rng, nstart=10, nstep=700, graph_starts=True):
    lo, hi = band_edges(a, b)
    y = hi + y_off
    ys = np.array([y])
    blocks = uniform_blocks(qprime, b)
    n = qprime * b
    starts = []
    for _ in range(nstart):
        G = rng.standard_normal((n, n))
        M = feasible_Kclass(0.35*(G+G.T)+0.25*np.eye(n), blocks, a)
        if kclass_residual(M, blocks, a) < 1e-8:
            starts.append(M)
    if graph_starts:
        # graph kernel needs p*a = qprime*b
        if (qprime * b) % a == 0:
            p = qprime * b // a
            for _ in range(4):
                adj = random_biregular(p, qprime, a, b, rng)
                if adj is None:
                    continue
                KF, _ = graph_kernel(adj, p, qprime, a, b)
                starts.append(frac_to_np(KF))
    best = (-np.inf, None)
    for M0 in starts:
        M = M0.copy()
        c = float(rng.uniform(0.02, 1.0/a))
        v = 0.3 * rng.standard_normal(n)
        r = feasible_border(c, v, M); v = 0.98*r*v
        S0, NM0 = S_of(c, v, M, blocks, a, ys)
        if not np.isfinite(S0[0]) or NM0[0] <= 0:
            continue
        obj = S0[0]; eps = 0.25
        for step in range(nstep):
            which = rng.random(); M2, v2, c2 = M, v, c
            if which < 0.4:
                H = rng.standard_normal((n, n))
                M2 = feasible_Kclass(M + eps*(H+H.T), blocks, a, iters=110)
                if kclass_residual(M2, blocks, a) > 1e-8:
                    eps *= 0.985; continue
            elif which < 0.88:
                v2 = v + eps * rng.standard_normal(n)
            else:
                c2 = float(np.clip(c*np.exp(0.35*rng.standard_normal()),
                                   5e-4, 1.0/a))
            r = feasible_border(c2, v2, M2); v2 = 0.98*r*v2
            S2, NM2 = S_of(c2, v2, M2, blocks, a, ys)
            if not np.isfinite(S2[0]) or NM2[0] <= 0:
                eps *= 0.985; continue
            if S2[0] > obj:
                M, v, c, obj = M2, v2, c2, S2[0]
            else:
                eps *= 0.992
        if obj > best[0]:
            best = (obj, (M.copy(), v.copy(), c))
    lam = Lambda(y, a, b)
    Smax = best[0]
    print(f"  (a,b)=({a},{b}) q'={qprime} y=edge+{y_off}: max S = {Smax:.4f}"
          f"   Lambda={lam:.4f}   y/b={y/b:.4f}   "
          f"margin to y/b = {y/b - Smax:+.4f}"
          f"{'  *** WEAK-S VIOLATED ***' if Smax > y/b else ''}")
    sys.stdout.flush()
    if best[1] is not None:
        M, v, c = best[1]
        np.savez(f'/private/tmp/claude-501/-Users-vico-Documents-elvec1o-RAMA-'
                 f'NOTEBOOK/0d522a0e-ade5-4120-8948-e5567f4829cb/scratchpad/'
                 f'weakS_a{a}b{b}q{qprime}_off{y_off}.npz', M=M, v=v, c=c, y=y)
    return Smax

if __name__ == '__main__':
    rng = np.random.default_rng(60606)
    t0 = time.time()
    for qp in (2, 3, 4, 6):
        for yoff in (0.01, 0.5):
            attack(3, 2, qp, yoff, rng)
    attack(3, 2, 8, 0.01, rng, nstart=6, nstep=500)
    attack(4, 2, 4, 0.01, rng)
    attack(4, 2, 6, 0.01, rng, nstart=8, nstep=600)
    print(f"[{time.time()-t0:.0f}s total]")
