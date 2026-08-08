r"""Adversarial searches for the upper-edge contract.

  root : maximise the top root of N_K over the kernel class K(a,b)
         (blocks <= (1/a) I, sizes <= b).  C-upper says sup = (s+t)^2.
  senv : maximise S = N_{M - vv^T/c}/N_M over legal bordered kernels
         [[c, v^T],[v, M]] in class, tracing the envelope S_max(c, delta),
         delta = |v|^2/c.  Constraint from PSD <= I: delta <= 1 - c.

Both hill-climbs with random restarts; float; any candidate violation gets
re-checked at tighter feasibility before being reported.
"""
import sys
import time
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from upper_edge import (band_edges, A_plus, Lambda, schur_np, del_block,
                        feasible_Kclass, kclass_residual, uniform_blocks,
                        top_root)
from upper_inv import N_coeffs_fast, polyvals


# ------------------------------------------------------------- root search
def maximise_top_root(a, b, q, rng, nstart=10, nstep=250, sizes=None):
    lo, hi = band_edges(a, b)
    blocks = (uniform_blocks(q, b) if sizes is None else None)
    if sizes is not None:
        blocks, off = [], 0
        for s in sizes:
            blocks.append(list(range(off, off + s)))
            off += s
    n = sum(len(bk) for bk in blocks)
    best_root, best_K = -np.inf, None
    for st in range(nstart):
        M = rng.standard_normal((n, n))
        K = feasible_Kclass(0.35 * (M + M.T) + 0.25 * np.eye(n), blocks, a)
        if kclass_residual(K, blocks, a) > 1e-8:
            continue
        r0, _ = top_root(N_coeffs_fast(K, blocks, a))
        eps = 0.3
        for step in range(nstep):
            H = rng.standard_normal((n, n))
            K2 = feasible_Kclass(K + eps * (H + H.T), blocks, a, iters=150)
            if kclass_residual(K2, blocks, a) > 1e-8:
                eps *= 0.98
                continue
            r2, im2 = top_root(N_coeffs_fast(K2, blocks, a))
            if r2 > r0:
                K, r0 = K2, r2
            else:
                eps *= 0.99
        if r0 > best_root:
            best_root, best_K = r0, K
    # tight re-verification
    K = feasible_Kclass(best_K, blocks, a, iters=3000)
    res = kclass_residual(K, blocks, a)
    r, im = top_root(N_coeffs_fast(K, blocks, a))
    print(f"  (a,b)=({a},{b}) q={q} sizes={sizes or 'uniform'}: "
          f"max top root {r:.6f}  edge {hi:.6f}  margin {hi - r:+.6f}  "
          f"feas {res:.1e}  {'*** VIOLATION ***' if r > hi + 1e-7 else ''}")
    return r, K, blocks


# ------------------------------------------------------------- S envelope
def feasible_border(c, v, M, tol=1e-10):
    """largest r <= 1 with [[c, r v^T],[r v, M]] psd and <= I; None if v=0."""
    nv = np.linalg.norm(v)
    if nv < 1e-14:
        return 0.0
    lo_r, hi_r = 0.0, 1.0

    def ok(r):
        n = M.shape[0]
        Kb = np.zeros((n + 1, n + 1))
        Kb[0, 0] = c
        Kb[0, 1:] = r * v
        Kb[1:, 0] = r * v
        Kb[1:, 1:] = M
        w = np.linalg.eigvalsh(Kb)
        return w.min() > -tol and w.max() < 1 + tol

    if ok(1.0):
        return 1.0
    for _ in range(50):
        mid = 0.5 * (lo_r + hi_r)
        if ok(mid):
            lo_r = mid
        else:
            hi_r = mid
    return lo_r


def S_of(c, v, M, blocks, a, ys):
    Md = M - np.outer(v, v) / c
    NM = polyvals(N_coeffs_fast(M, blocks, a), ys)
    ND = polyvals(N_coeffs_fast(Md, blocks, a), ys)
    return ND / NM, NM


def senv_search(a, b, qprime, rng, y_off, nstart=14, nstep=400,
                delta_target=None, c_fix=None):
    """maximise S at y = edge + y_off; returns list of (c, delta, S, info)."""
    lo, hi = band_edges(a, b)
    ys = np.array([hi + y_off])
    blocks = uniform_blocks(qprime, b)
    n = qprime * b
    out = []
    for st in range(nstart):
        G = rng.standard_normal((n, n))
        M = feasible_Kclass(0.35 * (G + G.T) + 0.25 * np.eye(n), blocks, a)
        if kclass_residual(M, blocks, a) > 1e-8:
            continue
        c = c_fix if c_fix is not None else float(rng.uniform(0.02, 1.0 / a))
        v = 0.3 * rng.standard_normal(n)
        r = feasible_border(c, v, M, tol=1e-11)
        v = 0.98 * r * v
        Sb, _ = S_of(c, v, M, blocks, a, ys)
        obj0 = Sb[0]
        if delta_target is not None:
            obj0 -= 30.0 * (np.dot(v, v) / c - delta_target) ** 2
        eps = 0.25
        for step in range(nstep):
            which = rng.random()
            M2, v2, c2 = M, v, c
            if which < 0.45:
                H = rng.standard_normal((n, n))
                M2 = feasible_Kclass(M + eps * (H + H.T), blocks, a,
                                     iters=120)
                if kclass_residual(M2, blocks, a) > 1e-8:
                    eps *= 0.985
                    continue
            elif which < 0.9:
                v2 = v + eps * rng.standard_normal(n)
            elif c_fix is None:
                c2 = float(np.clip(c * np.exp(0.3 * rng.standard_normal()),
                                   1e-3, 1.0 / a))
            r = feasible_border(c2, v2, M2, tol=1e-11)
            v2 = 0.98 * r * v2
            S2, NM2 = S_of(c2, v2, M2, blocks, a, ys)
            if not np.isfinite(S2[0]) or (NM2 <= 0).any():
                eps *= 0.985
                continue
            obj2 = S2[0]
            if delta_target is not None:
                obj2 -= 30.0 * (np.dot(v2, v2) / c2 - delta_target) ** 2
            if obj2 > obj0:
                M, v, c, obj0 = M2, v2, c2, obj2
            else:
                eps *= 0.99
        # final strict re-verification at tol 1e-12, shrink v by 1e-6
        r = feasible_border(c, v, M, tol=1e-12)
        v = (1 - 1e-9) * r * v
        Sb, NM = S_of(c, v, M, blocks, a, ys)
        delta = float(np.dot(v, v) / c)
        # per-block masses
        mvec = [float(np.dot(v[bk], v[bk])) / c for bk in blocks]
        taus = [float(np.trace(M[np.ix_(bk, bk)])) for bk in blocks]
        out.append((c, delta, float(Sb[0]), mvec, taus, M.copy(), v.copy()))
    return out


def report_senv(a, b, qprime, rng, y_off):
    lo, hi = band_edges(a, b)
    y = hi + y_off
    lam = Lambda(y, a, b)
    rp = 1 - (b - 1) / A_plus(y, a, b)
    print(f"--- S-envelope (a,b)=({a},{b}) q'={qprime} y=edge+{y_off} "
          f"(Lambda={lam:.4f})")
    res = senv_search(a, b, qprime, rng, y_off)
    res.sort(key=lambda t: -t[2])
    for (c, delta, S, mvec, taus, M, v) in res[:6]:
        h4 = y / (y - a * delta / rp) if y - a * delta / rp > 0 else np.inf
        print(f"    S={S:.4f}  c={c:.4f} delta={delta:.4f}  "
              f"m={np.round(mvec,3)}  tau={np.round(taus,3)}  "
              f"vs Lambda {'>' if S > lam else '<'}  vs H4 "
              f"{'>' if S > h4 else '<'} ({h4:.4f})")
    return res


if __name__ == '__main__':
    rng = np.random.default_rng(20260802)
    mode = sys.argv[1] if len(sys.argv) > 1 else 'root'
    if mode == 'root':
        print('=' * 78)
        print('ADVERSARIAL top-root maximisation over class K(a,b)')
        t0 = time.time()
        maximise_top_root(3, 2, 6, rng)
        maximise_top_root(3, 2, 8, rng)
        maximise_top_root(4, 2, 8, rng)
        maximise_top_root(3, 2, 6, rng, sizes=[2, 2, 2, 2, 1, 1])
        print(f"[{time.time()-t0:.0f}s]")
    if mode == 'senv':
        print('=' * 78)
        print('ADVERSARIAL S-envelope')
        t0 = time.time()
        for y_off in (0.01, 0.5, 1.0):
            report_senv(3, 2, 3, rng, y_off)
        report_senv(3, 2, 4, rng, 0.5)
        report_senv(4, 2, 3, rng, 0.5)
        print(f"[{time.time()-t0:.0f}s]")
