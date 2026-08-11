r"""Dissect the (INV) violations: record (c_e, delta_e, S_e) for every
Schur-descent sample, test the deficiency-repaired bound, and exactly
re-verify the worst violator with mpmath.

Per-slot data at slot e of block k (M := K \ blk k, v := K[off-block, e],
c := K_ee, w := v/sqrt(c)):

    delta_e := |w|^2 = sum_{f not in blk k} K_fe^2 / K_ee
    S_e     := N_{M - w w^T} / N_M    (evaluated at y > (s+t)^2)

Candidate bounds tested:
    (H1)  S <= Lambda(y) = y/A+                    [naive; FALSIFIED]
    (H4)  S <= y / (y - a delta_e / R+(y)),  R+ = 1 - (b-1)/A+
          [graph slots have delta = (deg-1)/a; delta=(a-1)/a gives Lambda]
"""
import sys
import time
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from upper_edge import (build_zoo, band_edges, A_plus, Lambda, schur_np,
                        del_slot, del_block)
from upper_inv import N_coeffs_fast, polyvals

import os as _os, tempfile as _tempfile
SCRATCH = _os.environ.get('RAMA_SCRATCH', _tempfile.gettempdir())
_os.makedirs(SCRATCH, exist_ok=True)


def R_plus(y, a, b):
    return 1.0 - (b - 1) / A_plus(y, a, b)


def collect(zoo, rng, ys_off=(0.01, 0.1, 0.5, 1.0), npaths=40):
    samples = []          # rows: (a,b,y, c, delta, S, tau_k, bsize, zid)
    dumps = []
    for zid, z in enumerate(zoo):
        a, b = z['a'], z['b']
        lo, hi = band_edges(a, b)
        ys = hi + np.array(ys_off)
        for path in range(npaths):
            K = z['K'].copy()
            blocks = [list(bk) for bk in z['blocks']]
            depth = 0
            while any(bk for bk in blocks):
                nonempty = [j for j, bk in enumerate(blocks) if bk]
                k = int(rng.choice(nonempty))
                bl_del = del_block(blocks, k)
                Nd = N_coeffs_fast(K, bl_del, a)
                vd = polyvals(Nd, ys)
                tau = float(np.trace(K[np.ix_(blocks[k], blocks[k])]))
                if (vd > 0).all():
                    off = [x for bk in bl_del for x in bk]
                    for e in blocks[k]:
                        ce = K[e, e]
                        if ce < 1e-9:
                            continue
                        delta = float((K[off, e] ** 2).sum() / ce)
                        Ke = schur_np(K, e)
                        vs = polyvals(N_coeffs_fast(Ke, bl_del, a), ys)
                        S = vs / vd
                        for i, yy in enumerate(ys):
                            samples.append((a, b, yy, ce, delta, S[i], tau,
                                            len(blocks[k]), zid))
                        lam = Lambda(ys, a, b)
                        if (S > lam + 1e-7).any():
                            dumps.append(dict(K=K.copy(),
                                              blocks=[list(x) for x in blocks],
                                              k=k, e=e, a=a, b=b, zid=zid,
                                              name=z['name'], S=S.copy(),
                                              ys=ys.copy(), c=ce, delta=delta))
                move = rng.random()
                if move < 0.35:
                    blocks = bl_del
                elif move < 0.55:
                    e = int(rng.choice(blocks[k]))
                    blocks = del_slot(blocks, e)
                else:
                    cand = [e for e in blocks[k] if K[e, e] > 1e-9]
                    if cand:
                        e = int(rng.choice(cand))
                        K = schur_np(K, e)
                        blocks = bl_del
                    else:
                        blocks = bl_del
                depth += 1
    return np.array([s for s in samples]), dumps


def analyse(samples):
    print('=' * 78)
    print('scatter analysis: S vs the candidate bounds, grouped by (a,b,y)')
    keys = sorted(set(map(tuple, samples[:, :3].round(6))))
    for (a, b, y) in keys:
        m = ((np.abs(samples[:, 0] - a) < 1e-6)
             & (np.abs(samples[:, 1] - b) < 1e-6)
             & (np.abs(samples[:, 2] - y) < 1e-6))
        rows = samples[m]
        c, delta, S = rows[:, 3], rows[:, 4], rows[:, 5]
        lam = Lambda(y, a, b)
        rp = R_plus(y, a, b)
        h4 = y - a * delta / rp
        ok4 = h4 > 1e-9
        viol1 = int((S > lam + 1e-7).sum())
        v4 = (S[ok4] > y / h4[ok4] + 1e-7)
        viol4 = int(v4.sum()) + int((~ok4).sum() and
                                    0)  # blown bound counts separately
        blown = int((~ok4).sum())
        print(f"  (a,b)=({int(a)},{int(b)}) y={y:.4f}: n={len(rows):5d}  "
              f"maxS={S.max():.4f} Lambda={lam:.4f}  "
              f"H1 viol={viol1:4d}   H4 viol={viol4:4d} "
              f"(bound blown for {blown} rows)   max delta={delta.max():.4f}")
        if viol1:
            worst = rows[np.argsort(rows[:, 5] - lam)][-3:]
            for r in worst[::-1]:
                dd = r[4]
                bd = y - a * dd / rp
                h4s = y / bd if bd > 0 else np.inf
                print(f"       S={r[5]:.4f} c={r[3]:.4f} delta={dd:.4f} "
                      f"tau={r[6]:.4f}  H4bound={h4s:.4f} "
                      f"{'H4 OK' if r[5] <= h4s + 1e-7 else 'H4 VIOLATED'}")


def exact_recheck(d):
    """mpmath re-verification of the worst violating S at dps=40."""
    import mpmath as mp
    mp.mp.dps = 40
    K, blocks, k, e, a = d['K'], d['blocks'], d['k'], d['e'], d['a']
    bl_del = del_block(blocks, k)
    Kmp = mp.matrix(K.tolist())
    n = K.shape[0]
    ce = Kmp[e, e]
    Ke = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            Ke[i, j] = Kmp[i, j] - Kmp[i, e] * Kmp[e, j] / ce

    def N_mp(M, blks, y):
        from itertools import product as prod
        opts = [[None] + list(bk) for bk in blks]
        tot = mp.mpf(0)
        for choice in prod(*opts):
            T = [x for x in choice if x is not None]
            mm = len(T)
            if mm == 0:
                dd = mp.mpf(1)
            else:
                sub = mp.matrix(mm, mm)
                for i2, x in enumerate(T):
                    for j2, x2 in enumerate(T):
                        sub[i2, j2] = M[x, x2]
                dd = mp.det(sub)
            tot += ((-a) ** mm) * dd * y ** (len(blks) - mm)
        return tot

    y = mp.mpf(float(d['ys'][0]))
    Nd = N_mp(Kmp, bl_del, y)
    Ns = N_mp(Ke, bl_del, y)
    S = Ns / Nd
    lam = Lambda(float(y), d['a'], d['b'])
    print(f"  exact recheck ({d['name']}, slot {e}): S = {mp.nstr(S, 20)}  "
          f"float said {d['S'][0]:.12f}   Lambda = {lam:.12f}   "
          f"violation confirmed: {float(S) > lam}")


if __name__ == '__main__':
    rng = np.random.default_rng(777)
    zoo = build_zoo(np.random.default_rng(20260801), heavy=True)
    zoo = [z for z in zoo if len(z['blocks']) <= 8]
    t0 = time.time()
    samples, dumps = collect(zoo, rng, npaths=40)
    print(f"collected {len(samples)} S-samples, {len(dumps)} H1-violating "
          f"states  [{time.time()-t0:.1f}s]")
    np.savez(SCRATCH + '/dissect_samples.npz', samples=samples)
    analyse(samples)
    if dumps:
        dumps.sort(key=lambda d: -(d['S'] / Lambda(d['ys'], d['a'],
                                                   d['b'])).max())
        d = dumps[0]
        print('=' * 78)
        print(f"worst violator: {d['name']}  c={d['c']:.5f} "
              f"delta={d['delta']:.5f}  S={d['S']}")
        np.savez(SCRATCH + '/worst_violator.npz', K=d['K'],
                 blocks=np.array(d['blocks'], dtype=object), k=d['k'],
                 e=d['e'], a=d['a'], b=d['b'])
        exact_recheck(d)
