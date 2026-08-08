r"""Test the unfolding inequality (UI), the linchpin of the cavity route.

For legal K with slot e (c = K_ee), M = K \ blk(e), w = K[off,e]/sqrt(c),
M' = M - w w^T (the Schur descendant), per-block masses m_k = |w_k|^2:

  (UI)   N_M(y)  >=  N_{M'}(y) - a sum_k m_k N_{M' \ blk k}(y)

for y > (s+t)^2.  On graph kernels (UI) is an identity (the nu-recursion).
Equivalently 1/S >= 1 - sum_k a m_k / B_k(M') when everything is positive.

Tested on: (i) all Schur-descent samples from the zoo, (ii) adversarially
optimised (M, w) configurations.
"""
import sys
import time
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from upper_edge import (build_zoo, band_edges, Lambda, schur_np,
                        del_slot, del_block, feasible_Kclass,
                        kclass_residual, uniform_blocks)
from upper_inv import N_coeffs_fast, polyvals
from upper_adv import feasible_border


def ui_check(M, blocks, w, a, ys):
    """returns (lhs - rhs)/scale at each y, plus S and the ratio form."""
    Mp = M - np.outer(w, w)
    NM = polyvals(N_coeffs_fast(M, blocks, a), ys)
    NMp = polyvals(N_coeffs_fast(Mp, blocks, a), ys)
    rhs = NMp.copy()
    terms = []
    for k, bk in enumerate(blocks):
        mk = float(np.dot(w[bk], w[bk]))
        if mk < 1e-15:
            terms.append(0.0)
            continue
        Nk = polyvals(N_coeffs_fast(Mp, del_block(blocks, k), a), ys)
        rhs -= a * mk * Nk
        terms.append(mk)
    scale = np.maximum(np.abs(NM), np.abs(NMp)) + 1e-300
    return (NM - rhs) / scale, NM, NMp, np.array(terms)


def descent_ui(zoo, rng, ys_off=(0.01, 0.1, 0.5, 1.0), npaths=30):
    print('=' * 78)
    print('(UI) along Schur-descent paths')
    grand_min, nchk, nviol = np.inf, 0, 0
    worst_info = None
    for zid, z in enumerate(zoo):
        a, b = z['a'], z['b']
        lo, hi = band_edges(a, b)
        ys = hi + np.array(ys_off)
        zmin = np.inf
        for path in range(npaths):
            K = z['K'].copy()
            blocks = [list(bk) for bk in z['blocks']]
            while any(bk for bk in blocks):
                nonempty = [j for j, bk in enumerate(blocks) if bk]
                k = int(rng.choice(nonempty))
                bl_del = del_block(blocks, k)
                for e in blocks[k]:
                    ce = K[e, e]
                    if ce < 1e-9:
                        continue
                    off = [x for bk2 in bl_del for x in bk2]
                    wfull = np.zeros(K.shape[0])
                    wfull[off] = K[off, e] / np.sqrt(ce)
                    gap, NM, NMp, m = ui_check(K, bl_del, wfull, a, ys)
                    nchk += len(ys)
                    g = gap.min()
                    if g < zmin:
                        zmin = g
                    if g < grand_min:
                        grand_min = g
                        worst_info = (z['name'], ce, float(m.sum()), g)
                    if (gap < -1e-7).any():
                        nviol += 1
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
        print(f"   {z['name']}: min normalised (UI) slack {zmin:+.2e}")
        sys.stdout.flush()
    print(f"   TOTAL: {nchk} checks, {nviol} violations, min slack "
          f"{grand_min:+.3e}   worst at {worst_info}")


def adversarial_ui(a, b, qprime, rng, y_off, nstart=12, nstep=500):
    """directly minimise the (UI) slack over legal (M, c, v)."""
    lo, hi = band_edges(a, b)
    ys = np.array([hi + y_off])
    blocks = uniform_blocks(qprime, b)
    n = qprime * b
    best = np.inf
    binfo = None
    for st in range(nstart):
        G = rng.standard_normal((n, n))
        M = feasible_Kclass(0.35 * (G + G.T) + 0.25 * np.eye(n), blocks, a)
        if kclass_residual(M, blocks, a) > 1e-8:
            continue
        c = float(rng.uniform(0.02, 1.0 / a))
        v = 0.3 * rng.standard_normal(n)
        r = feasible_border(c, v, M)
        v = 0.98 * r * v
        w = v / np.sqrt(c)
        gap, _, _, _ = ui_check(M, blocks, w, a, ys)
        obj = gap[0]
        eps = 0.25
        for step in range(nstep):
            which = rng.random()
            M2, v2, c2 = M, v, c
            if which < 0.4:
                H = rng.standard_normal((n, n))
                M2 = feasible_Kclass(M + eps * (H + H.T), blocks, a,
                                     iters=120)
                if kclass_residual(M2, blocks, a) > 1e-8:
                    eps *= 0.985
                    continue
            elif which < 0.85:
                v2 = v + eps * rng.standard_normal(n)
            else:
                c2 = float(np.clip(c * np.exp(0.3 * rng.standard_normal()),
                                   1e-3, 1.0 / a))
            r = feasible_border(c2, v2, M2)
            v2 = 0.98 * r * v2
            w2 = v2 / np.sqrt(c2)
            gap2, NM2, _, _ = ui_check(M2, blocks, w2, a, ys)
            if not np.isfinite(gap2[0]):
                eps *= 0.985
                continue
            if gap2[0] < obj:
                M, v, c, obj = M2, v2, c2, gap2[0]
            else:
                eps *= 0.99
        if obj < best:
            best = obj
            binfo = (c, float(np.dot(v, v) / c))
    print(f"   adversarial (a,b)=({a},{b}) q'={qprime} y=edge+{y_off}: "
          f"min (UI) slack {best:+.4e}   (c, delta) = "
          f"({binfo[0]:.4f}, {binfo[1]:.4f})"
          f"{'   *** (UI) VIOLATED ***' if best < -1e-7 else ''}")
    return best


if __name__ == '__main__':
    rng = np.random.default_rng(31337)
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if mode in ('all', 'descent'):
        zoo = build_zoo(np.random.default_rng(20260801), heavy=False)
        zoo = [z for z in zoo if len(z['blocks']) <= 8]
        t0 = time.time()
        descent_ui(zoo, rng, npaths=20)
        print(f"[{time.time()-t0:.0f}s]")
    if mode in ('all', 'adv'):
        print('=' * 78)
        print('(UI) adversarial minimisation')
        t0 = time.time()
        for y_off in (0.01, 0.5):
            adversarial_ui(3, 2, 3, rng, y_off)
            adversarial_ui(3, 2, 4, rng, y_off)
            adversarial_ui(4, 2, 3, rng, y_off)
        print(f"[{time.time()-t0:.0f}s]")
