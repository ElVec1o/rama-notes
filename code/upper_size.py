r"""Size dependence of the S-amplification: max S over full slot-scans of
Schur-descent paths, for rotated-pair families with m = 3, 4, 5 pairs
(q = 6, 8, 10) and TFF (6,12,4,2) -- does sup S approach y/b as q grows?"""
import sys, time
import numpy as np
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from upper_edge import (band_edges, Lambda, schur_np, del_slot, del_block,
                        rotated_pairs_family, uniform_blocks)
from naimark_form import naimark_pi
from tff import build_tff
from upper_inv import N_coeffs_fast, polyvals

def scan(K0, blocks0, a, b, rng, npaths, name, ys_off=(0.01, 0.5)):
    lo, hi = band_edges(a, b)
    ys = hi + np.array(ys_off)
    maxS = np.full(len(ys), -np.inf)
    arg = [None]*len(ys)
    t0 = time.time()
    for path in range(npaths):
        K = K0.copy()
        blocks = [list(bk) for bk in blocks0]
        while any(bk for bk in blocks):
            nonempty = [j for j, bk in enumerate(blocks) if bk]
            k = int(rng.choice(nonempty))
            bl_del = del_block(blocks, k)
            vd = polyvals(N_coeffs_fast(K, bl_del, a), ys)
            if (vd > 0).all():
                for e in blocks[k]:
                    ce = K[e, e]
                    if ce < 1e-9: continue
                    Ke = schur_np(K, e)
                    vs = polyvals(N_coeffs_fast(Ke, bl_del, a), ys)
                    S = vs/vd
                    for i in range(len(ys)):
                        if S[i] > maxS[i]:
                            maxS[i] = S[i]
                            arg[i] = (len([b_ for b_ in bl_del if b_]), ce,
                                      float((K[[x for bb in bl_del for x in bb], e]**2).sum()/ce))
            move = rng.random()
            if move < 0.35: blocks = bl_del
            elif move < 0.55:
                e = int(rng.choice(blocks[k])); blocks = del_slot(blocks, e)
            else:
                cand = [e for e in blocks[k] if K[e, e] > 1e-9]
                if cand:
                    e = int(rng.choice(cand)); K = schur_np(K, e); blocks = bl_del
                else: blocks = bl_del
    for i, yo in enumerate(ys_off):
        y = hi + yo
        print(f"  {name}: y=edge+{yo}: max S = {maxS[i]:.4f}  Lambda = "
              f"{Lambda(y, a, b):.4f}  y/b = {y/2:.4f}  margin(y/b) = "
              f"{y/2 - maxS[i]:+.4f}   at (q', c, delta) = {arg[i]}")
    sys.stdout.flush()

if __name__ == '__main__':
    rng = np.random.default_rng(505050)
    t0 = time.time()
    for m, npaths in ((3, 60), (4, 40), (5, 12)):
        A = rotated_pairs_family(m, rng)
        K = naimark_pi(A, m, 2)
        scan(K, uniform_blocks(2*m, 2), m, 2, rng, npaths,
             f"rotated pairs m={m} (q={2*m}, a={m})")
    A, res = build_tff(6, 12, 4, 2, rng)
    if res < 1e-10:
        K = naimark_pi(A, 4, 2)
        scan(K, uniform_blocks(12, 2), 4, 2, rng, 6, "TFF (6,12,4,2) q=12")
    print(f"[{time.time()-t0:.0f}s]")
