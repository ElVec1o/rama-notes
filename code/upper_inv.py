r"""Step 2: test the invariant (INV) along random Schur-descent paths.

(INV), at fixed y > (s+t)^2, for every kernel K reachable from the zoo by
{delete slot, delete block, Schur-condition at a slot then delete its block}
and every nonempty block k with tau_k = tr K[blk k]:

    (B-lo)  B_k := N_K / N_{K \ blk k}  >=  y - a tau_k Lambda(y)
    (B-hi)  B_k                        <=  y - a tau_k
    (S-lo)  S_e := N_{K^{(e)} \ blk k} / N_{K \ blk k}  >=  1
    (S-hi)  S_e                                        <=  Lambda(y)

Lambda(y) = y / A+(y).  (B-lo) and (S-hi) are the load-bearing sides: they
imply N_K > 0 above the band, hence C-upper.  (B-hi)/(S-lo) are the free
sides on graphs (S >= 1 automatic given positivity).

Also monitored: N_K(y) > 0 at every state (C1), and the top root vs edge.
"""
import sys
import time
from itertools import product
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from upper_edge import (build_zoo, band_edges, A_plus, Lambda, schur_np,
                        del_slot, del_block, class_report, top_root)

_SIG_CACHE = {}


def tgroups_sig(sizes):
    """transversal position-tuples for a size signature, grouped by |T|."""
    if sizes not in _SIG_CACHE:
        pos_blocks = []
        off = 0
        for s in sizes:
            pos_blocks.append(list(range(off, off + s)))
            off += s
        opts = [[None] + bk for bk in pos_blocks]
        bym = {}
        for choice in product(*opts):
            T = [x for x in choice if x is not None]
            if T:
                bym.setdefault(len(T), []).append(T)
        _SIG_CACHE[sizes] = {m: np.array(v, dtype=int)
                             for m, v in bym.items()}
    return _SIG_CACHE[sizes]


def N_coeffs_fast(K, blocks, a):
    sizes = tuple(len(bk) for bk in blocks)
    cat = [x for bk in blocks for x in bk]
    q = len(blocks)
    c = np.zeros(q + 1)
    c[0] = 1.0
    if cat:
        Ks = K[np.ix_(cat, cat)]
        for m, idx in tgroups_sig(sizes).items():
            mats = Ks[idx[:, :, None], idx[:, None, :]]
            c[m] = ((-a) ** m) * np.linalg.det(mats).sum()
    return c


def polyvals(c, ys):
    v = np.zeros_like(ys)
    for x in c:
        v = v * ys + x
    return v


class Stats:
    """track worst slack per inequality, with a snapshot of the offender."""

    def __init__(self):
        self.worst = {}
        self.count = 0

    def add(self, key, slack, info):
        self.count += 1
        if key not in self.worst or slack < self.worst[key][0]:
            self.worst[key] = (slack, info)


def run_descents(zoo, rng, ys_off=(0.01, 0.1, 0.5, 1.0), npaths=40,
                 report_each=True):
    grand = {}
    for z in zoo:
        a, b = z['a'], z['b']
        lo, hi = band_edges(a, b)
        ys = hi + np.array(ys_off)
        lam = Lambda(ys, a, b)
        st = Stats()
        nneg = 0
        t0 = time.time()
        for path in range(npaths):
            K = z['K'].copy()
            blocks = [list(bk) for bk in z['blocks']]
            depth = 0
            while any(bk for bk in blocks):
                NK = N_coeffs_fast(K, blocks, a)
                vK = polyvals(NK, ys)
                if (vK <= 0).any():
                    nneg += 1
                nonempty = [j for j, bk in enumerate(blocks) if bk]
                # ---- record ratios at a random nonempty block
                k = int(rng.choice(nonempty))
                tau = float(np.trace(K[np.ix_(blocks[k], blocks[k])]))
                bl_del = del_block(blocks, k)
                Nd = N_coeffs_fast(K, bl_del, a)
                vd = polyvals(Nd, ys)
                if (vd > 0).all() and (vK > 0).all():
                    B = vK / vd
                    sBlo = B - (ys - a * tau * lam)
                    sBhi = (ys - a * tau) - B
                    for i, yy in enumerate(ys):
                        info = (z['name'], depth, path, 'B', k, tau, yy,
                                B[i])
                        st.add(('B-lo', i), sBlo[i], info)
                        st.add(('B-hi', i), sBhi[i], info)
                    for e in blocks[k]:
                        ce = K[e, e]
                        if ce < 1e-9:
                            continue
                        Ke = schur_np(K, e)
                        Ns = N_coeffs_fast(Ke, bl_del, a)
                        vs = polyvals(Ns, ys)
                        S = vs / vd
                        for i, yy in enumerate(ys):
                            info = (z['name'], depth, path, 'S', e, ce, yy,
                                    S[i])
                            st.add(('S-hi', i), lam[i] - S[i], info)
                            st.add(('S-lo', i), S[i] - 1.0, info)
                # ---- descend
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
        if report_each:
            print(f"--- {z['name']}  (a,b)=({a},{b})  edge={hi:.4f}  "
                  f"paths={npaths}  checks={st.count}  "
                  f"N<=0 events={nneg}  [{time.time()-t0:.1f}s]")
            for i, yy in enumerate(ys):
                row = []
                for key in ('B-lo', 'B-hi', 'S-hi', 'S-lo'):
                    if (key, i) in st.worst:
                        row.append(f"{key} {st.worst[(key, i)][0]:+.4f}")
                print(f"      y=edge+{ys_off[i]:<4}: " + '   '.join(row))
            bad = [(k2, v) for k2, v in st.worst.items() if v[0] < -1e-7]
            for k2, v in bad:
                print(f"      *** VIOLATION {k2}: slack {v[0]:.6f}  info {v[1]}")
        grand[z['name']] = st
        sys.stdout.flush()
    return grand


if __name__ == '__main__':
    rng = np.random.default_rng(777)
    heavy = '--light' not in sys.argv
    zoo = build_zoo(np.random.default_rng(20260801), heavy=heavy)
    # drop the two largest for speed unless asked
    if '--big' not in sys.argv:
        zoo = [z for z in zoo if len(z['blocks']) <= 8]
    npaths = 40
    for arg in sys.argv[1:]:
        if arg.startswith('--paths='):
            npaths = int(arg.split('=')[1])
    run_descents(zoo, rng, npaths=npaths)
