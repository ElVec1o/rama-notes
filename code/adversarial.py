"""Adversarial search: directly MINIMISE the smallest root (resp. MAXIMISE the
largest root) of mu[A_1..A_q] over families of rank-b projections (or rank-b
PSD) with sum = a I, to try to break the tree band [(s-t)^2,(s+t)^2]."""
import sys
import time
import numpy as np
from mixed_char_poly import mixed_char_poly, band
from tff import (build_tff, build_psd_family, rand_projections, restore,
                 tff_residual, random_biregular, graph_to_projections,
                 commutativity, proj_rank_b)
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode
import os as _os, tempfile as _tempfile
SCRATCH = _os.environ.get('RAMA_SCRATCH', _tempfile.gettempdir())
_os.makedirs(SCRATCH, exist_ok=True)


def obj(A, mode):
    c = mixed_char_poly(A)
    r = np.sort(np.roots(c).real)
    return (r.min() if mode == 'lo' else -r.max()), r


def perturb(A, b, eps, rng):
    q, p, _ = A.shape
    w, V = np.linalg.eigh(A)
    U = V[:, :, -b:] + eps * rng.standard_normal((q, p, b))
    Uq, _ = np.linalg.qr(U)
    return Uq @ np.swapaxes(Uq, 1, 2)


def hill_climb(p, q, a, b, rng, mode='lo', n_restart=10, n_step=500,
               psd_class=False, starts=None, eps0=0.4, verbose=False):
    best_val, best_A = 1e18, None
    for rs in range(n_restart):
        if starts is not None and rs < len(starts):
            A = starts[rs].copy()
            res = 0.0 if psd_class else tff_residual(A, a)
        elif psd_class:
            A = build_psd_family(p, q, a, b, rng)
            res = 0.0
        else:
            A, res = build_tff(p, q, a, b, rng)
        if res > 1e-9:
            continue
        val, _ = obj(A, mode)
        eps, stall = eps0, 0
        for step in range(n_step):
            new = perturb(A, b, eps, rng)
            if psd_class:
                new = build_psd_family(p, q, a, b, rng, A=new)
                nres = 0.0
            else:
                new, nres = restore(new, q, p, a, b, iters=400)
            if nres > 1e-9:
                stall += 1
                continue
            nval, _ = obj(new, mode)
            if nval < val - 1e-14:
                A, val = new, nval
                stall = 0
            else:
                stall += 1
                if stall > 20:
                    eps *= 0.6
                    stall = 0
                    if eps < 1e-6:
                        break
        if val < best_val:
            best_val, best_A = val, A.copy()
        if verbose:
            print(f"    restart {rs}: {val:.9f} (best {best_val:.9f})", flush=True)
    return best_val, best_A


PARAMS = quickmode.few([
    (4, 6, 3, 2),
    (3, 6, 4, 2),
    (6, 9, 3, 2),
    (6, 8, 4, 3),
    (4, 8, 4, 2),
    (6, 10, 5, 3),
    (5, 10, 4, 2),
    (8, 10, 5, 4),
    (8, 12, 3, 2),
    (4, 10, 5, 2),
])

if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(PARAMS)))
    rng = np.random.default_rng(31337)
    for idx in sel:
        p, q, a, b = PARAMS[idx]
        lo, hi = band(a, b)
        t0 = time.time()
        print("=" * 78)
        print(f"[{idx}] p={p} q={q} (a,b)=({a},{b})  band=[{lo:.8f},{hi:.8f}]"
              f"  MP=[{(np.sqrt(a)-np.sqrt(b))**2:.4f},{(np.sqrt(a)+np.sqrt(b))**2:.4f}]",
              flush=True)
        gmin, gmax, ng = 1e9, -1e9, 0
        for _ in range(300):
            adj = random_biregular(p, q, a, b, rng)
            if adj is None:
                continue
            ng += 1
            r = np.sort(np.roots(mixed_char_poly(graph_to_projections(adj, p, q))).real)
            gmin, gmax = min(gmin, r.min()), max(gmax, r.max())
        print(f"  graphs({ng})   : min r_min={gmin:.9f} (margin {gmin-lo:+.9f})   "
              f"max r_max={gmax:.9f} (margin {hi-gmax:+.9f})", flush=True)
        for cls, flag in (("projections", False), ("PSD rank-b ", True)):
            v_lo, A_lo = hill_climb(p, q, a, b, rng, 'lo', psd_class=flag)
            v_hi, A_hi = hill_climb(p, q, a, b, rng, 'hi', psd_class=flag)
            print(f"  {cls}: min r_min={v_lo:.9f} (margin {v_lo-lo:+.9f})   "
                  f"max r_max={-v_hi:.9f} (margin {hi+v_hi:+.9f})", flush=True)
            print(f"      commutator norm at optimum: lo-family {commutativity(A_lo):.3e}"
                  f"   hi-family {commutativity(A_hi):.3e}", flush=True)
            _stem = f"adv_{p}_{q}_{a}_{b}_{cls.strip()[:4]}"
            np.save(os.path.join(SCRATCH, _stem + "_lo.npy"), A_lo)
            np.save(os.path.join(SCRATCH, _stem + "_hi.npy"), A_hi)
        print(f"  ({time.time()-t0:.0f}s)", flush=True)
