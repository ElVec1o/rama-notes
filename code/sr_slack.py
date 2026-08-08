"""sr_slack.py -- how much room is there between the matrix optimum and the
band edge?  This says how much a hypothetical non-matrix strongly Rayleigh law
would have to gain in order to refute (SR-BAND).

For each (p,q,a,b) we maximise lambda_max (and minimise lambda_min) over
rank-b projection families by random restarts plus a local hill climb on the
Grassmannian (perturb, re-project onto the feasible set, accept if better),
and compare with

    hi  = (sqrt(a-1)+sqrt(b-1))^2      the band edge,
    LP  = the (i)+(ii) optimum from sr_lp2.py,
    ab  = the trivial bound.
"""
import sys
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import band, rand_proj_family                              # noqa
from mcp2 import mcp, restore_proj, rand_X, proj_from_X                  # noqa


def lam(P):
    r = np.roots(mcp(P))
    rr = np.sort(r.real)
    return float(rr.max()), float(rr.min()), float(np.abs(r.imag).max())


def climb(p, q, a, b, seed=0, restarts=14, steps=260, upper=True):
    rng = np.random.default_rng(seed)
    best = None
    for t in range(restarts):
        P, res = rand_proj_family(p, q, a, b, seed=seed + 977 * t)
        if res > 1e-11:
            continue
        hi_, lo_, im = lam(P)
        cur = hi_ if upper else -lo_
        scale = 0.35
        for it in range(steps):
            X = rng.normal(size=(q, p, b)) * scale
            Q, _ = np.linalg.qr(np.linalg.qr(P.transpose(0, 2, 1)[:, :, :b])[0]
                                if False else
                                (P @ rng.normal(size=(q, p, b))) + X)
            A = Q @ np.swapaxes(Q, 1, 2)
            A, r = restore_proj(A, q, p, a, b, iters=3000, tol=1e-13)
            if r > 1e-10:
                scale *= 0.7
                continue
            h2, l2, im2 = lam(A)
            new = h2 if upper else -l2
            if new > cur + 1e-13:
                P, cur = A, new
                scale = min(scale * 1.15, 0.6)
            else:
                scale *= 0.82
            if scale < 1e-7:
                break
        if best is None or cur > best[0]:
            best = (cur, P)
    return best


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 92)
    print(f"{'(p,q,a,b)':>14} {'lo':>9} {'matrix min':>11} {'matrix max':>11} "
          f"{'hi':>9} {'slack@hi':>9} {'LP(i+ii)':>9} {'ab':>5}")
    print("=" * 92)
    LP = {(4, 6, 3, 2): None, (6, 9, 3, 2): 6.0, (3, 6, 4, 2): None,
          (4, 8, 4, 2): None, (5, 5, 3, 3): None, (6, 8, 4, 3): None,
          (3, 4, 4, 3): None, (4, 5, 5, 4): None, (7, 7, 3, 3): None,
          (6, 6, 3, 3): None}
    for (p, q, a, b) in [(3, 4, 4, 3), (4, 6, 3, 2), (3, 6, 4, 2), (4, 8, 4, 2),
                         (6, 9, 3, 2), (5, 5, 3, 3), (6, 6, 3, 3), (7, 7, 3, 3),
                         (6, 8, 4, 3), (4, 5, 5, 4)]:
        lo, hi = band(a, b)
        bu = climb(p, q, a, b, seed=11, restarts=10, steps=200, upper=True)
        bl = climb(p, q, a, b, seed=23, restarts=10, steps=200, upper=False)
        mx = bu[0] if bu else float('nan')
        mn = -bl[0] if bl else float('nan')
        lp = LP.get((p, q, a, b))
        lps = f"{lp:9.4f}" if lp else f"{'forced':>9}"
        print(f"{str((p,q,a,b)):>14} {lo:9.4f} {mn:11.5f} {mx:11.5f} "
              f"{hi:9.4f} {hi-mx:9.5f} {lps} {a*b:5d}")
