"""Why does the margin exponent depend on the aspect ratio?  Measure the edge density.

The soft-edge heuristic is explicit about the mechanism.  If the roots of mu_G accumulate near
the inner edge g with density vanishing like (x - g)^beta, then the expected number of roots
within delta of the edge is about N int_0^delta t^beta dt ~ N delta^(beta+1), and the smallest
root sits where that count is order one:

    margin  ~  N^(-1/(beta+1)).

A square-root edge, beta = 1/2, gives exponent -2/3, and it gives it UNIVERSALLY, for every
(d,q).  Since the measured exponent is -0.667 at q = 2d but about -0.62 for q >= 3d
(code/softedge3.py), either beta varies with the aspect ratio, in which case the mechanism is
identified and the dependence is explained, or it does not, in which case the soft-edge reading
is wrong and something else sets the scale.

FROZEN BEFORE THIS DATA:
  P8. beta varies with q/d, and -1/(beta+1) reproduces the measured margin exponent in every
      family to within the fitting error.

If P8 holds, the aspect-ratio dependence is a statement about the edge behaviour of the
biregular tree spectral measure and nothing more mysterious.  If P8 fails, the two exponents
disagree and the soft-edge picture, which is currently the interpretation of the whole result,
is wrong.

METHOD.  A single graph of the sizes reachable here has only r positive roots, far too few to
resolve a density.  So the roots are POOLED over many independent samples at fixed r: the
counting function N(delta) is the average number of roots at most g + delta per graph, and
beta + 1 is the slope of log N against log delta over a window small compared with the band
width 2 sqrt(d-1).
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import json
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from softedge2 import biregular_base, swap_randomize, connected, check_biregular
from softedge3 import matching_counts

yv = sp.Symbol('y')
BUDGET = 1600.0


def all_pos_roots(mk, r):
    co = [((-1) ** k) * int(mk[k]) for k in range(r + 1)]
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return []
    try:
        return sorted(float(sp.sqrt(sp.re(t)))
                      for t in sp.Poly(co, yv).nroots(n=25, maxsteps=6000)
                      if abs(sp.im(t)) < 1e-16 and sp.re(t) > 1e-12)
    except Exception:
        return []


def pooled_roots(d, q, r, nsample):
    base = biregular_base(d, q, r)
    if base is None:
        return None
    m, nbr0 = base
    pool, got = [], 0
    for seed in range(nsample * 3):
        if got >= nsample:
            break
        nbr = swap_randomize(m, r, nbr0, seed)
        if not check_biregular(m, r, nbr, d, q) or not connected(m, r, nbr):
            continue
        mk = matching_counts(r, nbr)
        if mk is None:
            continue
        rts = all_pos_roots(mk, r)
        if not rts:
            continue
        pool.extend(rts); got += 1
    return (pool, got) if got >= 8 else None


def main():
    print("P8 (frozen): beta varies with q/d, and -1/(beta+1) reproduces the margin exponent.\n")
    measured = {}
    try:
        D = json.load(open('private/softedge3_data.json'))
        for k, v in D.items():
            if len(v) >= 6:
                ln = np.log([t[1] for t in v]); lm = np.log([t[2] for t in v])
                measured[k] = float(np.polyfit(ln, lm, 1)[0])
    except Exception:
        pass

    FAM = ((3, 6), (4, 8), (5, 10), (3, 9), (4, 12), (3, 12), (3, 15))
    print(f"{'family':>9}{'q/d':>5}{'r':>4}{'graphs':>8}{'roots':>7}{'beta':>9}"
          f"{'-1/(b+1)':>11}{'measured':>10}{'diff':>8}")
    t0 = time.time()
    rows = []
    for (d, q) in FAM:
        if time.time() - t0 > BUDGET:
            break
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        band = 2 * math.sqrt(d - 1)
        r = 15
        P = pooled_roots(d, q, r, 45)
        if P is None:
            continue
        pool, ng = P
        arr = np.array(pool)
        # counting function over a window small compared with the band width
        ds = np.array([band * f for f in (0.02, 0.03, 0.05, 0.07, 0.10, 0.14, 0.20, 0.28)])
        N = np.array([np.sum(arr <= g + t) / ng for t in ds])
        ok = N > 0.3
        if ok.sum() < 4:
            continue
        slope = float(np.polyfit(np.log(ds[ok]), np.log(N[ok]), 1)[0])
        beta = slope - 1.0
        pred = -1.0 / (beta + 1.0)
        meas = measured.get(f"{d},{q}")
        diff = (pred - meas) if meas is not None else float('nan')
        print(f"{f'({d},{q})':>9}{q/d:>5.0f}{r:>4}{ng:>8}{len(pool):>7}{beta:>9.4f}"
              f"{pred:>11.4f}"
              f"{(f'{meas:.4f}' if meas is not None else '-'):>10}"
              f"{(f'{diff:+.4f}' if meas is not None else '-'):>8}", flush=True)
        rows.append((d, q, beta, pred, meas))
    print(f"\n{time.time()-t0:.0f}s\n")
    if len(rows) < 4:
        print("  too few families to judge P8.")
        return 0
    betas = [t[2] for t in rows]
    print(f"  beta across families: {min(betas):.4f} to {max(betas):.4f}, "
          f"spread {np.std(betas):.4f}")
    print(f"  square-root edge would be beta = 0.5 exactly, giving -2/3 in every family.")
    good = [t for t in rows if t[4] is not None]
    if good:
        errs = [abs(t[3] - t[4]) for t in good]
        print(f"  |predicted - measured| exponent: mean {np.mean(errs):.4f}, "
              f"max {max(errs):.4f}")
        by = {}
        for d, q, b, p, mm in good:
            by.setdefault(q // d, []).append(b)
        print("\n  beta by aspect ratio:")
        for k in sorted(by):
            print(f"    q/d = {k}: beta = {np.mean(by[k]):.4f}  (n={len(by[k])})")
        if max(errs) < 0.03 and np.std(betas) > 0.03:
            print("\n  P8 HOLDS: beta varies with q/d and -1/(beta+1) reproduces the measured")
            print("  exponent. The aspect-ratio dependence is the edge behaviour of the")
            print("  biregular tree spectral measure, nothing more.")
        elif np.std(betas) < 0.03:
            print(f"\n  P8 FAILS on the first clause: beta is essentially CONSTANT "
                  f"({np.mean(betas):.3f}) across aspect ratios, so it cannot explain a "
                  "varying margin exponent.")
        else:
            print(f"\n  P8 FAILS on the second clause: -1/(beta+1) does not reproduce the "
                  f"measured exponent (max error {max(errs):.4f}). The soft-edge reading is "
                  "not the mechanism.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
