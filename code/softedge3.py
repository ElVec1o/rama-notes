"""Why does the fitted exponent depend on the aspect ratio q/d?

Eight families fit a power law at R^2 >= 0.999, but the exponent tracks q/d: about -0.670 at
q = 2d, -0.627 at 3d, -0.610 at 4d (code/softedge2.py).

FIRST, AN ELIMINATION. "Find the right scaling variable" cannot be the answer. For fixed (d,q)
the vertex count n, the small side r, the large side m and the edge count rq are all
PROPORTIONAL to one another, so the exponent measured against any of them is identical; a
change of variable only moves the constant. The between-family differences are real differences
in how the margin scales with size, not an artefact of which size is used.

THE LIVE ALTERNATIVE is that the margin is not a pure power but carries a correction,

    margin  =  A r^(-a)  ( 1 + B r^(-c) + ... ),

in which case a straight-line fit over a bounded range returns an EFFECTIVE exponent that
depends on how large B is, hence on (d,q), while the true exponent a is common. The diagnostic
is the LOCAL slope: the finite-difference exponent between consecutive sizes. If the local
slopes drift toward a common value as r grows, the exponent is universal and the earlier fits
were contaminated by the correction term. If they stay flat and separated, the exponent really
does depend on q/d.

FROZEN BEFORE THIS DATA:
  P7. The local exponents converge to a common value as r grows, and the apparent
      aspect-ratio dependence is a correction-term artefact.

Also extends to q/d = 5 and 6, to see whether the fitted exponent keeps drifting or flattens.

FASTER COUNTING. The bitmask permanent is now done by bit-slicing rather than fancy indexing:
viewing the state array as (2^(r-1-j), 2, 2^j), the update for bit j is a single strided slice
addition. That is a pure memory pass per bit and takes the reachable r from about 18 to 21.
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

y = sp.Symbol('y')
BUDGET = 1700.0
CKPT = 'private/softedge3_ckpt.txt'


def matching_counts(r, nbr):
    """m_k for k = 0..r, exactly, by a bit-sliced bitmask permanent."""
    size = 1 << r
    dp = np.zeros(size, dtype=np.int64)
    dp[0] = 1
    delta = np.empty(size, dtype=np.int64)
    for s in nbr:
        delta[:] = 0
        for j in s:
            lo = 1 << j
            hi = size >> (j + 1)
            dv = delta.reshape(hi, 2, lo)
            sv = dp.reshape(hi, 2, lo)
            dv[:, 1, :] += sv[:, 0, :]
        dp += delta
        if dp.max() > (1 << 61):
            return None
    idx = np.arange(size, dtype=np.int64)
    pc = np.zeros(size, dtype=np.int64)
    for j in range(r):
        pc[(idx & (1 << j)) != 0] += 1
    return [int(dp[pc == k].sum()) for k in range(r + 1)]


def ymin_from_counts(mk, r):
    co = [((-1) ** k) * int(mk[k]) for k in range(r + 1)]
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return None
    try:
        rs = sorted(sp.re(t) for t in sp.Poly(co, y).nroots(n=30, maxsteps=6000)
                    if abs(sp.im(t)) < 1e-18 and sp.re(t) > 1e-14)
    except Exception:
        return None
    return float(rs[0]) if rs else None


def main():
    print("P7 (frozen): the local exponents converge to a common value; the aspect-ratio")
    print("             dependence is a correction-term artefact.\n")
    FAM = ((3, 6), (4, 8), (5, 10), (6, 12),        # q/d = 2
           (3, 9), (4, 12), (5, 15),                 # q/d = 3
           (3, 12), (4, 16),                         # q/d = 4
           (3, 15), (4, 20),                         # q/d = 5
           (3, 18))                                  # q/d = 6
    t0 = time.time()
    T = {}
    print(f"{'family':>9}{'q/d':>5}{'r':>4}{'n':>6}{'margin_x':>12}{'local exp':>11}")
    for (d, q) in FAM:
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        prev = None
        for r in range(max(d, 6), 22):
            if time.time() - t0 > BUDGET:
                break
            base = biregular_base(d, q, r)
            if base is None:
                continue
            m, nbr0 = base
            n = m + r
            if r > 21 or n > 160:
                continue
            best, used = None, 0
            for seed in range(6):
                nbr = swap_randomize(m, r, nbr0, seed)
                if not check_biregular(m, r, nbr, d, q) or not connected(m, r, nbr):
                    continue
                mk = matching_counts(r, nbr)
                if mk is None:
                    continue
                ym = ymin_from_counts(mk, r)
                if ym is None:
                    continue
                used += 1
                if best is None or ym < best:
                    best = ym
            if best is None or used < 2:
                continue
            mx = math.sqrt(best) - g
            if mx <= 0:
                print(f"  MARGIN NEGATIVE at ({d},{q}) r={r}: {mx:.6f}  -- D3 REFUTED")
                return 1
            loc = ''
            if prev is not None:
                loc = f"{(math.log(mx) - math.log(prev[1])) / (math.log(r) - math.log(prev[0])):>11.4f}"
            prev = (r, mx)
            T.setdefault(f"{d},{q}", []).append((r, n, mx))
            print(f"{f'({d},{q})':>9}{q/d:>5.0f}{r:>4}{n:>6}{mx:>12.6f}{loc:>11}", flush=True)
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"({d},{q}) r={r} margin={mx:.6f}\n")
            os.replace(CKPT + '.tmp', CKPT)
        print()
    json.dump(T, open('data/softedge3_data.json', 'w'))
    print(f"{time.time()-t0:.0f}s\n")

    print("  local exponent between consecutive sizes, by aspect ratio:")
    print(f"{'q/d':>5}{'fam':>5}{'early (small r)':>18}{'late (large r)':>17}{'drift':>9}")
    by = {}
    for k, v in T.items():
        d, q = map(int, k.split(','))
        if len(v) < 6:
            continue
        loc = [(v[i][0], (math.log(v[i][2]) - math.log(v[i - 1][2])) /
                (math.log(v[i][0]) - math.log(v[i - 1][0]))) for i in range(1, len(v))]
        h = len(loc) // 2
        early = float(np.mean([t[1] for t in loc[:h]]))
        late = float(np.mean([t[1] for t in loc[h:]]))
        by.setdefault(q // d, []).append((early, late))
    for rr in sorted(by):
        e = float(np.mean([t[0] for t in by[rr]]))
        l = float(np.mean([t[1] for t in by[rr]]))
        print(f"{rr:>5}{len(by[rr]):>5}{e:>18.4f}{l:>17.4f}{l - e:>+9.4f}")
    if len(by) >= 3:
        lates = [float(np.mean([t[1] for t in v])) for v in by.values()]
        earlies = [float(np.mean([t[0] for t in v])) for v in by.values()]
        se, sl = float(np.std(earlies)), float(np.std(lates))
        print(f"\n  spread of the exponent across aspect ratios: early {se:.4f}, late {sl:.4f}")
        if sl < se * 0.6:
            print("  P7 HOLDS: the local exponents are converging; the exponent is universal and")
            print("  the earlier fits were contaminated by a correction term.")
        else:
            print("  P7 FAILS: the spread does not shrink with size. The exponent genuinely")
            print(f"  depends on q/d, ranging over {min(lates):.3f} to {max(lates):.3f} at "
                  "the largest sizes reached.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
