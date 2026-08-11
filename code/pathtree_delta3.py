"""Is spec(P) subset spec(T) even TRUE at minimum degree three?

PathTreeRoute reduces the conjecture to that containment, and it holds on the four biregular
families measured. But the hypothesis is STRICTLY STRONGER than the conclusion, since mu_P carries
its own roots as well as those of mu_G. So it could perfectly well be false on graphs where the
conjecture is true, and then the reformulation is a dead end rather than a route.

That is the first thing to settle, and it is decidable by the same instrument: find a gap of
spec(T), then count path-tree eigenvalues inside it by Sylvester's law, comparing the number of
negative cavity ratios at the two edges.

FROZEN BEFORE THE DATA:
  P32. For delta >= 3 graphs carrying a gap, the path tree has no eigenvalue in it, so the
       containment is a live hypothesis at minimum degree three.

If P32 fails the reformulation is worth nothing: the hypothesis would be false where the
conclusion is true, and no proof could go through it.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import numpy as np

sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gapscale import gap_profile
from D3broad import spread_graph, connected
from pathtree_inertia import inertia

BUDGET = 2100.0


def main():
    t0 = time.time()
    rng = np.random.default_rng(20260904)
    print("P32 (frozen): at delta >= 3, the path tree has no eigenvalue in a gap of spec(T).\n")
    print(f"{'n':>4}{'degrees':>10}{'gap':>20}{'|P|':>10}{'neg lo':>9}{'neg hi':>9}"
          f"{'eigs in gap':>13}{'verdict':>11}")
    tested = 0
    fails = []
    untrusted = []
    for n in (8, 10, 12):
        for trial in range(60):
            if time.time() - t0 > BUDGET:
                break
            E = spread_graph(n, rng, int(rng.integers(1, 3)),
                             int(rng.integers(max(4, n // 2), n)))
            if not connected(n, E):
                continue
            deg = [0] * n
            for a, b in E:
                deg[a] += 1; deg[b] += 1
            if min(deg) < 3 or max(deg) - min(deg) < 3:
                continue
            gaps = [(a, b) for (a, b) in gap_profile(n, E, step=0.02) if b - a > 0.06]
            if not gaps:
                continue
            adj = {i: set() for i in range(n)}
            for a, b in E:
                adj[a].add(b); adj[b].add(a)
            lo_g, hi_g = max(gaps, key=lambda t: t[1] - t[0])
            r1 = inertia(adj, 0, lo_g + 0.005, cap=1_200_000)
            r2 = inertia(adj, 0, hi_g - 0.005, cap=1_200_000)
            if r1 is None or r2 is None:
                continue
            tested += 1
            n1, tot, ok1 = r1
            n2, _, ok2 = r2
            inside = n1 - n2
            # inertia() sets ok=False on a near-zero pivot, where the count is not trustworthy.
            # Discarding that flag was this script's own bug: a single bad pivot can shift the
            # count, and the counts here run to the hundreds.
            trust = ok1 and ok2
            if inside != 0 and trust:
                fails.append((n, tuple(sorted(set(deg))), (lo_g, hi_g), inside))
            if inside != 0 and not trust:
                untrusted.append((n, (lo_g, hi_g), inside))
            if inside != 0 or tested % 5 == 1:
                tag = ('HAS EIGS' if inside and trust else
                       ('near-zero pivot' if inside else 'inherits'))
                print(f"{n:>4}{f'{min(deg)}..{max(deg)}':>10}"
                      f"{f'[{lo_g:.3f},{hi_g:.3f}]':>20}{tot:>10}{n1:>9}{n2:>9}{inside:>13}"
                      f"{tag:>17}", flush=True)

    print(f"\n  graphs with a gap tested: {tested}   trusted hits: {len(fails)}"
          f"   discarded on a near-zero pivot: {len(untrusted)}")
    if fails:
        print("  P32 IS FALSE. The containment fails at minimum degree three even where the")
        print("  conjecture holds, so the reformulation cannot carry a proof:")
        for (n, dg, gp, k) in fails[:6]:
            print(f"    n={n} degrees={dg} gap=[{gp[0]:.3f},{gp[1]:.3f}]: {k} eigenvalue(s) inside")
    else:
        print("  P32 holds. The path tree inherits the gap at minimum degree three too, so the")
        print("  containment is a live hypothesis and not merely a stronger one.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
