"""Is k = 4 a threshold, or was p simply too small?

code/c2_attack.py refutes C2 at k = 3 and finds both k = 4 attempts clean, which invites the reading
that 4-connectivity is a structural barrier: the leaves have degree k+1, so raising k inflates the
degrees, widens the band, and swallows the root. That reading may be right, and it may also be an
artifact of one number.

THE CONFOUND. At k = 3 the same construction is clean at p = 4 and violates at p = 5. So p matters
independently of k, and it is easy to see why: the hub degree is p*m, and it is the hub degree that
pushes an isolated band up and opens the gap the root sits in. Both k = 4 runs were at p = 5. If
larger k merely needs larger p, there is no threshold at k = 4, only a boundary that moved, and the
conclusion "kappa >= 4 is safe" would be false.

THE TEST. Hold m and k fixed and walk p up. If the gap reopens at some p, the k = 4 barrier is not
structural. If it never does, while the k = 3 series violates throughout its range, the barrier is
real and the degree-inflation reading survives its sharpest test.

Connectivity needs delta >= kappa, and the centre has degree m, so kappa = min(m, k, ...) and a
kappa = 4 instance needs m >= 4. Both m = 3 (where kappa stays 3 whatever k is) and m = 4 are run,
the first to isolate the effect of k on the spectrum from the effect of k on connectivity.

FROZEN BEFORE THE DATA:
  P66. (a) The k = 3, m = 3 series violates at every p >= 5 in range, confirming that p, not k,
           opened the gap there.
       (b) At k = 4 the gap REOPENS at some p <= 9, so k = 4 is not a threshold and the two clean
           rows of c2_attack.py were p being too small.
       (c) The p at which the gap opens grows with k, which is the real content: degree inflation
           delays the violation rather than preventing it.

(b) is predicted against the reading that k = 4 is structural, because the mechanism that opens the
gap is the hub degree p*m and nothing in it is capped by k. If (b) fails, the degree-inflation
barrier is real and 4-connectivity becomes the first hypothesis in this subject to survive an
attack designed against it, which would be a genuine positive result and is worth the compute
either way.

FALSIFICATION. If the k = 4 series is clean at every p up to 9 while k = 3 violates throughout,
(b) is refuted and the threshold reading stands. If instead k = 4 violates at some p, the paper
cannot claim a threshold.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from gapscale import gap_profile, connectivity
from d3_counterexample import adj_of, classify
from c2_attack import build_k
import quickmode

BUDGET = 2400.0
NMAX = 56
ETAS = (1e-3, 1e-4, 1e-5)


def main():
    print("P66 (frozen): k = 4 is not a threshold; p was too small.\n")
    print(f"{'k':>2}{'m':>3}{'p':>3}{'n':>5}{'dmin':>5}{'kappa':>6}{'root':>8}"
          f"{'gap holding it':>18}{'verdict':>15}", flush=True)
    t0 = time.time()
    series = {}
    for (k, m) in ([(3, 3), (4, 3), (4, 4)] if quickmode.QUICK
                   else [(3, 3), (4, 3), (4, 4), (5, 5), (6, 4)]):
        lam = math.sqrt(m)
        for p in range(4, 10):
            n = k + p * (m + 1)
            if n > NMAX or time.time() - t0 > BUDGET:
                continue
            edges = build_k(k, m, p)[1]
            adj = adj_of(n, edges)
            deg = [len(adj[i]) for i in range(n)]
            kap = connectivity(n, edges)
            gaps = [t for t in gap_profile(n, edges) if t[1] - t[0] >= 0.05]
            ingap = [(lo, hi) for lo, hi in gaps if lo < lam < hi]
            if not ingap:
                print(f"{k:>2}{m:>3}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{lam:>8.4f}"
                      f"{'-':>18}{'in a band':>15}", flush=True)
                series.setdefault((k, m), []).append((p, False))
                continue
            kind, v = classify(n, edges, lam, etas=ETAS)
            ctrl, _ = classify(n, edges, 0.0, etas=ETAS)
            bad = (kind == 'outside spec' and ctrl == 'ATOM')
            g = ingap[0]
            print(f"{k:>2}{m:>3}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{lam:>8.4f}"
                  f"{f'({g[0]:.2f},{g[1]:.2f})':>18}"
                  f"{('VIOLATION' if bad else kind):>15}", flush=True)
            series.setdefault((k, m), []).append((p, bad))

    print(f"\n{time.time()-t0:.0f}s\n")
    print("first p at which the gap opens, by (k, m):")
    opened = {}
    for key in sorted(series):
        hits = [p for p, b in series[key] if b]
        rng = [p for p, _ in series[key]]
        opened[key] = min(hits) if hits else None
        print(f"  k={key[0]} m={key[1]}: p tested {min(rng)}..{max(rng)},  "
              f"opens at p = {opened[key] if opened[key] else 'never in range'}")

    k4 = [v for kk, v in opened.items() if kk[0] >= 4]
    k3 = opened.get((3, 3))
    if any(v is not None for v in k4):
        print("\n  P66(b) HOLDS. k = 4 is NOT a threshold: the gap reopens once p is large enough.")
        print("  The two clean rows of c2_attack.py were p too small, not connectivity working.")
        print("  Paper 2a must not claim kappa >= 4 as a structural barrier.")
    elif k3 is not None:
        print("\n  P66(b) IS REFUTED, which is the better outcome. k = 3 violates in range and")
        print("  every k >= 4 series is clean across the whole p range tested, so the degree")
        print("  inflation is doing real work and the barrier survives its sharpest test. That is")
        print("  evidence for a threshold, not proof of one: p is bounded here by n <= "
              f"{NMAX}.")
    else:
        print("\n  inconclusive: the k = 3 control did not violate in range either, so the")
        print("  comparison has no baseline and nothing can be read off it.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
