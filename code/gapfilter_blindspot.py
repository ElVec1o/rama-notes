"""The width filter in every search in this repository discards Hall's own counterexample.

Every search here filters the detected gaps of spec(T) by a minimum width before looking for roots
inside them:

    MIN_GAP = 0.05                                     code/mindeg3.py, mindeg3adv.py,
    gaps = [g for g in gap_profile(...) if wide]        c2attack.py, starcut.py

and skips a graph entirely when no gap survives the filter. Hall's graph has

    gap containing sqrt5 = (2.220, 2.260),  width 0.040 < 0.05,

so it does not survive. Run any of those searches on Hall's 41-vertex counterexample and it is
reported as having no gap, hence clean. The instrument cannot see the one object it was built to
look for.

This is not a failure of gap_profile, which finds the gap correctly. It is the threshold. The
phenomenon lives in gaps of width a few hundredths, and the filter was set above that. The
counterexamples of the two-cut family occupy 0.066 to 0.148, which is presumably where 0.05 came
from, but Hall's own example is narrower than all of them.

CONSEQUENCE. The negative results in this repository are much weaker evidence than they read as.
"806 cut-based configurations, 419 graphs with no separator, 39 with a separating pair, all clean"
means: no violation was found in gaps wider than 0.05. It does not mean no violation was found. A
graph could carry Hall's exact phenomenon and be scored clean.

FROZEN BEFORE THE DATA:
  P71. (a) gap_profile finds a gap of width 0.040 around sqrt5 in Hall's graph.
       (b) With MIN_GAP = 0.05 that gap is discarded and the graph is scored as having no gap.
       (c) With MIN_GAP <= 0.03 it survives, and sqrt5 is then found inside it.

FALSIFICATION. If (a) fails the detector never saw the gap at all and the diagnosis is different,
being a solver problem rather than a threshold problem.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from gapscale import gap_profile
from aomoto_obstruction import hall


def main():
    print("P71 (frozen): the MIN_GAP = 0.05 filter hides Hall's counterexample.\n")
    n, edges, _ = hall(5, 5, True)
    s5 = math.sqrt(5)
    g = gap_profile(n, edges)
    print(f"Hall's graph: n={n}, |E|={len(edges)}, sqrt5 = {s5:.6f}")
    print("gap_profile, unfiltered:")
    holder = None
    for lo, hi in g:
        mark = "   <-- contains sqrt5" if lo < s5 < hi else ""
        if mark:
            holder = (lo, hi)
        print(f"    ({lo:.3f}, {hi:.3f})   width {hi - lo:.3f}{mark}")
    if holder is None:
        print("  P71(a) FAILS: the detector did not find the gap at all.")
        return 1
    print(f"\n(a) HOLDS: the gap is found, width {holder[1] - holder[0]:.3f}")

    print("\n(b),(c) effect of the threshold used by every search in this repository:")
    for thr in (0.05, 0.04, 0.03, 0.02):
        kept = [t for t in g if t[1] - t[0] >= thr]
        alive = any(lo < s5 < hi for lo, hi in kept)
        verdict = "sqrt5 findable" if alive else "graph scored CLEAN, counterexample invisible"
        print(f"    MIN_GAP = {thr:<5}: {len(kept)} gaps kept   ->  {verdict}")
    print("\n  MIN_GAP = 0.05 is the value in mindeg3.py, mindeg3adv.py, c2attack.py and")
    print("  starcut.py. At that setting Hall's 41-vertex counterexample is reported as having")
    print("  no gap. Every 'clean' verdict in this repository must be read as 'no violation in a")
    print("  gap wider than 0.05', which is a much weaker statement and excludes the one example")
    print("  known to exist.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
