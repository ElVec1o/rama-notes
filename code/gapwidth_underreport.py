"""The gap detector under-reports widths by up to 2.5x, and that is why counterexamples were missed.

code/gapfilter_blindspot.py showed that MIN_GAP = 0.05 discards Hall's counterexample, whose gap
gap_profile reports as width 0.040. That diagnosis was incomplete, and the incomplete version is
recorded in the git history of this repository rather than silently replaced.

The real problem is not that the gaps are narrow. It is that gap_profile UNDER-REPORTS their width.
It scans in steps of 0.02 and asks rho_at whether each point is outside spec(T); rho_at is a
fixed-point iteration that fails to converge at most points inside a gap, returning None, and
gap_profile scores None as "in the spectrum". A gap therefore appears as a few isolated converged
points rather than an interval, and its reported width collapses toward the 0.04 floor, which is two
scan steps.

Fine scanning at step 0.0005, and treating non-convergence as UNKNOWN rather than as "in spectrum",
gives certified widths:

    Hall's 41-vertex example        0.0295     (reported 0.040)
    new counterexample n = 36       0.1035     (reported 0.040)
    new counterexample n = 36       0.1000     (reported 0.040)
    new counterexample n = 37       0.0305     (reported 0.040)
    new counterexample n = 37       0.0400     (reported 0.040)

and only 25 to 58 percent of the fine-scan points converge at all, so even these are lower bounds.

Two of the new counterexamples sit in gaps of width about 0.10, twice the 0.05 filter threshold.
They were still missed, because the reported width was 0.040. So the earlier statement that "the
phenomenon lives in gaps below the threshold" is wrong: it lives in gaps that the instrument
describes as below the threshold.

The violating root sits at 40 to 61 percent of the way across the gap in four of the five cases,
which is roughly central, and at 99 percent in the fifth, which is marginal and should be treated as
the least robust of the set.

FROZEN BEFORE THE DATA:
  P73. (a) The certified widths differ from the reported 0.040, so the coarse scan is not resolving
           the gaps.
       (b) At least one counterexample sits in a gap wider than the 0.05 threshold and was still
           discarded, which shows the failure is under-reporting rather than genuine narrowness.
       (c) Convergence is well below 100 percent throughout, so every width here is a lower bound.

FALSIFICATION. If the fine scan returns the same 0.040 everywhere, the gaps really are that narrow
and the original threshold diagnosis was right as stated.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from gapscale import setup, rho_at, gap_profile
from aomoto_obstruction import hall

STEP = 0.0005
HALF = 0.06


def certified_gap(n, edges, theta, half=HALF, step=STEP):
    """Scan finely around theta. Non-convergence is UNKNOWN, never 'in the spectrum'."""
    B, M = setup(n, edges)
    lo = hi = None
    conv = tot = 0
    k = int(half / step)
    for i in range(-k, k + 1):
        lam = theta + i * step
        r = rho_at(lam, B, M)
        tot += 1
        if r is not None:
            conv += 1
        if r is not None and r < 1:
            lo = lam if lo is None else min(lo, lam)
            hi = lam if hi is None else max(hi, lam)
    return lo, hi, conv, tot


def main():
    print("P73 (frozen): the detector under-reports gap widths.\n")
    cases = []
    n, e, _ = hall(5, 5, True)
    cases.append(("Hall 41v", n, e, math.sqrt(5)))
    for o in json.load(open(os.path.join(os.path.dirname(__file__), '..',
                                         'data', 'lowgap_counterexamples.json'))):
        cases.append((f"new n={o['n']} root {o['root']:.4f}", o['n'],
                      [tuple(t) for t in o['edges']], o['root']))

    print(f"{'example':>26}  {'reported':>9}  {'certified':>10}  {'ratio':>6}  "
          f"{'root pos':>9}  {'converged':>10}")
    widths = []
    for nm, n, e, th in cases:
        gp = [g for g in gap_profile(n, e) if g[0] < th < g[1]]
        rep = (gp[0][1] - gp[0][0]) if gp else 0.0
        lo, hi, conv, tot = certified_gap(n, e, th)
        if lo is None:
            print(f"{nm:>26}  {rep:>9.4f}  {'none':>10}")
            continue
        w = hi - lo
        widths.append((nm, rep, w))
        pos = (th - lo) / w if w > 0 else 0.5
        print(f"{nm:>26}  {rep:>9.4f}  {w:>10.4f}  {w/rep if rep else 0:>6.2f}x"
              f"  {pos*100:>8.1f}%  {conv:>5}/{tot}")

    print()
    bad = [(nm, rep, w) for nm, rep, w in widths if w > 0.05 and rep < 0.05]
    if bad:
        print("  P73(b) HOLDS. These sit in gaps WIDER than the 0.05 filter and were still")
        print("  discarded, because the reported width was below it:")
        for nm, rep, w in bad:
            print(f"    {nm}: true width {w:.4f}, reported {rep:.4f}")
        print("  So the failure is under-reporting, not genuine narrowness. A correct detector")
        print("  would have found these at the original threshold.")
    else:
        print("  P73(b) fails: no example is wider than the threshold, so narrowness alone")
        print("  explains the misses and the earlier diagnosis stands as stated.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
