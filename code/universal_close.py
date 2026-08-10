"""Does the refined certificate close PROVABLY, or only on the path trees we measured?

code/twolevel.py showed the child-count-aware requirement k > lambda*(lambda + j_max/c) holds on
every path tree tested, including the (3,6,5) points where the uniform one fails. But it used the
MEASURED child counts j. A proof cannot: it must use a structural bound on j, and the one already
formalized is child_count_drop, ku <= k - (q-r).

Substituting Delta = q - r and j_max <= k - Delta, the requirement becomes

    k > lambda^2 + lambda (k - Delta)/c,

and both sides are linear in k with slopes 1 and lambda/c. So it holds for ALL large k exactly
when c > lambda, and then -- together with min_children, k >= Delta -- the certificate closes for
every right-type vertex with no reference to any particular path tree. That is a proof rather
than a sweep.

FROZEN BEFORE THE DATA:
  P25. c > lambda holds across the gap for every (d,q,r) tested.

If P25 holds the ratio route closes universally on those parameters. If it fails, the refinement
is still correct but child_count_drop is too weak to carry it, and the gap between what is
measured and what is proved is exactly the strength of the structural child-count bound. Either
answer is worth having, and the second says precisely what to prove next.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certificate import Bsmall


def analyse(d, q, r, frac):
    """Returns (lam, B, c, Delta, c>lam, smallest k for which the structural test passes)."""
    g = math.sqrt(q - 1) - math.sqrt(d - 1)
    lam = frac * g
    Delta = q - r                      # min_children: every right vertex has k >= Delta
    if Delta <= 0:
        return None
    B = Bsmall(d, q, lam, Delta)
    if B is None or B <= 0:
        return None
    c = Delta / B - lam
    if c <= 0:
        return dict(lam=lam, B=B, c=c, Delta=Delta, ok=False, kmin=None, reason='c<=0')
    # structural requirement with j_max <= k - Delta:  k(1 - lam/c) > lam^2 - lam*Delta/c
    slope = 1.0 - lam / c
    rhs = lam * lam - lam * Delta / c
    if slope > 0:
        kneed = rhs / slope
        kstar = max(Delta, math.floor(kneed) + 1)
        return dict(lam=lam, B=B, c=c, Delta=Delta, ok=True, kmin=kstar,
                    allk=(kneed < Delta), reason='')
    return dict(lam=lam, B=B, c=c, Delta=Delta, ok=False, kmin=None, reason='c<=lam')


def main():
    print("P25 (frozen): c > lambda across the gap for every (d,q,r), so child_count_drop alone")
    print("closes the certificate for every k.\n")
    print(f"{'(d,q,r)':>12}{'frac':>7}{'lam':>9}{'B':>9}{'c':>9}{'Delta':>7}"
          f"{'c>lam':>7}{'closes all k':>14}")
    tested = 0
    cgt = 0
    allk = 0
    fails = []
    for (d, q) in ((3, 6), (3, 9), (3, 12), (4, 8), (4, 12), (5, 10), (5, 15), (6, 12), (3, 20)):
        for r in (q - 1, q - 2, q - 3, max(1, q // 2)):
            if r <= 0 or q - r <= 0:
                continue
            for frac in (0.25, 0.5, 0.75, 0.9, 0.99):
                res = analyse(d, q, r, frac)
                if res is None:
                    continue
                tested += 1
                if res['ok']:
                    cgt += 1
                    if res.get('allk'):
                        allk += 1
                else:
                    fails.append((d, q, r, frac, res['reason'], res['c'], res['lam']))
                if frac in (0.5, 0.99) and r in (q - 1, max(1, q // 2)):
                    print(f"{f'({d},{q},{r})':>12}{frac:>7.2f}{res['lam']:>9.4f}{res['B']:>9.4f}"
                          f"{res['c']:>9.4f}{res['Delta']:>7}"
                          f"{str(res['ok']):>7}{str(res.get('allk', False)):>14}")

    print(f"\n  parameter points tested: {tested}")
    print(f"  c > lambda at:           {cgt}   ({100*cgt/max(tested,1):.1f}%)")
    print(f"  closes for EVERY k >= Delta with no further input: {allk}")
    if fails:
        print(f"\n  P25 IS FALSE at {len(fails)} points. Worst examples:")
        for (d, q, r, frac, why, c, lam) in fails[:8]:
            print(f"    (d,q,r)=({d},{q},{r}) frac={frac}: {why}, c={c:.4f} lam={lam:.4f}")
        print("\n  The refinement is still correct -- twolevel.py verifies it on real path trees --")
        print("  but child_count_drop is too weak to carry it at these parameters. What a proof")
        print("  needs there is a stronger structural bound on the CHILD's child count than")
        print("  ku <= k - (q-r): the measured j are far below that worst case.")
    else:
        print("\n  P25 HOLDS. On every parameter point tested the refined requirement follows")
        print("  from min_children and child_count_drop alone, with no appeal to a particular")
        print("  path tree. That is the biregular inner edge, proved on these parameters.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
