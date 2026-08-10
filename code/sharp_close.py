"""#1: the sharper child-count bound, and what it buys.

child_count_drop gives ku <= k - (q-r) from the path constraint. It omits the most elementary
bound available: a child u of a right-type vertex lies in L, has degree d, and one of its d
neighbours is its parent w, so

    ku <= d - 1

unconditionally. Together,

    ku <= min(d - 1, k - (q - r)).                                                    (SHARP)

That changes the closure condition qualitatively. With only k - Delta, the requirement
k > lambda^2 + lambda(k - Delta)/c is linear in k with slope 1 - lambda/c, so it needs c > lambda
to hold for large k -- which is exactly what fails at Delta small with lambda near the gap edge.
With (SHARP) the worst case saturates at d - 1, so for k > Delta + d - 1 the requirement is just

    k > lambda(lambda + (d-1)/c) = lambda*B,

the uniform one, which holds for all large k regardless of the sign of c. What is left is a
FINITE check over Delta <= k <= Delta + d - 1, plus Delta + d > lambda*B.

FROZEN BEFORE THE DATA:
  P26. With (SHARP) the certificate closes at strictly more parameter points than with
       child_count_drop alone, and in particular at some of the three where P25 failed.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certificate import Bsmall


def closes_old(lam, c, Delta):
    """child_count_drop alone: needs c > lam (and then Delta > lam^2)."""
    if c <= 0:
        return False
    return (lam < c) and (lam * lam < Delta)


def closes_sharp(lam, c, Delta, d, B):
    """min(d-1, k-Delta): finite check on the low range, plus the tail condition."""
    if c <= 0:
        return False
    if not (lam * lam < Delta):
        return False
    # tail: every k > Delta + d - 1 must satisfy k > lam*B; smallest such k is Delta + d
    if not (Delta + d > lam * B):
        return False
    # low range: Delta <= k <= Delta + d - 1, worst case j = k - Delta
    for k in range(Delta, Delta + d):
        j = min(d - 1, k - Delta)
        if not (k > lam * (lam + j / c)):
            return False
    return True


def main():
    print("P26 (frozen): the sharper bound closes at strictly more parameter points.\n")
    print(f"{'(d,q,r)':>12}{'frac':>7}{'lam':>9}{'c':>9}{'Delta':>7}{'old':>7}{'sharp':>7}"
          f"{'gained':>8}")
    nold = nsharp = tested = 0
    gained = []
    for (d, q) in ((3, 6), (3, 9), (3, 12), (3, 20), (4, 8), (4, 12), (5, 10), (5, 15),
                   (6, 12), (4, 20), (6, 18), (3, 30)):
        for r in (q - 1, q - 2, q - 3, max(1, q // 2), max(1, 2 * q // 3)):
            if r <= 0 or q - r <= 0:
                continue
            for frac in (0.1, 0.25, 0.5, 0.75, 0.9, 0.99):
                g = math.sqrt(q - 1) - math.sqrt(d - 1)
                lam = frac * g
                Delta = q - r
                B = Bsmall(d, q, lam, Delta)
                if B is None or B <= 0:
                    continue
                c = Delta / B - lam
                tested += 1
                o = closes_old(lam, c, Delta)
                s = closes_sharp(lam, c, Delta, d, B)
                nold += o; nsharp += s
                if s and not o:
                    gained.append((d, q, r, frac, lam, c, Delta))
                if frac in (0.5, 0.99) and r in (q - 1, max(1, q // 2)):
                    print(f"{f'({d},{q},{r})':>12}{frac:>7.2f}{lam:>9.4f}{c:>9.4f}{Delta:>7}"
                          f"{str(o):>7}{str(s):>7}{('YES' if s and not o else ''):>8}")

    print(f"\n  parameter points tested : {tested}")
    print(f"  closes with child_count_drop alone : {nold}  ({100*nold/max(tested,1):.1f}%)")
    print(f"  closes with the sharper bound      : {nsharp}  ({100*nsharp/max(tested,1):.1f}%)")
    print(f"  gained by the sharper bound        : {len(gained)}")
    if gained:
        print("\n  Points the sharper bound closes and the old one does not:")
        for (d, q, r, frac, lam, c, Delta) in gained[:12]:
            print(f"    (d,q,r)=({d},{q},{r}) frac={frac}: lam={lam:.4f} c={c:.4f} Delta={Delta}")
    if nsharp > nold:
        print("\n  P26 HOLDS. The elementary degree bound ku <= d-1, which child_count_drop")
        print("  omits, converts an unbounded linear requirement into a finite check.")
    else:
        print("\n  P26 IS FALSE: the sharper bound gains nothing at these parameters.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
