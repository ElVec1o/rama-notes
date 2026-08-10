"""Audit of section 10's checkable claims, on the corrected instrument.

The reply to Xu was gated on this. Section 10 is what the exchange leans on -- the barrier
obstruction, the band equivalence, and the largest-root bounds -- and one of its claims had
already been found to need care (the recentring constant, code/rl_conj.py), so the rest is
checked here rather than assumed.

Five claims, each verified against something independent of the note.

  1. Marchenko-Pastur is strictly wider than the tree band, the discrepancy being
     2[sqrt(ab) - sqrt((a-1)(b-1)) - 1] >= 0 with equality only at a = b.
  2. A_k = (b/p) I_p satisfies every hypothesis a rank-blind barrier uses -- PSD, tr A_k = b,
     sum A_k = aI -- and its mixed characteristic polynomial exceeds the tree band already at
     (a,b) = (3,2), p = 4, with largest root 6.229.
  3. Every root of mu[P_1,...,P_q] is at most ab.
  4. At b = 2 the extreme roots are a(1 +/- sqrt(pi_max)).
  5. prop:ineq2: at b = 2 the band is equivalent to pi_max <= 4(a-1)/a^2.

A NOTE ON CLAIM 1, because it fails if read carelessly and that is instructive. The expression
2[sqrt(ab) - sqrt((a-1)(b-1)) - 1] is NOT the gap at the upper band edge; that gap is the same
expression with +1 and never vanishes. It is the gap at the LOWER edge, tb_lo - mp_lo, and there
it does vanish exactly at a = b. Comparing it to the upper edge makes the note look doubly wrong,
with a sign error and a false equality claim, when it is right. The audit therefore checks the
expression against both edges and reports which one it is.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mixed_char_poly import mixed_char_poly, band
from tff import build_tff

rng = np.random.default_rng(20260827)


def claim1():
    """Which edge does the note's discrepancy measure, and where is it zero?"""
    lower_ok, eq = True, []
    for a in range(2, 13):
        for b in range(2, 13):
            D = 2 * (math.sqrt(a * b) - math.sqrt((a - 1) * (b - 1)) - 1)
            mp_lo = (math.sqrt(a) - math.sqrt(b)) ** 2
            tb_lo = (math.sqrt(a - 1) - math.sqrt(b - 1)) ** 2
            if abs(D - (tb_lo - mp_lo)) > 1e-9:
                lower_ok = False
            if abs(D) < 1e-12:
                eq.append((a, b))
    return lower_ok and all(a == b for (a, b) in eq), eq[:5]


def claim2():
    a, b, p = 3, 2, 4
    q = a * p // b
    As = [(b / p) * np.eye(p) for _ in range(q)]
    S = sum(As)
    r = np.roots(mixed_char_poly(As)).real
    lo, hi = band(a, b)
    hyp = abs(S[0, 0] - a) < 1e-12 and abs(float(np.trace(As[0])) - b) < 1e-12
    return hyp and r.max() > hi and abs(r.max() - 6.229) < 0.01, float(r.max()), hi


def claim3():
    for (p, q, a, b) in ((4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (8, 10, 5, 4), (4, 8, 4, 2)):
        for _ in range(40):
            A, res = build_tff(p, q, a, b, rng)
            if res > 1e-9:
                continue
            if np.roots(mixed_char_poly(A)).real.max() > a * b + 1e-8:
                return False
    return True


def claim4():
    worst = 0.0
    for (p, q, a, b) in ((4, 6, 3, 2), (6, 9, 3, 2), (4, 8, 4, 2), (5, 10, 4, 2)):
        for _ in range(15):
            A, res = build_tff(p, q, a, b, rng)
            if res > 1e-9:
                continue
            r = np.sort(np.roots(mixed_char_poly(A)).real)
            pim = ((r.max() / a) - 1.0) ** 2
            worst = max(worst, abs(a * (1.0 - math.sqrt(pim)) - r.min()))
    return worst < 1e-6, worst


def claim5():
    for (p, q, a, b) in ((4, 6, 3, 2), (6, 9, 3, 2), (4, 8, 4, 2), (5, 10, 4, 2)):
        for _ in range(25):
            A, res = build_tff(p, q, a, b, rng)
            if res > 1e-9:
                continue
            r = np.roots(mixed_char_poly(A)).real
            lo, hi = band(a, b)
            inband = (r.min() >= lo - 1e-9) and (r.max() <= hi + 1e-9)
            pim = ((r.max() / a) - 1.0) ** 2
            if inband != (pim <= 4 * (a - 1) / a ** 2 + 1e-9):
                return False
    return True


def main():
    print("Audit of section 10, five checkable claims.\n")
    c1, eq = claim1()
    print(f"  1  MP-vs-band discrepancy is the LOWER-edge gap, zero only at a=b   "
          f"{'PASS' if c1 else 'FAIL'}   (zeros at {eq})")
    c2, rmax, hi = claim2()
    print(f"  2  rank-blind A_k=(b/p)I exceeds the band, root {rmax:.4f} vs {hi:.4f}   "
          f"{'PASS' if c2 else 'FAIL'}")
    c3 = claim3()
    print(f"  3  every root of mu at most ab                                      "
          f"{'PASS' if c3 else 'FAIL'}")
    c4, w = claim4()
    print(f"  4  extreme roots a(1 +/- sqrt(pi_max)), error {w:.2e}                "
          f"{'PASS' if c4 else 'FAIL'}")
    c5 = claim5()
    print(f"  5  prop:ineq2 band equivalence                                       "
          f"{'PASS' if c5 else 'FAIL'}")
    allok = all((c1, c2, c3, c4, c5))
    print(f"\n  overall: {'ALL PASS' if allok else 'FAILURES PRESENT'}")
    print("\n  Coverage is these five, not the whole section: the vertex recursion check, the")
    print("  C_r decomposition, the DPP representation and the pi_max trend are not re-verified.")
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main())
