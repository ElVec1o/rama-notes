#!/usr/bin/env python3
"""Exact formula for E[#PM of random d-cover of K4], derived by linearity:
E = (1/d!^2) * sum_{a+b+c=d} [ (d-a)!(d-b)!(d-c)! / (a!b!c!) ]^2
(opposite K4 edges carry equal flow; a,b,c = flows on the 3 perfect matchings).
Verify against the exact Psi_r constants, then compute growth rate."""
from fractions import Fraction
from math import factorial as F, log

def EPM(d):
    tot = 0
    for a in range(d + 1):
        for b in range(d + 1 - a):
            c = d - a - b
            t = F(d - a) * F(d - b) * F(d - c) // (F(a) * F(b) * F(c))
            tot += t * t
    return Fraction(tot, F(d) ** 2)

KNOWN = {1: Fraction(3), 2: Fraction(6), 3: Fraction(97, 9),
         4: Fraction(75, 4), 5: Fraction(162, 5)}
for d, v in KNOWN.items():
    got = EPM(d)
    print(f"d={d}: formula={got} known={v} {'MATCH' if got == v else 'MISMATCH'}")

print("\ngrowth: d, E_d (float), ratio E_d/E_{d-1}")
prev = None
import sys
for d in list(range(1, 21)) + [30, 40, 60, 80, 120, 160, 200, 260, 320]:
    v = EPM(d)
    fv = v.numerator / v.denominator if v.denominator < 10**300 else float(v)
    r = ""
    if prev is not None and prev[0] == d - 1:
        r = f"{float(v / prev[1]):.6f}"
    print(f"  d={d:3d}  E={float(v):.6e}  ratio={r}")
    prev = (d, v)
print(f"\n16/9   = {16/9:.6f}")
print(f"sqrt3  = {3**0.5:.6f}")
# rate from largest two consecutive: recompute 319,320
a, b = EPM(319), EPM(320)
print(f"ratio at d=320: {float(b/a):.8f}")
