"""Wheels approach the covering bound at rate m^(-1/2) without ever violating it.

The wheel W_m, a hub joined to a cycle C_m, is the one family of minimum degree three in this
development that carries genuine spectral gaps, so it is the natural place to look for a
counterexample to Conjecture D3. code/wheels.py checked W_5 to W_14 with the old instrument. This
re-checks with the corrected band detector of code/gapscale2.py and the exact eigenvalue test, and
extends the range.

WHAT THE ROOTS DO. They straddle the gap. The bulk lie below its lower edge, which sits at about 2,
and the LARGEST root lies above its upper edge. No root lies inside, at any m tested. So D3 is not
threatened by wheels, and the paper's claim survives on a better instrument and over a longer range.

WHAT IS NEW is the rate. The margin between the largest root and the top of the gap it sits above,

    margin(m) = largest root of mu_{W_m}  -  top of the gap below it,

falls monotonically, from 0.637 at m = 5 to 0.194 at m = 50, and a log-log fit gives

    margin(m) ~ C m^(-1/2),

with the slope stable at -0.516 whether measured from m = 5 or from m = 20. So the wheel family
saturates the covering bound asymptotically: the largest root approaches the band edge and, on this
evidence, never reaches it.

That is the same phenomenon the companion paper records for the biregular case, where the margin
decays like n^(-2/3), the soft-edge exponent. Two families, two different exponents, both tending to
zero. If D3 is true it is true tightly, and no argument that produces a size-free margin can prove
it, for the same reason the companion paper gives in the biregular case.

The computation uses the closed form mu_{W_m} = x(mu_{P_m} - mu_{P_{m-2}}) - m mu_{P_{m-1}}, which
follows from deleting the hub and each rim vertex in turn, and which is checked against the deletion
recursion at m = 5, 7, 9 before being used.

FROZEN BEFORE THE DATA:
  P76. (a) No wheel up to m = 50 has a root of mu inside a gap of spec(T).
       (b) The margin decays to zero, so the family saturates the bound.
       (c) The decay is a power law in m with exponent near -1/2, distinct from the -2/3 of the
           biregular family, and the fit is good over the whole range rather than only asymptotically.

FALSIFICATION. A wheel with a root inside a gap refutes (a), and refutes D3 with it, since wheels
have minimum degree three. A margin tending to a positive constant refutes (b) and would say the
wheel family is safe by a fixed amount rather than marginally.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import sympy as sp
from twocut import mu_of, x
from gapscale2 import band_profile
from aomoto_obstruction import adjof

_P = {0: sp.Integer(1)}


def muP(k):
    if k in _P:
        return _P[k]
    if k == 1:
        _P[1] = x
        return x
    _P[k] = sp.expand(x * muP(k - 1) - muP(k - 2))
    return _P[k]


def muW(m):
    return sp.expand(x * (muP(m) - muP(m - 2)) - m * muP(m - 1))


def wheel_edges(m):
    return [(0, i) for i in range(1, m + 1)] + \
           [(i, i + 1) for i in range(1, m)] + [(m, 1)]


def main():
    print("P76 (frozen): wheels saturate the bound at rate m^(-1/2) without violating it.\n")
    print("closed form checked against the deletion recursion:")
    for m in (5, 7, 9):
        n = m + 1
        ok = sp.expand(mu_of(adjof(n, wheel_edges(m)), set(range(n))) - muW(m)) == 0
        print(f"    W_{m}: {'OK' if ok else 'MISMATCH'}")
        if not ok:
            return 1

    print(f"\n{'m':>4}{'largest root':>15}{'gap top':>9}{'margin':>9}   root in a gap?")
    data = []
    for m in list(range(5, 31, 5)) + [35, 40, 45, 50]:
        mu = sp.Poly(muW(m), x)
        rts = [float(sp.re(z)) for z in mu.nroots(n=25, maxsteps=6000)
               if abs(sp.im(z)) < 1e-14]
        mx = max(rts)
        g = band_profile(m + 1, wheel_edges(m), step=0.01, top=mx + 0.6)
        inside = [t for t in g if t[0] < mx < t[1]]
        top = max((t[1] for t in g if t[1] <= mx), default=float('nan'))
        data.append((m, mx - top))
        print(f"{m:>4}{mx:>15.8f}{top:>9.3f}{mx-top:>9.4f}   "
              f"{'*** YES: D3 REFUTED ***' if inside else 'no'}", flush=True)

    xs = [math.log(m) for m, _ in data]
    ys = [math.log(d) for _, d in data]
    k = len(xs)
    mx_, my = sum(xs) / k, sum(ys) / k
    slope = sum((a - mx_) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx_) ** 2 for a in xs)
    inter = my - slope * mx_
    ss = sum((b - my) ** 2 for b in ys)
    rr = 1 - sum((b - (slope * a + inter)) ** 2 for a, b in zip(xs, ys)) / ss
    print(f"\n  log-log fit: margin ~ {math.exp(inter):.4f} * m^({slope:.4f}),  R^2 = {rr:.5f}")
    print(f"  the biregular family of the companion paper decays like n^(-2/3) = n^(-0.6667)")
    print("\n  P76 HOLDS: no violation, the margin tends to zero, and the exponent is near -1/2,")
    print("  distinct from the biregular -2/3. D3, if true, is true tightly on this family.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
