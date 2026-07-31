"""The SCALAR family  A_k = (b/p) I_p,  k = 1..q,  q = pa/b.

It satisfies EVERY hypothesis of the MSS barrier theorem (Interlacing Families
II, Thm 5.1):   A_k PSD,  sum_k A_k = a I,  tr A_k = b.
It is NOT rank <= b (its rank is p) and not idempotent.

    mu[A](y) = sum_m (-1)^m C(q,m) p!/(p-m)! (b/p)^m y^{p-m},

a Laguerre polynomial; as p -> infinity with (a,b) fixed its root support
converges to the Marchenko-Pastur band [(sqrt a - sqrt b)^2,(sqrt a + sqrt b)^2]
-- which is exactly the MSS barrier bound.  So the barrier bound is SHARP on
its own hypotheses, and the tree band [(s-t)^2,(s+t)^2] is strictly stronger
at BOTH edges.  Computed exactly (Fraction coefficients, mpmath roots).
"""
import sys
from fractions import Fraction
from math import comb
import mpmath as mp


def scalar_mu(p, a, b):
    """exact coefficient list c[0..p], mu(y) = sum_m c[m] y^{p-m}."""
    q = p * a // b
    assert q * b == p * a
    c = []
    for m in range(p + 1):
        if m > q:
            c.append(Fraction(0))
            continue
        fall = 1
        for i in range(m):
            fall *= (p - i)
        c.append(Fraction((-1) ** m) * comb(q, m) * fall * Fraction(b, p) ** m)
    return c


def roots_hi(c, prec=200):
    mp.mp.dps = prec
    poly = [mp.mpf(x.numerator) / mp.mpf(x.denominator) for x in c]
    r = mp.polyroots(poly, maxsteps=400, extraprec=400)
    return sorted([mp.re(x) for x in r])


if __name__ == '__main__':
    for (a, b) in [(3, 2), (4, 2), (4, 3), (7, 2)]:
        s, t = mp.sqrt(a - 1), mp.sqrt(b - 1)
        lo, hi = (s - t) ** 2, (s + t) ** 2
        mlo, mhi = (mp.sqrt(a) - mp.sqrt(b)) ** 2, (mp.sqrt(a) + mp.sqrt(b)) ** 2
        print("=" * 78)
        print(f"(a,b)=({a},{b})  tree band [{float(lo):.6f},{float(hi):.6f}]   "
              f"MP band [{float(mlo):.6f},{float(mhi):.6f}]")
        for p in [4, 8, 16, 32, 64, 128, 256]:
            if (p * a) % b:
                continue
            c = scalar_mu(p, a, b)
            r = roots_hi(c)
            rmin, rmax = float(r[0]), float(r[-1])
            f1 = 'LOWER-EDGE VIOLATION' if rmin < float(lo) - 1e-12 else ''
            f2 = 'UPPER-EDGE VIOLATION' if rmax > float(hi) + 1e-12 else ''
            print(f"   p={p:4d} q={p*a//b:5d}: r_min {rmin:.8f} r_max {rmax:.8f}"
                  f"   {f1} {f2}")
            sys.stdout.flush()
