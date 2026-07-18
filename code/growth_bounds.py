#!/usr/bin/env python3
"""Paper 3, Proposition 3: rigorous lower bound on (a(n)/n!)^{1/n}.
Lower (Jensen): c >= e^L, L = sum_p logp/(p^2-1) = 0.56996..., e^L = 1.76819.
Upper (row-sum product) DIVERGES like loglog n (Mertens) -> finiteness of c OPEN."""
import math
from math import gcd
from sympy import primerange

P = list(primerange(2, 500000))
L = sum(math.log(p)/(p*p-1) for p in P)
print(f"L = sum_p logp/(p^2-1) = {L:.6f}   =>   liminf (a(n)/n!)^(1/n) >= e^L = {math.exp(L):.5f}")

# show the row-sum exponent grows (diverges) with n, so it can't bound c by a constant
KNOWN = {15:47444016840290304, 20:9250427364885586859163648,
         27:42950237145098618016020059492435623936}
for n in sorted(KNOWN):
    Slog = sum(math.log(gcd(i,j)) for i in range(1,n+1) for j in range(1,n+1))
    low = math.exp(Slog/n/n)
    R = [sum(gcd(i,j) for j in range(1,n+1)) for i in range(1,n+1)]
    up = math.exp((sum(math.log(r) for r in R) - sum(math.log(i) for i in range(1,n+1)))/n)
    data = (KNOWN[n]/math.factorial(n))**(1/n)
    print(f"  n={n:2d}: lower={low:.4f} <= data={data:.4f} <= rowsum-upper={up:.4f} (upper rising, ~loglog)")
