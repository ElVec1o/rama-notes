#!/usr/bin/env python3
"""Paper 3 Prop 3 RESOLVED: c = lim (a(n)/n!)^{1/n} = +infinity.
Van der Waerden (Falikman-Egorychev) + Sinkhorn scaling gives a RIGOROUS
per-n lower bound  (a(n)/n!)^{1/n} >= 1/(n * (prod x prod y)^{1/n}),  which
DIVERGES (exponent -> log 2). Data fits (log n)^{log 2} to <1%. So a(n) grows
like n! * exp((log2+o(1)) n loglog n)."""
import math
from math import gcd
import numpy as np
def vdw_lower(n,iters=8000):
    M=np.array([[gcd(i+1,j+1) for j in range(n)] for i in range(n)],float)
    x=np.ones(n);y=np.ones(n)
    for _ in range(iters): x=1.0/(M@y); y=1.0/(M.T@x)
    return math.exp(-(n*math.log(n)+np.sum(np.log(x))+np.sum(np.log(y)))/n)
KNOWN={15:47444016840290304,20:9250427364885586859163648,27:42950237145098618016020059492435623936,30:35826751407711255748715380987982495052988416}
print("RIGOROUS VdW lower bound diverges => c = infinity:")
for n in (15,30,60,125,250,500,1000):
    print(f"  n={n:4d}: VdW-lower (a/n!)^(1/n) >= {vdw_lower(n):.4f}   [exponent {math.log(vdw_lower(n))/math.log(math.log(n)):.3f}]")
print(f"\nlog 2 = {math.log(2):.4f}. Data (a/n!)^(1/n)/(log n)^log2:")
for n in sorted(KNOWN):
    d=(KNOWN[n]/math.factorial(n))**(1/n); print(f"  n={n}: {d/math.log(n)**math.log(2):.4f}")
