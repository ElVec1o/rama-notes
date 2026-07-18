#!/usr/bin/env python3
"""Paper 3: extend perm[gcd] to n = 27; growth-rate analysis."""
import time, math
from math import gcd

KNOWN23 = 1226734830877410684373175894016  # a(23) from July 2 run

def gcd_permanent_ryser_gray(n):
    M = [[gcd(i + 1, j + 1) for j in range(n)] for i in range(n)]
    cols = [[M[i][j] for i in range(n)] for j in range(n)]
    sums = [0] * n
    total = 0
    prev = 0
    for s in range(1, 1 << n):
        g = s ^ (s >> 1)
        diff = g ^ prev
        j = diff.bit_length() - 1
        cj = cols[j]
        if g & diff:
            for i in range(n):
                sums[i] += cj[i]
        else:
            for i in range(n):
                sums[i] -= cj[i]
        prev = g
        bits = bin(g).count('1')
        prod = 1
        for v in sums:
            prod *= v
        total += prod if ((n - bits) % 2 == 0) else -prod
    return total

def factorize(v):
    fs, d = [], 2
    while d * d <= v and d < 10_000_000:
        while v % d == 0:
            fs.append(d); v //= d
        d += 1
    if v > 1:
        fs.append(v)   # may be composite if > 1e14; fine for display
    return fs

vals = {}
a23 = gcd_permanent_ryser_gray(23)
assert a23 == KNOWN23, "regression vs July 2 value!"
vals[23] = a23
print(f"a(23) regression check OK", flush=True)

for n in (24, 25, 26, 27):
    t0 = time.time()
    a = gcd_permanent_ryser_gray(n)
    vals[n] = a
    v2 = 0; tmp = a
    while tmp % 2 == 0:
        v2 += 1; tmp //= 2
    print(f"a({n}) = {a}", flush=True)
    print(f"   v2={v2}  mod24={a%24}  mod3={a%3}  [{time.time()-t0:.0f}s]",
          flush=True)

# growth analysis using all known values
ALL = {1:1,2:3,3:14,4:112,5:872,6:14372,7:154480,8:3098480,9:59710816,
       10:1688186176,11:27925409152,12:1327833590272,13:25675495200768,
       14:1017195720916224,15:47444016840290304,
       16:2267031138313024512,17:56480432945454004224,
       18:4051971981329937580032,19:112180041921327922569216,
       20:9250427364885586859163648,21:604870570906353696547307520,
       22:37003949025135478872990547968,23:1226734830877410684373175894016}
ALL.update(vals)
print("\ngrowth: n, a(n)/n!, (a(n)/n!)^(1/n), ln a(n)/(n ln n)")
for n in sorted(ALL):
    if n < 2: continue
    ratio = ALL[n] / math.factorial(n)
    print(f"  {n:2d}  {ratio:.4e}  {ratio ** (1/n):.4f}  "
          f"{math.log(ALL[n]) / (n * math.log(n)):.4f}")
