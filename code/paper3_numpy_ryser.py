#!/usr/bin/env python3
"""gcd permanent for n = 28, 29, 30 via block-vectorized MODULAR Ryser + CRT.

perm = (-1)^n * sum_{S subseteq [n]} (-1)^{|S|} prod_i (sum_{j in S} M[i][j])
Split S = (hi, lo): lo = low B bits. colsums(S) = base(hi) + delta(lo),
delta precomputed as a 2^B x n array. All arithmetic mod several primes,
CRT-reconstructed. Validated against known exact values for n = 15, 20, 23.
"""
import time, math
from math import gcd
import numpy as np

PRIMES = [1073741789, 1073741783, 1073741741, 1073741723,
          1073741719, 1073741717, 1073741689, 1073741671]  # < 2^30

KNOWN = {15: 47444016840290304,
         20: 9250427364885586859163648,
         23: 1226734830877410684373175894016}

def perm_mod(n, p, B=18):
    M = np.array([[gcd(i + 1, j + 1) for j in range(n)] for i in range(n)],
                 dtype=np.int64)
    B = min(B, n)
    nhi = n - B
    lo_count = 1 << B
    # delta[lo, i] = sum_{j < B, bit j of lo} M[i][j]  (mod p not needed yet, small)
    bits = ((np.arange(lo_count)[:, None] >> np.arange(B)[None, :]) & 1)  # 2^B x B
    delta = bits @ M[:, :B].T          # 2^B x n, values <= 3n*B small
    pop_lo = bits.sum(axis=1)          # popcount of lo
    sign_lo = np.where((pop_lo & 1) == 0, 1, -1).astype(np.int64)
    total = 0
    for hi in range(1 << nhi):
        base = np.zeros(n, dtype=np.int64)
        h = hi
        j = B
        pop_hi = 0
        while h:
            if h & 1:
                base += M[:, j]
                pop_hi += 1
            h >>= 1
            j += 1
        sums = (delta + base[None, :]) % p          # 2^B x n
        prod = np.ones(lo_count, dtype=np.int64)
        for i in range(n):
            prod = (prod * sums[:, i]) % p
        s = np.where(pop_hi & 1, -sign_lo, sign_lo)  # (-1)^{|S|}
        total = (total + int((prod * s % p).sum() % p)) % p
    if n & 1:
        total = (-total) % p
    return total

def crt(residues, moduli):
    x, m = 0, 1
    for r, p in zip(residues, moduli):
        # solve x' == x (mod m), x' == r (mod p)
        inv = pow(m % p, -1, p)
        x = x + m * ((r - x) % p * inv % p)
        m *= p
    return x % m, m

# validation
for n in (15, 20, 23):
    t0 = time.time()
    res = [perm_mod(n, p) for p in PRIMES[:4]]
    v, m = crt(res, PRIMES[:4])
    assert v == KNOWN[n] % m and KNOWN[n] < m, f"VALIDATION FAIL n={n}"
    print(f"validated n={n} [{time.time()-t0:.0f}s]", flush=True)
print("validation OK\n", flush=True)

for n in (28, 29, 30):
    t0 = time.time()
    # quick mod-3 answer first
    m3 = perm_mod(n, 3)
    print(f"n={n}: a(n) mod 3 = {m3}   [{time.time()-t0:.0f}s]", flush=True)
    res = [perm_mod(n, p) for p in PRIMES]
    v, m = crt(res, PRIMES)
    # sanity: v must be < m by good margin; growth trend says a(30) ~ 1e42, m ~ 1e72
    v2 = 0
    t = v
    while t % 2 == 0:
        v2 += 1; t //= 2
    print(f"a({n}) = {v}", flush=True)
    print(f"   v2={v2}  mod24={v%24}  mod3={v%3}  [{time.time()-t0:.0f}s]",
          flush=True)
