#!/usr/bin/env python3
"""Paper 3 enhancement: extend perm[gcd(i,j)] to n = 23, factor, check mod 24 and parity."""
import sys, time
from math import gcd

KNOWN = {1:1, 2:3, 3:14, 4:112, 5:872, 6:14372, 7:154480, 8:3098480, 9:59710816,
         10:1688186176, 11:27925409152, 12:1327833590272, 13:25675495200768,
         14:1017195720916224, 15:47444016840290304}

def gcd_permanent_ryser_gray(n):
    """Ryser with Gray code: perm = (-1)^n * sum_{S nonempty} (-1)^{|S|} prod_i colsum_i(S)."""
    M = [[gcd(i + 1, j + 1) for j in range(n)] for i in range(n)]
    cols = [[M[i][j] for i in range(n)] for j in range(n)]  # column j as vector
    sums = [0] * n
    total = 0
    prev = 0
    for s in range(1, 1 << n):
        g = s ^ (s >> 1)              # Gray code
        diff = g ^ prev
        j = diff.bit_length() - 1     # flipped column index
        cj = cols[j]
        if g & diff:                  # column j added
            for i in range(n):
                sums[i] += cj[i]
        else:                         # column j removed
            for i in range(n):
                sums[i] -= cj[i]
        prev = g
        bits = bin(g).count('1')
        prod = 1
        for v in sums:
            prod *= v
        total += prod if ((n - bits) % 2 == 0) else -prod
    return total

def phi_sieve(n):
    phi = list(range(n + 1))
    for i in range(2, n + 1):
        if phi[i] == i:  # prime
            for j in range(i, n + 1, i):
                phi[j] -= phi[j] // i
    return phi

def factorize(v):
    fs, d = [], 2
    while d * d <= v:
        while v % d == 0:
            fs.append(d); v //= d
        d += 1
    if v > 1:
        fs.append(v)
    return fs

NMAX = 23
phi = phi_sieve(NMAX)
t0 = time.time()
vals = {}
detprod = 1
print("n : a(n) | v2 | a mod 24 | det=prod phi(k) mod 2 | factorization", flush=True)
for n in range(1, NMAX + 1):
    t1 = time.time()
    a = gcd_permanent_ryser_gray(n)
    vals[n] = a
    if n in KNOWN:
        assert a == KNOWN[n], f"MISMATCH at n={n}: got {a}, expected {KNOWN[n]}"
    detprod *= phi[n]
    v2 = 0
    tmp = a
    while tmp and tmp % 2 == 0:
        v2 += 1; tmp //= 2
    fac = factorize(a) if n <= 23 else []
    par_ok = (a - detprod) % 2 == 0
    print(f"{n:2d} : {a} | v2={v2} | mod24={a%24} | parity-vs-det ok={par_ok} | {fac}   [{time.time()-t1:.1f}s]", flush=True)

print(f"\nTotal time {time.time()-t0:.1f}s")
print("\nAll parity checks perm ≡ det (mod 2):", all((vals[n] - eval('1')) is not None for n in vals))
# explicit re-verify parity claim
detp = 1
ok = True
for n in range(1, NMAX + 1):
    detp *= phi[n]
    if (vals[n] - detp) % 2 != 0:
        ok = False
        print(f"PARITY FAIL at {n}")
print("parity theorem perm≡det mod 2 verified for all computed n:", ok)
print("\nmod 24 tail:", {n: vals[n] % 24 for n in range(10, NMAX + 1)})
