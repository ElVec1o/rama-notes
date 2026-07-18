#!/usr/bin/env python3
"""Paper 1 enhancement: extend S1, S0, S-1 to n = 30000."""
import sys, time

N = 200000

t0 = time.time()
# pentagonal recurrence, iterative
p = [0] * (N + 1)
p[0] = 1
S1, S0, Sm1 = [], [], []
res_record = []  # (n, p(n) mod n)

for n in range(1, N + 1):
    total = 0
    k = 1
    while True:
        g1 = k * (3 * k - 1) // 2
        if g1 > n:
            break
        sign = 1 if (k % 2 == 1) else -1
        total += sign * p[n - g1]
        g2 = k * (3 * k + 1) // 2
        if g2 <= n:
            total += sign * p[n - g2]
        k += 1
    p[n] = total
    if n >= 2:
        r = p[n] % n
        if r == 1:
            S1.append(n)
        elif r == 0:
            S0.append(n)
        elif r == n - 1:
            Sm1.append(n)
    if n % 5000 == 0:
        print(f"... n={n}  elapsed={time.time()-t0:.1f}s  |S1|={len(S1)} |S0|={len(S0)} |S-1|={len(Sm1)}", flush=True)

print(f"\nDone in {time.time()-t0:.1f}s")
# sanity: known values
assert [x for x in S1 if x <= 1000] == [4, 7, 11, 54, 55, 115, 146, 157, 234, 239, 951], "S1 mismatch vs paper!"
assert [x for x in S0 if x <= 400] == [2, 3, 124, 158, 342], "S0 mismatch vs paper!"
assert [x for x in Sm1 if x <= 500] == [6, 156, 305, 484], "S-1 mismatch vs paper!"
print("Sanity checks vs published terms: OK\n")

import math
print(f"S1  (n | p(n)-1), {len(S1)} terms up to {N}:")
print(S1)
print(f"expected count ~ ln({N}) = {math.log(N):.2f}")
print()
print(f"S0  (n | p(n)), {len(S0)} terms up to {N}:")
print(S0)
print()
print(f"S-1 (p(n) == -1 mod n), {len(Sm1)} terms up to {N}:")
print(Sm1)
print()
# consecutive pairs in S1
pairs = [(a, b) for a, b in zip(S1, S1[1:]) if b == a + 1]
print(f"Consecutive pairs in S1: {pairs}")
allmem = sorted(set(S1) | set(S0) | set(Sm1))
pairs_all = [(a, b) for a, b in zip(allmem, allmem[1:]) if b == a + 1]
print(f"Consecutive pairs in S1 u S0 u S-1: {pairs_all}")
# densities in dyadic windows to test ln growth
print("\nS1 counts by window [2^k, 2^(k+1)):")
for k in range(2, 15):
    lo, hi = 2 ** k, 2 ** (k + 1)
    c = sum(1 for x in S1 if lo <= x < hi)
    print(f"  [{lo},{hi}): {c}   (random prediction ~ ln2 = 0.69)")
