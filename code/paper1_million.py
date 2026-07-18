#!/usr/bin/env python3
"""Paper 1: extend to N = 10^6 with residue-class controls.

Key question: do the ±1 droughts persist, and are residues ±1 special
compared to control residues (0, ±2, ±3, 5)?
"""
import time, math

N = 1_000_000
t0 = time.time()

p = [0] * (N + 1)
p[0] = 1

# residue classes tracked: keys are labels
hits = {k: [] for k in ["0", "+1", "-1", "+2", "-2", "+3", "-3", "+5"]}
# normalized residue histogram (20 bins) to test uniformity of p(n) mod n
BINS = 20
hist = [0] * BINS

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
        r = total % n
        hist[(r * BINS) // n] += 1
        if r == 0:
            hits["0"].append(n)
        elif r == 1:
            hits["+1"].append(n)
        elif r == n - 1:
            hits["-1"].append(n)
        elif r == 2:
            hits["+2"].append(n)
        elif r == n - 2:
            hits["-2"].append(n)
        elif r == 3:
            hits["+3"].append(n)
        elif r == n - 3:
            hits["-3"].append(n)
        elif r == 5:
            hits["+5"].append(n)
    if n % 100000 == 0:
        print(f"... n={n}  t={time.time()-t0:.0f}s  " +
              " ".join(f"{k}:{len(v)}" for k, v in hits.items()), flush=True)

print(f"\nDone in {time.time()-t0:.0f}s.  ln(N) = {math.log(N):.2f}\n")
# sanity vs earlier runs
assert [x for x in hits["+1"] if x <= 1000] == [4, 7, 11, 54, 55, 115, 146, 157, 234, 239, 951]
assert [x for x in hits["0"] if x <= 20000] == [2, 3, 124, 158, 342, 693, 1896, 3853, 4434, 5273, 8640, 14850, 17928]
assert [x for x in hits["-1"] if x <= 2000] == [6, 156, 305, 484, 1219]
print("sanity vs n<=200000 runs: OK\n")

for k, v in hits.items():
    tail = v[-8:] if len(v) > 8 else v
    print(f"residue {k:3s}: {len(v):3d} terms; last = {v[-1] if v else None}; tail = {tail}")

print(f"\nrandom-model expectation per class ~ ln N = {math.log(N):.2f}")
print("\nnormalized residue histogram (20 bins, expect ~uniform "
      f"{(N-1)/BINS:.0f} per bin):")
for b in range(BINS):
    print(f"  [{b/BINS:.2f},{(b+1)/BINS:.2f}): {hist[b]}")

# drought significance for +1 and -1
for lab, start in (("+1", 951), ("-1", 1219)):
    terms_after = [x for x in hits[lab] if x > start]
    lam = math.log(N / start)
    print(f"\nresidue {lab}: terms in ({start}, {N}]: {len(terms_after)} "
          f"(expected {lam:.2f}; P(0 terms) = e^-{lam:.2f} = {math.exp(-lam):.4f})")
    if terms_after:
        print(f"  -> DROUGHT BROKEN at {terms_after[:5]}")
