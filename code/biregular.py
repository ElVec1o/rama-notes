"""Falsification attempt on the last surviving hypothesis: the biregular case.

After Hall's counterexample and the 31-vertex subcubic one, degree conditions are dead:
minimum degree two and bounded maximum degree both fail. What survives is biregularity, which
is Problem 1 of Song, Fan and Miao and is Conjecture 10 restricted to (a,b)-biregular
bipartite graphs.

WHY IT SURVIVES, STRUCTURALLY. Both known mechanisms are blocked. Hall's needs a wide degree
spread; the subcubic one needs a tree skeleton, and a tree has leaves, whereas a biregular
graph with both degrees at least two has none. So neither construction can be made biregular,
which is a reason to test the statement seriously rather than assume it will fall.

THE STATEMENT. For (a,b)-biregular bipartite G the universal cover is the (a,b)-biregular
tree, whose spectrum is

    +- [ |sqrt(a-1) - sqrt(b-1)| , sqrt(a-1) + sqrt(b-1) ]   together with 0,

so the conjecture says mu_G has no root mu with 0 < |mu| < |sqrt(a-1) - sqrt(b-1)|. Zero
itself is excluded: it is a root of mu_G of multiplicity at least ||A| - |B||.

METHOD. For a bipartite graph the number of k-matchings is computed exactly by a subset DP
over the smaller side,

    dp_{i+1}[S] = dp_i[S] + sum_{b in S, b ~ a_i} dp_i[S - b],

so mu_G is exact in integer arithmetic without enumerating matchings. Roots are then located
and compared with the threshold. Counts are held in int64 and checked for overflow.

Graphs are drawn from a configuration model on the two sides, rejecting multi-edges and
disconnected results, which samples biregular bipartite graphs without bias toward any
particular structure.

Rule 8: instrumented, backgrounded, checkpointed.
"""

import sys
import os
import math
import time
import random
import numpy as np
import sympy as sp

CKPT = 'private/biregular_ckpt.txt'
x = sp.Symbol('x')


def random_biregular(a, b, k, rng, tries=400):
    """(a,b)-biregular bipartite: |A| = b*k on the a-side, |B| = a*k on the b-side."""
    nA, nB = b * k, a * k
    for _ in range(tries):
        stubsA = [i for i in range(nA) for _ in range(a)]
        stubsB = [j for j in range(nB) for _ in range(b)]
        rng.shuffle(stubsB)
        e = list(zip(stubsA, stubsB))
        if len(set(e)) != len(e):
            continue
        adjA = [[] for _ in range(nA)]
        for (i, j) in e:
            adjA[i].append(j)
        # connectivity on the bipartite graph
        seen = {('A', 0)}
        st = [('A', 0)]
        nbrB = [[] for _ in range(nB)]
        for (i, j) in e:
            nbrB[j].append(i)
        while st:
            side, v = st.pop()
            nb = [('B', t) for t in adjA[v]] if side == 'A' else [('A', t) for t in nbrB[v]]
            for w in nb:
                if w not in seen:
                    seen.add(w); st.append(w)
        if len(seen) == nA + nB:
            return nA, nB, adjA
    return None


def matching_counts(nA, nB, adjA):
    """Exact k-matching counts by subset DP over the B side (int64, overflow checked)."""
    size = 1 << nB
    dp = np.zeros(size, dtype=np.int64)
    dp[0] = 1
    idx = np.arange(size, dtype=np.int64)
    for i in range(nA):
        new = dp.copy()
        for bvert in adjA[i]:
            bit = np.int64(1) << np.int64(bvert)
            has = (idx & bit) != 0
            new[has] += dp[idx[has] ^ bit]
        if np.any(new < 0):
            raise OverflowError("int64 overflow in matching DP")
        dp = new
    pc = np.zeros(size, dtype=np.int64)
    for j in range(nB):
        pc += (idx >> np.int64(j)) & np.int64(1)
    m = np.zeros(nB + 1, dtype=object)
    for kk in range(nB + 1):
        m[kk] = int(dp[pc == kk].sum())
    return m


def main():
    rng = random.Random(20260809)
    combos = [(3, 4), (3, 5), (4, 5), (3, 6), (4, 6), (5, 6), (3, 7), (4, 7)]
    print(f"{'a':>3}{'b':>3}{'k':>3}{'nA':>4}{'nB':>4}{'n':>4}{'threshold':>11}"
          f"{'min |root|>0':>14}{'verdict':>10}", flush=True)
    worst = {}
    tested = 0
    t0 = time.time()
    for (a, b) in combos:
        thr = abs(math.sqrt(a - 1) - math.sqrt(b - 1))
        for k in range(1, 6):
            nA, nB = b * k, a * k
            if nB > 15 or nA + nB > 40:
                continue
            for trial in range(12):
                g = random_biregular(a, b, k, rng)
                if g is None:
                    continue
                nA_, nB_, adjA = g
                try:
                    m = matching_counts(nA_, nB_, adjA)
                except OverflowError:
                    print(f"{a:>3}{b:>3}{k:>3}  overflow, skipped", flush=True)
                    continue
                n = nA_ + nB_
                poly = sum((-1) ** kk * int(m[kk]) * x ** (n - 2 * kk)
                           for kk in range(len(m)))
                co = sp.Poly(poly, x).all_coeffs()
                while co and co[-1] == 0:
                    co.pop()
                if len(co) < 2:
                    continue
                rts = [abs(complex(r)) for r in sp.Poly(co, x).nroots(n=20, maxsteps=500)
                       if abs(sp.im(r)) < 1e-9 and abs(sp.re(r)) > 1e-9]
                tested += 1
                if not rts:
                    continue
                mn = min(rts)
                key = (a, b)
                if key not in worst or mn < worst[key][0]:
                    worst[key] = (mn, k, n)
                bad = mn < thr - 1e-9
                if bad or trial == 0:
                    print(f"{a:>3}{b:>3}{k:>3}{nA_:>4}{nB_:>4}{n:>4}{thr:>11.5f}"
                          f"{mn:>14.6f}{('VIOLATION' if bad else 'ok'):>10}", flush=True)
                if bad:
                    print(f"    counterexample: a={a} b={b} k={k} adjA={adjA}", flush=True)
    print(f"\n{tested} biregular graphs tested in {time.time()-t0:.0f}s")
    print(f"\n{'a':>3}{'b':>3}{'threshold':>11}{'smallest nonzero |root| seen':>30}"
          f"{'ratio':>9}")
    for (a, b), (mn, k, n) in sorted(worst.items()):
        thr = abs(math.sqrt(a - 1) - math.sqrt(b - 1))
        print(f"{a:>3}{b:>3}{thr:>11.5f}{mn:>30.6f}{mn/thr:>9.3f}")
    print("\nratio below 1 would be a violation of Song-Fan-Miao Problem 1.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
