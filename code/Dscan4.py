"""Dscan4.py -- does (D) degrade with p at b >= 3 as it does at b = 2?

Resolvable commuting families: partition [p] into p/b blocks of size b, a times
(a independent random partitions).  Every such family HAS a parallel-class
partition (a of them, by construction), so the orthogonal-partition hypothesis
holds identically -- isolating the p-dependence.

mu is exact (matching generating polynomial of the incidence bipartite graph),
computed by an array subset-DP over the p-side.
"""
from fractions import Fraction
import sys

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from Dclaim import (boxp, deconv, poly_from_roots, psi0,                       # noqa
                    is_real_rooted_exact, maximag_float)
from Dscan3 import tstar, rr_at                                                # noqa


def mu_from_blocks_fast(blocks, p):
    """m_i = # i-matchings of the incidence bipartite graph, array DP over 2^p."""
    N = 1 << p
    f = np.zeros(N, dtype=object)
    f[0] = 1
    for B in blocks:
        bm = [1 << i for i in B]
        g = f.copy()
        for mask in range(N):
            v = f[mask]
            if v == 0:
                continue
            for bit in bm:
                if not (mask & bit):
                    g[mask | bit] += v
        f = g
    pc = np.zeros(N, dtype=np.int64)
    for mask in range(N):
        pc[mask] = bin(mask).count('1')
    m = [0] * (p + 1)
    for mask in range(N):
        if f[mask]:
            m[pc[mask]] += int(f[mask])
    return [Fraction((-1) ** i * m[i]) for i in range(p + 1)]


def resolvable_family(p, b, a, seed):
    """a random parallel classes: each is a partition of [p] into p/b b-sets."""
    rng = np.random.default_rng(seed)
    blocks = []
    for _ in range(a):
        perm = rng.permutation(p)
        for t in range(p // b):
            blocks.append(tuple(sorted(int(x) for x in perm[t * b:(t + 1) * b])))
    return blocks


def main():
    print("=" * 112)
    print("RESOLVABLE COMMUTING FAMILIES (a random parallel classes) -- p-dependence")
    print("  every family here HAS the orthogonal partition; only p and b vary")
    print("=" * 112)
    print("%-5s %-3s %-3s %-4s %-5s | %-7s %-10s %-9s %-9s" %
          ("p", "b", "a", "q", "seed", "(D)", "#real/p", "t*(p/b)", "t*/b"))
    cases = []
    for b in (2, 3, 4):
        for p in ([6, 8, 10, 12, 14] if b == 2 else
                  ([6, 9, 12, 15] if b == 3 else [8, 12, 16])):
            for a in (3, 4):
                for seed in (1, 2, 3):
                    cases.append((p, b, a, seed))
    for (p, b, a, seed) in cases:
        if p % b or p > 16:
            continue
        blocks = resolvable_family(p, b, a, seed)
        q = len(blocks)
        # biregularity is automatic; check no repeated block collapses degrees
        deg = [0] * p
        for B in blocks:
            for i in B:
                deg[i] += 1
        assert set(deg) == {a}
        mu = mu_from_blocks_fast(blocks, p)
        rho = deconv(mu, psi0(p, b), p)
        assert boxp(psi0(p, b), rho, p) == mu
        rr, nreal, nsq = is_real_rooted_exact(rho)
        ts, sat = tstar(mu, p, b, p // b, tmax=Fraction(3 * b))
        print("  %-5d %-3d %-3d %-4d %-5d | %-7s %2d/%-7d %9.5f %9.4f%s"
              % (p, b, a, q, seed, rr, nreal, p, ts, ts / b,
                 "  (sat)" if sat else ""))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
