"""Dscan.py -- WHEN is  rho = mu deconv psi_0  real-rooted?

Claim (D) is FALSE (Q_3 at p=8, Petersen at p=10, both exact/Sturm-certified in
Dclaim.py).  This file maps the true boundary.

Everything commuting is EXACT (Fractions + Sturm).  mu for a commuting family
P_k = diag(1_{B_k}) is the matching generating polynomial of the incidence
bipartite graph,
    mu(x) = sum_i (-1)^i m_i x^{p-i},   m_i = # i-matchings,
computed here by subset DP over the p-side (O(q 2^p)).  Cross-checked in
Dclaim.py against (i) the rank-one randomisation and (ii) the multilinear
definition of the MSS mixed characteristic polynomial.
"""
from fractions import Fraction
from itertools import combinations, product
import sys

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from Dclaim import (boxp, boxp_pow, deconv, poly_from_roots, psi0,            # noqa
                    is_real_rooted_exact, maximag_float, sturm_real_root_count)


# ----------------------------------------------------- exact mu, commuting
def mu_from_blocks(blocks, p):
    """mu = sum_i (-1)^i m_i x^{p-i}, m_i = # i-matchings of the incidence
    bipartite graph (p-side = ground set, q-side = blocks).  Subset DP."""
    f = {0: 1}
    for blk in blocks:
        nf = dict(f)
        for mask, v in f.items():
            for i in blk:
                if not (mask >> i) & 1:
                    nf[mask | (1 << i)] = nf.get(mask | (1 << i), 0) + v
        f = nf
    m = [0] * (p + 1)
    for mask, v in f.items():
        m[bin(mask).count('1')] += v
    return [Fraction((-1) ** i * m[i]) for i in range(p + 1)]


def check_biregular(blocks, p, a, b):
    if any(len(set(B)) != b for B in blocks):
        return False
    deg = [0] * p
    for B in blocks:
        for i in B:
            deg[i] += 1
    return set(deg) == {a} and len(blocks) * b == p * a


# ------------------------------------------------------------- graph zoo
def edges_to_blocks(E):
    return [tuple(sorted(e)) for e in E]


def cycle_prism(n):
    """C_n x K_2 : cubic, 2n vertices, 3n edges."""
    E = [(i, (i + 1) % n) for i in range(n)]
    E += [(n + i, n + (i + 1) % n) for i in range(n)]
    E += [(i, n + i) for i in range(n)]
    return E, 2 * n


def moebius_kantor(n):
    """Moebius-Kantor / generalized Petersen GP(n,k)."""
    def gp(n, k):
        E = [(i, (i + 1) % n) for i in range(n)]
        E += [(i, n + i) for i in range(n)]
        E += [(n + i, n + (i + k) % n) for i in range(n)]
        return E, 2 * n
    return gp


def moebius_ladder(n):
    """M_n: cycle C_{2n} plus the n main diagonals -- cubic on 2n vertices."""
    N = 2 * n
    E = [(i, (i + 1) % N) for i in range(N)]
    E += [(i, i + n) for i in range(n)]
    return E, N


def complete_bipartite(m):
    return [(i, m + j) for i in range(m) for j in range(m)], 2 * m


def complete_graph(n):
    return list(combinations(range(n), 2)), n


def hypercube(d):
    V = list(product((0, 1), repeat=d))
    idx = {v: i for i, v in enumerate(V)}
    E = []
    for v in V:
        for c in range(d):
            w = list(v); w[c] ^= 1; w = tuple(w)
            if idx[v] < idx[w]:
                E.append((idx[v], idx[w]))
    return E, len(V)


def petersen():
    E = [(i, (i + 1) % 5) for i in range(5)]
    E += [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    E += [(i, 5 + i) for i in range(5)]
    return E, 10


def gp(n, k):
    E = [(i, (i + 1) % n) for i in range(n)]
    E += [(i, n + i) for i in range(n)]
    E += [(n + i, n + (i + k) % n) for i in range(n)]
    return E, 2 * n


def circulant(n, conn):
    E = set()
    for i in range(n):
        for c in conn:
            E.add(tuple(sorted((i, (i + c) % n))))
    return sorted(E), n


# ------------------------------------------------------ parallel classes
def has_parallel_class(blocks, p, b):
    """Is there a subset G of the blocks partitioning [p]?  Exact cover."""
    if p % b:
        return False
    masks = sorted({sum(1 << i for i in B) for B in blocks})
    full = (1 << p) - 1
    seen = set()

    def rec(cur):
        if cur == full:
            return True
        if cur in seen:
            return False
        seen.add(cur)
        low = (~cur & full) & (-(~cur & full))         # lowest uncovered bit
        for mk in masks:
            if (mk & low) and not (mk & cur):
                if rec(cur | mk):
                    return True
        return False
    return rec(0)


def count_parallel_classes(blocks, p, b):
    if p % b:
        return 0
    masks = [sum(1 << i for i in B) for B in blocks]
    full = (1 << p) - 1
    out = []

    def rec(cur, start, chosen):
        if cur == full:
            out.append(tuple(chosen))
            return
        low = (~cur & full) & (-(~cur & full))
        for j in range(len(masks)):
            if (masks[j] & low) and not (masks[j] & cur):
                rec(cur | masks[j], j + 1, chosen + [j])
    rec(0, 0, [])
    return len(out)


def has_resolution(blocks, p, a, b):
    """Partition of ALL q blocks into a parallel classes (a resolution)."""
    if p % b:
        return False
    masks = [sum(1 << i for i in B) for B in blocks]
    q = len(masks)
    full = (1 << p) - 1
    # classes: enumerate all parallel classes as index sets, then exact-cover [q]
    classes = []

    def rec(cur, start, chosen):
        if cur == full:
            classes.append(sum(1 << j for j in chosen))
            return
        low = (~cur & full) & (-(~cur & full))
        for j in range(start, q):
            if (masks[j] & low) and not (masks[j] & cur):
                rec(cur | masks[j], 0, chosen + [j])
    rec(0, 0, [])
    classes = sorted(set(classes))
    target = (1 << q) - 1
    memo = {}

    def cover(cur):
        if cur == target:
            return True
        if cur in memo:
            return memo[cur]
        low = (~cur & target) & (-(~cur & target))
        r = False
        for c in classes:
            if (c & low) and not (c & cur):
                if cover(cur | c):
                    r = True
                    break
        memo[cur] = r
        return r
    return cover(0), len(classes)


# ------------------------------------------------------------- the test
def D_test(mu, p, b, m=None):
    f = psi0(p, b, m)
    rho = deconv(mu, f, p)
    ok = boxp(f, rho, p) == [Fraction(x) for x in mu]
    rr, nreal, nsq = is_real_rooted_exact(rho)
    return rho, ok, rr, nreal, nsq


def max_good_m(mu, p, b):
    """largest m with  mu deconv x^{p-m}(x-b)^m  real-rooted (0 = only trivial)."""
    best = 0
    for m in range(0, p + 1):
        rho = deconv(mu, psi0(p, b, m), p)
        rr, _, _ = is_real_rooted_exact(rho)
        if rr:
            best = m
        else:
            break
    return best


def run_b2():
    print("=" * 108)
    print("b = 2 COMMUTING FAMILIES (a-regular multigraph M; blocks = edges)")
    print("  (D) asks: is  mu deconv x^{p/2}(x-2)^{p/2}  real-rooted?")
    print("=" * 108)
    print("%-24s %3s %3s %3s | %-7s %-7s %-6s | %-9s %-9s %-9s" %
          ("graph M", "p", "q", "a", "par.cls", "resolv", "m*/(p/b)",
           "(D)", "#real", "max|Im|"))
    fams = []
    fams += [('K_4', *complete_graph(4))]
    fams += [('K_{3,3}', *complete_bipartite(3))]
    fams += [('C_3 x K_2 (prism)', *cycle_prism(3))]
    fams += [('K_4 (again)', *complete_graph(4))]
    fams += [('Q_3 (cube)', *hypercube(3))]
    fams += [('K_{3,3} (bip)', *complete_bipartite(3))]
    fams += [('Petersen', *petersen())]
    fams += [('C_4 x K_2', *cycle_prism(4))]
    fams += [('C_5 x K_2 = GP(5,1)', *cycle_prism(5))]
    fams += [('Moebius ladder M_3', *moebius_ladder(3))]
    fams += [('Moebius ladder M_4', *moebius_ladder(4))]
    fams += [('Moebius ladder M_5', *moebius_ladder(5))]
    fams += [('Moebius ladder M_6', *moebius_ladder(6))]
    fams += [('C_6 x K_2', *cycle_prism(6))]
    fams += [('GP(6,2)', *gp(6, 2))]
    fams += [('GP(7,2)', *gp(7, 2))]
    fams += [('Heawood(=GP? ) K_{3,3}+', *complete_bipartite(4))]   # 4-regular
    fams += [('K_5 (a=4, p odd)', *complete_graph(5))]
    fams += [('K_6 (a=5)', *complete_graph(6))]
    fams += [('C_4^2 circ(8,[1,2])', *circulant(8, [1, 2]))]
    fams += [('circ(10,[1,2])', *circulant(10, [1, 2]))]
    fams += [('circ(6,[1,2])', *circulant(6, [1, 2]))]
    fams += [('circ(8,[1,3])', *circulant(8, [1, 3]))]
    fams += [('circ(12,[1,2])', *circulant(12, [1, 2]))]

    seen = set()
    rows = []
    for name, E, p in fams:
        blocks = edges_to_blocks(E)
        q = len(blocks)
        if p * 0 == 0 and (2 * q) % p:
            continue
        a = 2 * q // p
        if not check_biregular(blocks, p, a, 2):
            print("  %-24s SKIP (not %d-regular)" % (name, a))
            continue
        key = (p, q, a, tuple(sorted(blocks)))
        if key in seen:
            continue
        seen.add(key)
        mu = mu_from_blocks(blocks, p)
        if p % 2:
            print("  %-24s %3d %3d %3d | b does not divide p -- psi_0 undefined"
                  % (name, p, q, a))
            rows.append((name, p, q, a, None, None, None, None))
            continue
        pc = has_parallel_class(blocks, p, 2)
        res, ncls = has_resolution(blocks, p, a, 2)
        rho, ok, rr, nreal, nsq = D_test(mu, p, 2)
        mi, _ = maximag_float(rho)
        ms = max_good_m(mu, p, 2)
        print("  %-24s %3d %3d %3d | %-7s %-7s %d/%-4d | %-9s %d/%-7d %.3e"
              % (name, p, q, a, pc, res, ms, p // 2, rr, nreal, nsq, mi))
        rows.append((name, p, q, a, pc, res, rr, ms))
    return rows


if __name__ == '__main__':
    run_b2()
