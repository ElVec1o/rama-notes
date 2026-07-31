"""ineq2_moments.py -- exactly how far the moment / Newton ladder gets, and the
extremal family.

Uses the structure established in ineq2_ladder.py:

    mu(x+a) = sum_r (-1)^r M_r x^{p-2r},   M_r = a^{2r} e_r(pi) >= 0,
    M_0 = 1, M_1 = q, M_2 = C(q,2) - q(a-1) + a^4 sum_{j<k}|det Pi[B_j,B_k]|^2,
    p_j := sum_i pi_i^j = -(j/a^{2j}) [t^j] log( sum_r (-1)^r M_r t^r ),
    pi_max = lim_j p_j^{1/j}   (decreasing along j after the transient).

PART A.  the two-moment bound and its exact reach.
PART B.  how many moments are actually needed:  j_min(p) for the extremal graphs.
PART C.  the extremal family: is the sup over projection families attained on
         graphs, and does it approach 4(a-1)/a^2 ?
"""
import sys
import numpy as np
from fractions import Fraction
from math import comb, sqrt, log

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from mcp2 import mcp, restore_proj, rand_X, proj_from_X                    # noqa


# --------------------------------------------------------------- power sums
def power_sums_from_M(M, a, jmax):
    """p_j = sum_i pi_i^j from the M_r, exactly (Fractions in, Fractions out).
       Q(t) = sum_r (-1)^r M_r t^r ;   log Q = sum_j c_j t^j ;   p_j = -j c_j / a^{2j}."""
    Q = [Fraction(0)] * (jmax + 1)
    for r, m in enumerate(M):
        if r <= jmax:
            Q[r] = Fraction((-1) ** r) * Fraction(m)
    c = [Fraction(0)] * (jmax + 1)          # log Q coefficients, c[0] = 0
    for n in range(1, jmax + 1):
        s = Fraction(n) * Q[n]
        for k in range(1, n):
            s -= Fraction(k) * c[k] * Q[n - k]
        c[n] = s / Fraction(n)
    return [Fraction(-n) * c[n] / Fraction(a) ** (2 * n) for n in range(1, jmax + 1)]


def matching_numbers(adj, p):
    """exact r-matching counts of a simple graph given as adjacency bitmasks."""
    from functools import lru_cache
    full = (1 << p) - 1

    @lru_cache(maxsize=None)
    def f(avail):
        if avail == 0:
            return (1,)
        v = (avail & -avail).bit_length() - 1
        rest = avail & ~(1 << v)
        out = list(f(rest)) + [0]              # v unmatched
        nb = adj[v] & rest
        while nb:
            u = (nb & -nb).bit_length() - 1
            nb &= nb - 1
            sub = f(rest & ~(1 << u))
            for i, val in enumerate(sub):
                out[i + 1] += val
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        return tuple(out)
    return list(f(full))


def girth(adj, p):
    best = 10 ** 9
    for s in range(p):
        dist = [-1] * p
        par = [-1] * p
        dist[s] = 0
        Q = [s]
        while Q:
            nq = []
            for v in Q:
                nb = adj[v]
                while nb:
                    u = (nb & -nb).bit_length() - 1
                    nb &= nb - 1
                    if dist[u] < 0:
                        dist[u] = dist[v] + 1
                        par[u] = v
                        nq.append(u)
                    elif u != par[v]:
                        best = min(best, dist[u] + dist[v] + 1)
            Q = nq
    return best


def nx_graph(name, **kw):
    import networkx as nx
    G = getattr(nx, name)(**kw)
    p = G.number_of_nodes()
    idx = {v: i for i, v in enumerate(G.nodes())}
    adj = [0] * p
    for u, v in G.edges():
        adj[idx[u]] |= 1 << idx[v]
        adj[idx[v]] |= 1 << idx[u]
    return adj, p


# ------------------------------------------------------------------- PART A
def part_A():
    print("=" * 92)
    print("PART A -- the two-moment bound, exact reach")
    print("=" * 92)
    print("  sum_i pi_i^2 = q(2a-1)/a^4 - 2 sum_{j<k}|det Pi[B_j,B_k]|^2 <= p(2a-1)/(2a^3)")
    print("  pi_max <= sqrt(p(2a-1)/(2a^3));  INEQ-2 follows iff p <= 32(a-1)^2/(a(2a-1))")
    print()
    print(f"  {'a':>3} {'32(a-1)^2/(a(2a-1))':>21} {'p_crit':>7} "
          f"{'check p=p_crit':>15} {'check p=p_crit+2':>17}")
    for a in list(range(3, 13)) + [20, 50, 100, 1000]:
        thr = 32.0 * (a - 1) ** 2 / (a * (2 * a - 1))
        pc = int(np.floor(thr + 1e-12))
        pc -= pc % 2 if False else 0
        bound = 4.0 * (a - 1) / a ** 2
        ok1 = sqrt(pc * (2 * a - 1) / (2 * a ** 3)) <= bound + 1e-12
        ok2 = sqrt((pc + 2) * (2 * a - 1) / (2 * a ** 3)) <= bound + 1e-12
        print(f"  {a:>3} {thr:>21.4f} {pc:>7} {str(ok1):>15} {str(ok2):>17}")
    print("\n  => two moments settle INEQ-2 only for p <= 8 (a=3), 10 (a=4), ..., 15 (a->oo).")
    print("     limit as a->oo is 16;  the bound is USELESS for large p at every a.")
    print("     Note p_2 is EXACTLY q(2a-1)/a^4 for every simple graph (all det Pi[B_j,B_k]=0),")
    print("     so the inequality p_2 <= q(2a-1)/a^4 is tight and cannot be improved.")


# ------------------------------------------------------------------- PART B
LCF = [('Petersen', 10, None, None), ('Heawood', 14, [5, -5], 7),
       ('Moebius-Kantor', 16, [5, -5], 8), ('Pappus', 18, [5, 7, -7, 7, -7, -5], 3),
       ('Desargues', 20, [5, -5, 9, -9], 5), ('Nauru', 24, [5, -9, 7, -7, 9, -5], 4),
       ('McGee', 24, [12, 7, -7], 8), ('F26A', 26, [7, -7], 13),
       ('Tutte-Coxeter', 30, [-13, -9, 7, -7, 9, 13], 5),
       ('Dyck', 32, [5, -5, 13, -13], 8), ('F38', 38, [15, -15], 19)]


def cubic_graphs():
    import networkx as nx
    out = []
    for nm, n, sh, rep in LCF:
        G = nx.petersen_graph() if sh is None else nx.LCF_graph(n, sh, rep)
        p = G.number_of_nodes()
        order = list(nx.bfs_tree(G, list(G.nodes())[0]).nodes())
        idx = {v: i for i, v in enumerate(order)}
        adj = [0] * p
        for u, v in G.edges():
            adj[idx[u]] |= 1 << idx[v]
            adj[idx[v]] |= 1 << idx[u]
        if any(bin(x).count('1') != 3 for x in adj):
            continue
        out.append((nm, tuple(adj), p))
    return out


def pimax_from_M(M, p, a):
    co = np.zeros(p + 1)
    for r, m in enumerate(M):
        co[2 * r] = (-1) ** r * float(m)
    rts = np.sort(np.roots(co).real)
    return (rts[-1] / a) ** 2, rts[-1]


def part_B():
    print()
    print("=" * 92)
    print("PART B -- how many moments does the ladder need?"
          "   j_min = min{ j : p_j^(1/j) <= 4(a-1)/a^2 }")
    print("=" * 92)
    a = 3
    bound = 4.0 * (a - 1) / a ** 2
    print(f"  a=3, threshold 4(a-1)/a^2 = {bound:.6f};  p_j^(1/j) decreases to pi_max")
    print(f"  {'graph':16s} {'p':>3} {'g':>2} {'pi_max':>10} {'ratio':>7} {'j_min':>6}   "
          + ' '.join(f"j={j:<3d}" for j in (1, 2, 3, 5, 8, 12, 20, 40)))
    for nm, adj, p in cubic_graphs():
        M = matching_numbers(adj, p)
        pj = power_sums_from_M(M, a, 60)
        pimax, _ = pimax_from_M(M, p, a)
        jmin = next((j for j in range(1, 61)
                     if float(pj[j - 1]) > 0 and float(pj[j - 1]) ** (1.0 / j) <= bound), None)
        row = ' '.join(f"{float(pj[j-1])**(1.0/j):<5.3f}" for j in (1, 2, 3, 5, 8, 12, 20, 40))
        print(f"  {nm:16s} {p:>3} {girth(list(adj), p):>2} {pimax:>10.6f} "
              f"{pimax/bound:>7.4f} {str(jmin):>6}   {row}")
    print()
    print("  j_min GROWS with p and (because pi_max -> the threshold) diverges:")
    print("  no ladder of boundedly many moments can prove INEQ-2.")


# ------------------------------------------------------------------- PART C
def pimax_of(P, a):
    r = np.sort(np.roots(mcp(P)).real)
    return ((r.max() - a) / a) ** 2


def hill(p, q, a, rng, steps=400, restarts=6, eps0=0.7):
    b = 2
    best = -1.0
    for _ in range(restarts):
        X = rand_X(q, p, b, rng)
        P, res = restore_proj(proj_from_X(X), q, p, a, b, iters=4000, tol=1e-14)
        if res > 1e-11:
            continue
        cur = pimax_of(P, a)
        eps = eps0
        for t in range(steps):
            w, V = np.linalg.eigh(P)
            U = V[:, :, -b:] + eps * rng.standard_normal((q, p, b))
            Q, _ = np.linalg.qr(U)
            cand, res = restore_proj(Q @ np.swapaxes(Q, 1, 2), q, p, a, b,
                                     iters=2000, tol=1e-13)
            if res > 1e-10:
                eps *= 0.9
                continue
            v = pimax_of(cand, a)
            if v > cur:
                cur, P = v, cand
            else:
                eps *= 0.99
            if eps < 5e-5:
                break
        best = max(best, cur)
    return best


def part_C():
    import networkx as nx
    print()
    print("=" * 92)
    print("PART C -- the extremal family")
    print("=" * 92)
    a = 3
    bound = 4.0 * (a - 1) / a ** 2
    print(f"  (C1) cubic graphs: lambda_max -> a + 2 sqrt(a-1) = {a+2*sqrt(a-1):.7f}, "
          f"pi_max -> 4(a-1)/a^2 = {bound:.7f}")
    print(f"       {'graph':16s} {'p':>3} {'girth':>5} {'lambda_max':>12} {'pi_max':>11} {'ratio':>9}")
    for nm, adj, p in cubic_graphs():
        M = matching_numbers(adj, p)
        pimax, x = pimax_from_M(M, p, a)
        print(f"       {nm:16s} {p:>3} {girth(list(adj), p):>5} {a+x:>12.7f} "
              f"{pimax:>11.7f} {pimax/bound:>9.6f}")

    print("\n  (C2) best GRAPH vs best general PROJECTION family at the same (p,q,a):")
    rng = np.random.default_rng(20260801)
    for (p, q, a) in [(4, 6, 3), (6, 9, 3), (8, 12, 3), (6, 12, 4)]:
        if p * a != 2 * q:
            continue
        bd = 4.0 * (a - 1) / a ** 2
        bg = -1.0
        seen = set()
        for trial in range(400):
            G = nx.random_regular_graph(a, p, seed=int(rng.integers(1 << 30)))
            key = tuple(sorted(map(tuple, map(sorted, G.edges()))))
            if key in seen:
                continue
            seen.add(key)
            adj = [0] * p
            for u, v in G.edges():
                adj[u] |= 1 << v
                adj[v] |= 1 << u
            M = matching_numbers(tuple(adj), p)
            bg = max(bg, pimax_from_M(M, p, a)[0])
        bp = hill(p, q, a, rng, steps=250, restarts=5)
        tag = 'graph >= proj' if bg >= bp - 1e-7 else '*** PROJECTIONS BEAT GRAPHS'
        print(f"       (p,q,a)=({p},{q},{a})  GRAPH {bg:.8f} (r={bg/bd:.5f})  "
              f"PROJ {bp:.8f} (r={bp/bd:.5f})   {tag}", flush=True)


if __name__ == '__main__':
    part_A()
    part_B()
    part_C()
