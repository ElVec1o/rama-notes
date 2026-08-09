"""C1: does two-connectivity repair Conjecture 10?

FROZEN BEFORE THIS DATA:
  C1. Every 2-connected finite graph G satisfies Zeros(mu_G) inside spec(T_G).

WHY IT IS THE RIGHT HYPOTHESIS TO TRY. Every counterexample so far is built on the branch
recurrence

    mu_G = mu_H^{p-1} ( x mu_H - p mu_{H-v} ),

which exists only because a cut vertex splits the graph into isomorphic branches. Without a
cut vertex the matching polynomial does not factor that way and the resonance cannot be
engineered. Consistently, a cycle-skeleton family that is 2-connected produced no
counterexample in 26 cases (code/cycle_family.py), while both families that do produce them
are full of cut vertices.

Part A checks the mechanism claim: every known counterexample should have a cut vertex.

Part B is the falsification attempt, and it is the real test. Take the constructions that DO
work and close them up, adding edges until no cut vertex remains, then look for a root in a
gap. If the effect survives closure, C1 dies immediately. If it does not, C1 has been attacked
where it is most vulnerable, because these are the graphs most likely to violate it.

mu_G by memoised vertex deletion; spec(T) by the Angel-Friedman-Hoory decay rate with gap
edges bracketed by an outward scan before bisection.
"""

import sys
import os
import math
import time
import random
import functools
import itertools
import sympy as sp

x = sp.Symbol('x')


# ---------------------------------------------------------------- graph utilities
def cut_vertices(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)

    def connected_without(v):
        rest = [u for u in range(n) if u != v]
        if not rest:
            return True
        seen, st = {rest[0]}, [rest[0]]
        while st:
            u = st.pop()
            for w in adj[u]:
                if w != v and w not in seen:
                    seen.add(w); st.append(w)
        return len(seen) == len(rest)
    return [v for v in range(n) if not connected_without(v)]


def mu_memo(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    sys.setrecursionlimit(200000)

    @functools.lru_cache(maxsize=None)
    def mu(vs):
        S = set(vs)
        if not S:
            return sp.Integer(1)
        v = min(S, key=lambda t: len(adj[t] & S))
        S1 = S - {v}
        tot = x * mu(tuple(sorted(S1)))
        for u in adj[v] & S:
            tot -= mu(tuple(sorted(S1 - {u})))
        return sp.expand(tot)
    return mu(tuple(range(n)))


def setup(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    return [[idx[(b, c)] for c in adj[b] if c != a] for (a, b) in de], len(de)


def rho_at(lam, foll, M, iters=20000, tol=1e-12):
    h = [0.5] * M
    for _ in range(iters):
        new = [0.0] * M
        d = 0.0
        for k in range(M):
            s = lam
            for f in foll[k]:
                s -= h[f]
            if abs(s) < 1e-12:
                return None
            v = 1.0 / s
            d = max(d, abs(v - h[k])); new[k] = v
        h = new
        if d < tol:
            break
    else:
        return None
    random.seed(1)
    vec = [random.random() + 0.1 for _ in range(M)]
    r2 = 0.0
    for _ in range(2500):
        w1 = [h[k] * h[k] * sum(vec[f] for f in foll[k]) for k in range(M)]
        w2 = [h[k] * h[k] * sum(w1[f] for f in foll[k]) for k in range(M)]
        nr = max(abs(t) for t in w2)
        if nr == 0:
            return 0.0
        vec = [t / nr for t in w2]
        r2 = nr
    return math.sqrt(r2)


def edge_toward(theta, foll, M, direction, span=0.6, step=0.004, tol=1e-6):
    prev, t, good, bad = theta, theta, None, None
    while abs(t - theta) < span:
        t += direction * step
        r = rho_at(t, foll, M)
        if r is None or r >= 1:
            good, bad = prev, t; break
        prev = t
    if good is None:
        return None
    for _ in range(40):
        if abs(bad - good) < tol:
            break
        mid = (good + bad) / 2
        r = rho_at(mid, foll, M)
        if r is not None and r < 1:
            good = mid
        else:
            bad = mid
    return good


# ---------------------------------------------------------------- constructions
def tri_skeleton(depth):
    edges, c = [], [0]
    tri_roots = []
    def place():
        off = c[0]; c[0] += 3
        for (a, b) in [(0, 1), (1, 2), (2, 0)]:
            edges.append((a + off, b + off))
        tri_roots.append(off)
        return off
    def rec(d):
        if d == 0:
            return place()
        r = c[0]; c[0] += 1
        for _ in range(2):
            rt = rec(d - 1); edges.append((r, rt))
        return r
    rec(depth)
    return c[0], edges, tri_roots


def hall_star(p, q):
    e, n = [], 1
    ws = []
    for _ in range(p):
        off = n
        v, w = off, off + 1
        us = list(range(off + 2, off + 2 + q))
        cur = off + 2 + q
        for u in us:
            e.append((v, u)); e.append((u, w))
        e.append((w, cur)); leaf = cur; cur += 1
        e.append((0, v))
        ws.append((w, leaf))
        n = cur
    return n, e, ws


def close_up(n, edges, ring):
    """add a cycle through `ring` to kill cut vertices"""
    e = list(edges)
    L = len(ring)
    for i in range(L):
        a, b = ring[i], ring[(i + 1) % L]
        if a != b and (a, b) not in e and (b, a) not in e:
            e.append((a, b))
    return n, e


def examine(name, n, edges):
    cuts = cut_vertices(n, edges)
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    muG = mu_memo(n, edges)
    co = sp.Poly(muG, x).all_coeffs()
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return None
    try:
        roots = [float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=18, maxsteps=2500)
                 if abs(sp.im(r)) < 1e-9 and sp.re(r) > 1e-9]
    except Exception:
        return None
    foll, M = setup(n, edges)
    hits = []
    for th in roots:
        r = rho_at(th, foll, M)
        if r is None or r >= 1:
            continue
        lo = edge_toward(th, foll, M, -1)
        hi = edge_toward(th, foll, M, +1)
        if lo is None or hi is None:
            continue
        hits.append((th, min(th - lo, hi - th), hi - lo))
    print(f"{name:>26}{n:>5}{len(cuts):>7}{min(deg):>5}{max(deg):>5}"
          f"{(f'{hits[0][0]:.5f}' if hits else '-'):>10}"
          f"{(f'{hits[0][1]:.6f}' if hits else '-'):>11}"
          f"{('GAP' if hits else 'in spec'):>9}", flush=True)
    return hits, cuts


def main():
    print("A. do all known counterexamples have cut vertices?\n")
    print(f"{'case':>26}{'n':>5}{'#cuts':>7}{'dmin':>5}{'dmax':>5}"
          f"{'root':>10}{'defect':>11}{'verdict':>9}", flush=True)
    n1, e1, tr1 = tri_skeleton(3)
    examine("tri depth 3 (original)", n1, e1)
    n2, e2, ws2 = hall_star(5, 5)
    examine("Hall (5,5) (original)", n2, e2)

    print("\nB. closing them up until no cut vertex remains\n", flush=True)
    print(f"{'case':>26}{'n':>5}{'#cuts':>7}{'dmin':>5}{'dmax':>5}"
          f"{'root':>10}{'defect':>11}{'verdict':>9}", flush=True)
    # tri: ring through the triangle roots, and through the far triangle vertices
    n3, e3 = close_up(n1, e1, tr1)
    examine("tri depth 3 + root ring", n3, e3)
    far = [t + 1 for t in tr1]
    n4, e4 = close_up(n1, e1, far)
    examine("tri depth 3 + far ring", n4, e4)
    n5, e5 = close_up(*close_up(n1, e1, tr1)[:2], far)
    examine("tri depth 3 + both rings", n5, e5)
    # Hall: ring through the leaves, and through the w's
    leaves = [t[1] for t in ws2]
    n6, e6 = close_up(n2, e2, leaves)
    examine("Hall (5,5) + leaf ring", n6, e6)
    wsv = [t[0] for t in ws2]
    n7, e7 = close_up(n2, e2, wsv)
    examine("Hall (5,5) + w ring", n7, e7)
    print("\nA surviving GAP with zero cut vertices refutes C1 outright.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
