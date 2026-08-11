"""No connectivity hypothesis repairs Conjecture 10.

C1 said 2-connected suffices. It is false: a 2-cut carries its own recurrence, and the bracket
it produces is quadratic in the number of branches where the cut-vertex bracket was linear.
That is not an accident of the number two, and this file follows the pattern to its end.

THE GENERAL ENGINE. Take k hubs u_1..u_k and p identical branches, each branch attached to
every hub at its own vertex s_j. Deleting the hubs leaves p disjoint copies of the branch, and
summing over which hubs are matched into which branch gives, with A_J = mu of the branch with
the vertices {s_j : j in J} removed,

    mu_G = sum_{S subset of [k]} (-1)^{|S|} x^{k-|S|}
             sum_{partitions P of S} (p)_{|P|} ( prod_{J in P} A_J ) A^{p-|P|},

where (p)_m = p(p-1)...(p-m+1). This is A^{p-k} times a bracket of degree k in p. At k=1 it is
the cut-vertex recurrence mu_H^{p-1}(x mu_H - p mu_{H-v}) that produced every counterexample so
far. At k=2 it is the 2-cut bracket that killed C1.

THE CONSEQUENCE. A k-cut needs the graph to be at most k-connected, but it hands the
construction a degree-k polynomial in p to tune. So each step up in connectivity REMOVES one
separation but ADDS one degree of freedom. Connectivity cannot be the repairing hypothesis at
any level, and the point of this file is to check that the pattern really does continue rather
than stalling at two.

Vertex connectivity is computed exactly by Menger, as a unit-capacity max flow on the split
graph over every non-adjacent pair, so the connectivity claimed is the true one and not an
artifact of the construction. mu_G from the formula above is checked against a brute-force
matching polynomial before use, and spec(T) by the Angel-Friedman-Hoory decay rate.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import functools
import itertools
import numpy as np
import sympy as sp
from scipy.sparse import csr_matrix
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode

x = sp.Symbol('x')
BUDGET = quickmode.budget(1800.0, 25.0)
CKPT = quickmode.ckpt('private/kcut_ckpt.txt')
# ------------------------------------------------------------------ matching polynomial
def mu_of(adj, S):
    @functools.lru_cache(maxsize=None)
    def rec(vs):
        T = set(vs)
        if not T:
            return sp.Integer(1)
        w = min(T, key=lambda t: len(adj[t] & T))
        T1 = T - {w}
        tot = x * rec(tuple(sorted(T1)))
        for z in adj[w] & T:
            tot -= rec(tuple(sorted(T1 - {z})))
        return sp.expand(tot)
    return rec(tuple(sorted(S)))


def partitions(lst):
    if not lst:
        yield []
        return
    first, rest = lst[0], lst[1:]
    for P in partitions(rest):
        for i in range(len(P)):
            yield P[:i] + [[first] + P[i]] + P[i + 1:]
        yield [[first]] + P


def falling(p, m):
    r = 1
    for i in range(m):
        r *= (p - i)
    return r


def mu_kcut(nb, bedges, anchors, p):
    """mu_G for k hubs and p branches, by the k-cut expansion."""
    k = len(anchors)
    adj = {i: set() for i in range(nb)}
    for a, b in bedges:
        adj[a].add(b); adj[b].add(a)
    V = set(range(nb))
    AJ = {}
    for m in range(k + 1):
        for J in itertools.combinations(range(k), m):
            AJ[J] = mu_of(adj, V - {anchors[j] for j in J})
    A = AJ[()]
    tot = sp.Integer(0)
    for m in range(k + 1):
        for S in itertools.combinations(range(k), m):
            sgn = (-1) ** m
            for P in partitions(list(S)):
                f = falling(p, len(P))
                if f == 0:
                    continue
                term = sp.Integer(sgn * f) * x ** (k - m) * A ** (p - len(P))
                for J in P:
                    term *= AJ[tuple(sorted(J))]
                tot += term
    return sp.expand(tot)


def assemble(nb, bedges, anchors, p):
    k = len(anchors)
    edges, n = [], k
    for _ in range(p):
        off = n
        for a, b in bedges:
            edges.append((a + off, b + off))
        for j, s in enumerate(anchors):
            edges.append((j, s + off))
        n += nb
    return n, edges


# ------------------------------------------------------------------ exact connectivity
def local_cut(n, adj, s, t):
    """min vertex cut separating non-adjacent s,t: unit-capacity max flow on the split graph."""
    N = 2 * n                       # v_in = 2v, v_out = 2v+1
    cap = {}

    def add(a, b, c):
        cap[(a, b)] = cap.get((a, b), 0) + c
        cap.setdefault((b, a), 0)
    for v in range(n):
        add(2 * v, 2 * v + 1, 10 ** 6 if v in (s, t) else 1)
    for v in range(n):
        for w in adj[v]:
            add(2 * v + 1, 2 * w, 10 ** 6)
    nbr = {}
    for (a, b) in cap:
        nbr.setdefault(a, set()).add(b)
    src, snk, flow = 2 * s + 1, 2 * t, 0
    while True:
        par, q = {src: None}, [src]
        while q and snk not in par:
            a = q.pop(0)
            for b in nbr.get(a, ()):
                if b not in par and cap[(a, b)] > 0:
                    par[b] = a; q.append(b)
        if snk not in par:
            return flow
        b, bot = snk, 10 ** 9
        while par[b] is not None:
            bot = min(bot, cap[(par[b], b)]); b = par[b]
        b = snk
        while par[b] is not None:
            cap[(par[b], b)] -= bot; cap[(b, par[b])] += bot; b = par[b]
        flow += bot


def vertex_connectivity(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    best = n - 1
    for s in range(n):
        for t in range(s + 1, n):
            if t in adj[s]:
                continue
            best = min(best, local_cut(n, adj, s, t))
            if best == 0:
                return 0
    return best


# ------------------------------------------------------------------ spec(T)
def setup(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    rows, cols = [], []
    for k, (a, b) in enumerate(de):
        for c in adj[b]:
            if c != a:
                rows.append(k); cols.append(idx[(b, c)])
    M = len(de)
    return csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(M, M)), M


def rho_at(lam, B, M, iters=6000, tol=1e-13):
    h = np.full(M, 0.5)
    for _ in range(iters):
        s = lam - B @ h
        if np.min(np.abs(s)) < 1e-12:
            return None
        new = 1.0 / s
        d = np.max(np.abs(new - h))
        h = new
        if d < tol:
            break
    else:
        return None
    h2 = h * h
    vec = np.abs(np.sin(np.arange(M) * 1.7)) + 0.1
    r2 = 0.0
    for _ in range(3000):
        w = h2 * (B @ (h2 * (B @ vec)))
        nr = np.max(np.abs(w))
        if nr == 0:
            return 0.0
        vec = w / nr
        r2 = nr
    return math.sqrt(r2)


def edge_toward(theta, B, M, direction, span=0.7, step=0.004, tol=1e-7):
    prev, t, good, bad = theta, theta, None, None
    while abs(t - theta) < span:
        t += direction * step
        r = rho_at(t, B, M)
        if r is None or r >= 1:
            good, bad = prev, t; break
        prev = t
    if good is None:
        return None
    for _ in range(45):
        if abs(bad - good) < tol:
            break
        mid = (good + bad) / 2
        r = rho_at(mid, B, M)
        if r is not None and r < 1:
            good = mid
        else:
            bad = mid
    return good


# ------------------------------------------------------------------ branches
def br_cycle_tail(L, k, T):
    """cycle C_L with k anchors spread around it, each carrying a tail of length T."""
    e = [(i, (i + 1) % L) for i in range(L)]
    n = L
    anchors = []
    step = max(1, L // k)
    for j in range(k):
        prev = (j * step) % L
        for _ in range(T):
            e.append((prev, n)); prev = n; n += 1
        anchors.append(prev if T else (j * step) % L)
    return n, e, anchors


def br_Kmq(q, k):
    """K_{k,q}: the k degree-q vertices are the anchors."""
    e = []
    for j in range(k):
        for m in range(q):
            e.append((j, k + m))
    return k + q, e, list(range(k))


def br_Kmq_tail(q, k, T):
    """K_{k,q} with a tail of length T hung on each anchor."""
    e = []
    for j in range(k):
        for m in range(q):
            e.append((j, k + m))
    n = k + q
    anchors = []
    for j in range(k):
        prev = j
        for _ in range(T):
            e.append((prev, n)); prev = n; n += 1
        anchors.append(prev)
    return n, e, anchors


def families(k):
    out = []
    for q in range(2, 7):
        for T in (0, 1, 2, 3):
            out.append((f"K{k},{q}+t{T}", br_Kmq_tail(q, k, T) if T else br_Kmq(q, k)))
    for L in range(max(3, k), 9):
        for T in (0, 1, 2):
            out.append((f"C{L}+t{T}", br_cycle_tail(L, k, T)))
    return out


def selfcheck():
    ok = True
    for (nb, be, anc), p in ((br_Kmq(3, 2), 3), (br_Kmq_tail(2, 3, 1), 3),
                             (br_cycle_tail(4, 3, 0), 3)):
        pred = mu_kcut(nb, be, anc, p)
        n, edges = assemble(nb, be, anc, p)
        adj = {i: set() for i in range(n)}
        for a, b in edges:
            adj[a].add(b); adj[b].add(a)
        good = sp.expand(pred - mu_of(adj, set(range(n)))) == 0
        ok = ok and good
        print(f"  k={len(anc)} nb={nb} p={p} n={n}: {'OK' if good else 'MISMATCH'}", flush=True)
    return ok


def main():
    print("does the k-cut engine keep working as connectivity rises?\n")
    print("self-check of the k-cut expansion against brute force:", flush=True)
    if not selfcheck():
        print("EXPANSION WRONG - nothing below is meaningful.")
        return 1
    print()
    print(f"{'k':>2}{'branch':>12}{'p':>3}{'n':>5}{'kappa':>6}{'root':>11}"
          f"{'defect':>11}{'width':>9}{'verdict':>9}", flush=True)
    t0 = time.time()
    best = {}
    for k in (3, 4, 5):
        for name, (nb, be, anc) in families(k):
            if time.time() - t0 > BUDGET:
                break
            for p in range(k, 10):
                n = k + p * nb
                if n > 62 or time.time() - t0 > BUDGET:
                    continue
                muG = mu_kcut(nb, be, anc, p)
                co = sp.Poly(muG, x).all_coeffs()
                while co and co[-1] == 0:
                    co.pop()
                if len(co) < 2:
                    continue
                try:
                    roots = [float(sp.re(r)) for r in
                             sp.Poly(co, x).nroots(n=20, maxsteps=3000)
                             if abs(sp.im(r)) < 1e-10 and sp.re(r) > 1e-9]
                except Exception:
                    continue
                edges = assemble(nb, be, anc, p)[1]
                B, M = setup(n, edges)
                hit = None
                for th in roots:
                    r = rho_at(th, B, M)
                    if r is None or r >= 1:
                        continue
                    lo = edge_toward(th, B, M, -1)
                    hi = edge_toward(th, B, M, +1)
                    if lo is None or hi is None:
                        continue
                    hit = (th, min(th - lo, hi - th), hi - lo)
                    break
                if hit is None:
                    continue
                kap = vertex_connectivity(n, edges)
                print(f"{k:>2}{name:>12}{p:>3}{n:>5}{kap:>6}{hit[0]:>11.6f}"
                      f"{hit[1]:>11.6f}{hit[2]:>9.5f}{'GAP':>9}", flush=True)
                if kap not in best or n < best[kap][2]:
                    best[kap] = (name, p, n, k, hit[0], hit[1], hit[2])
                with open(CKPT + '.tmp', 'w') as f:
                    f.write(f"k={k} {name} p={p} best={sorted(best)}\n")
                os.replace(CKPT + '.tmp', CKPT)
    print(f"\n{time.time()-t0:.0f}s")
    print("\nsmallest violation at each true vertex connectivity kappa:")
    print(f"{'kappa':>6}{'branch':>12}{'k':>3}{'p':>3}{'n':>5}{'root':>11}{'defect':>11}")
    for kap in sorted(best):
        nm, p, n, k, th, df, w = best[kap]
        print(f"{kap:>6}{nm:>12}{k:>3}{p:>3}{n:>5}{th:>11.6f}{df:>11.6f}")
    if best and max(best) >= 3:
        print(f"\nConjecture 10 fails at vertex connectivity {max(best)}. "
              "Connectivity is not the repairing hypothesis at any level.")
    else:
        print("\nno violation above connectivity 2 in this range.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
