"""What actually narrows the gaps: connectivity, or the minimum degree it forces?

C1 died to a 2-cut. The obvious continuation, that a k-cut beats k-connectedness at every k,
then failed: nothing at k = 3, 4, 5. The story offered was that raising connectivity forces
edges, widens the bands of spec(T) and narrows the gaps a root could sit in. That is a story,
not a measurement, and this file is the measurement.

There is a confound worth naming first, because it may be the whole answer. A graph of vertex
connectivity kappa has minimum degree at least kappa. So demanding 3-connectedness silently
demands minimum degree three, and minimum degree three forbids long induced paths of degree-2
vertices. Those chains are exactly what makes a universal cover far from regular, and a regular
tree has NO gaps at all: spec of the d-regular tree is the single interval [-2sqrt(d-1),
2sqrt(d-1)]. So the narrowing may have nothing to do with connectivity and everything to do
with the minimum degree riding along behind it.

That matters because minimum degree is the far weaker hypothesis, and every counterexample in
hand has minimum degree at most two: Hall's has leaves, the 31-vertex graph and all three
2-cut graphs have degree-2 vertices.

FROZEN BEFORE THE DATA:
  P1. Total gap width of spec(T) is governed by the minimum degree, collapsing sharply at
      delta >= 3, and vertex connectivity adds nothing once delta is known.

If P1 holds, the hypothesis to attack is delta >= 3, not 3-connectedness, and C2 is the wrong
statement of the right idea.

Gaps are located by scanning the Angel-Friedman-Hoory decay rate; a point is outside spec(T)
when the decay rate is below one. Vertex connectivity is exact, by Menger: a minimum cut of
size at most delta must miss one of any delta+1 chosen vertices, so it suffices to run
unit-capacity max flows from delta+1 sources to all their non-neighbours.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import numpy as np
from scipy.sparse import csr_matrix

CKPT = 'private/gapscale_ckpt.txt'


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


def rho_at(lam, B, M, iters=4000, tol=1e-12):
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
    for _ in range(1500):
        w = h2 * (B @ (h2 * (B @ vec)))
        nr = np.max(np.abs(w))
        if nr == 0:
            return 0.0
        vec = w / nr
        r2 = nr
    return math.sqrt(r2)


def gap_profile(n, edges, step=0.02):
    """gaps of spec(T) inside (0, rho], measured to resolution `step`."""
    B, M = setup(n, edges)
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    hi = 2 * math.sqrt(max(deg) - 1) + 0.5
    out, cur, t = [], None, step
    while t < hi:
        r = rho_at(t, B, M)
        outside = (r is not None and r < 1)
        if outside and cur is None:
            cur = t
        if not outside and cur is not None:
            if t - cur > 1.5 * step:
                out.append((cur, t))
            cur = None
        t += step
    if cur is not None and hi - cur > 1.5 * step:
        out.append((cur, hi))
    # the unbounded region above the spectral radius is not a gap
    out = [g for g in out if g[1] < hi - step]
    return out


# ------------------------------------------------------------------ exact connectivity
def local_cut(n, adj, s, t):
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


def connectivity(n, edges):
    """exact vertex connectivity: a cut of size <= delta misses one of any delta+1 vertices."""
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    delta = min(len(adj[v]) for v in range(n))
    best = delta
    for s in range(min(delta + 1, n)):
        for t in range(n):
            if t == s or t in adj[s]:
                continue
            best = min(best, local_cut(n, adj, s, t))
            if best == 0:
                return 0
    return best


# ------------------------------------------------------------------ graph zoo
def chain_hubs(k, p, q, T):
    """k hubs, p branches of K_{2,q} with a tail of T vertices. T>0 gives degree-2 chains."""
    edges, n = [], k
    for _ in range(p):
        s, t = n, n + 1
        mids = list(range(n + 2, n + 2 + q))
        n += 2 + q
        for m in mids:
            edges.append((s, m)); edges.append((m, t))
        prev = t
        for _ in range(T):
            edges.append((prev, n)); prev = n; n += 1
        for j in range(k):
            edges.append((j, s if j == 0 else prev))
    return n, edges


def subdivided_regular(d, m, s):
    """a d-regular-ish circulant, every edge subdivided s times: forces long degree-2 chains."""
    base = []
    for i in range(m):
        for j in range(1, d // 2 + 1):
            a, b = i, (i + j) % m
            if a != b and (min(a, b), max(a, b)) not in base:
                base.append((min(a, b), max(a, b)))
    edges, n = [], m
    for a, b in base:
        prev = a
        for _ in range(s):
            edges.append((prev, n)); prev = n; n += 1
        edges.append((prev, b))
    return n, edges


def circulant(m, offs):
    """a genuine min-degree-|2 offs| graph with no degree-2 vertices."""
    edges = set()
    for i in range(m):
        for o in offs:
            a, b = i, (i + o) % m
            if a != b:
                edges.add((min(a, b), max(a, b)))
    return m, sorted(edges)


def biregular(a, b, m):
    """(a,b)-biregular bipartite graph: irregular, delta>=min(a,b), and its universal cover
    is the (a,b)-biregular tree, which HAS a gap around zero when a != b."""
    if (m * a) % b:
        return None
    r = (m * a) // b
    edges = set()
    for i in range(m):
        for j in range(a):
            edges.add((i, m + ((i * a + j) % r)))
    n = m + r
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
    if min(deg) < min(a, b) or len(edges) != m * a:
        return None
    return n, sorted(edges)


def ladder_hubs(k, p, L):
    """k hubs and p ladder branches. A ladder has internal degree 3 and corner degree 2; the
    corners are joined to hubs, so EVERY vertex has degree at least three. This is the
    delta>=3 analogue of a degree-2 chain, which is what makes it the right stress test."""
    edges, n = [], k
    for _ in range(p):
        top = list(range(n, n + L)); n += L
        bot = list(range(n, n + L)); n += L
        for i in range(L - 1):
            edges.append((top[i], top[i + 1])); edges.append((bot[i], bot[i + 1]))
        for i in range(L):
            edges.append((top[i], bot[i]))
        for j in range(k):
            edges.append((j, top[0] if j % 2 == 0 else top[-1]))
            edges.append((j, bot[0] if j % 2 == 0 else bot[-1]))
    return n, edges


def mixed_degree(m, extra):
    """cubic circulant with `extra` chords added: min degree 3, degrees 3 and 4 mixed."""
    edges = set()
    for i in range(m):
        edges.add((min(i, (i + 1) % m), max(i, (i + 1) % m)))
    for i in range(0, m, 2):
        edges.add((min(i, (i + m // 2) % m), max(i, (i + m // 2) % m)))
    for j in range(extra):
        a, b = (3 * j) % m, (3 * j + m // 3) % m
        if a != b:
            edges.add((min(a, b), max(a, b)))
    n = m
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
    if min(deg) < 3:
        return None
    return n, sorted(edges)


def theta_chain(p, L):
    """p internally-disjoint paths of length L between two hubs, then every path vertex
    doubled into a rung pair: delta 3, strongly irregular, long thin resonator."""
    edges, n = [], 2
    for _ in range(p):
        a = list(range(n, n + L)); n += L
        b = list(range(n, n + L)); n += L
        for i in range(L - 1):
            edges.append((a[i], a[i + 1])); edges.append((b[i], b[i + 1]))
        for i in range(L):
            edges.append((a[i], b[i]))
        edges += [(0, a[0]), (0, b[0]), (1, a[-1]), (1, b[-1])]
    return n, edges


def zoo():
    G = []
    for T in (0, 2, 3):
        for k in (1, 2, 3):
            for p in (4, 6):
                n, e = chain_hubs(k, p, 4, T)
                if n <= 52:
                    G.append((f"hub k={k} p={p} T={T}", n, e))
    for s_ in (1, 3):
        for m in (6, 8):
            n, e = subdivided_regular(4, m, s_)
            if n <= 52:
                G.append((f"subdiv m={m} s={s_}", n, e))
    for m in (10, 18):
        for offs in ((1, 2), (1, 2, 3)):
            n, e = circulant(m, offs)
            G.append((f"circ m={m} off={offs}", n, e))
    # ---- irregular, minimum degree at least three: the honest test of P1
    for (a, b, m) in ((3, 4, 16), (3, 5, 20), (3, 6, 18), (4, 6, 18),
                      (3, 4, 20), (2, 4, 16), (3, 9, 18)):
        r = biregular(a, b, m)
        if r and r[0] <= 52:
            G.append((f"bireg {a},{b} n={r[0]}", r[0], r[1]))
    for k in (2, 3):
        for p in (3, 4):
            for L in (3, 5, 7):
                n, e = ladder_hubs(k, p, L)
                if n <= 52:
                    G.append((f"ladder k={k} p={p} L={L}", n, e))
    for p in (3, 4):
        for L in (3, 5):
            n, e = theta_chain(p, L)
            if n <= 52:
                G.append((f"theta p={p} L={L}", n, e))
    for m in (12, 18, 24):
        for x in (1, 3):
            r = mixed_degree(m, x)
            if r:
                G.append((f"mixed m={m} x={x}", r[0], r[1]))
    return G


def main():
    print("P1 (frozen): gap width is governed by the minimum degree, collapsing at delta>=3;")
    print("             connectivity adds nothing once delta is known.\n")
    print(f"{'case':>22}{'n':>5}{'|E|':>5}{'dmin':>5}{'dmax':>5}{'kappa':>6}"
          f"{'#gaps':>6}{'totgap':>9}{'maxgap':>9}", flush=True)
    rows = []
    t0 = time.time()
    for name, n, e in zoo():
        adj = {i: set() for i in range(n)}
        for a, b in e:
            adj[a].add(b); adj[b].add(a)
        if any(not adj[v] for v in range(n)):
            continue
        st, vis = [0], {0}
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in vis:
                    vis.add(w); st.append(w)
        if len(vis) != n:
            continue
        deg = [len(adj[v]) for v in range(n)]
        kap = connectivity(n, e)
        g = gap_profile(n, e)
        tot = sum(b - a for a, b in g)
        mx = max((b - a for a, b in g), default=0.0)
        rows.append((name, n, len(e), min(deg), max(deg), kap, len(g), tot, mx))
        print(f"{name:>22}{n:>5}{len(e):>5}{min(deg):>5}{max(deg):>5}{kap:>6}"
              f"{len(g):>6}{tot:>9.4f}{mx:>9.4f}", flush=True)
        with open(CKPT + '.tmp', 'w') as f:
            f.write(f"{len(rows)} graphs, {time.time()-t0:.0f}s\n")
        os.replace(CKPT + '.tmp', CKPT)

    print(f"\n{len(rows)} graphs, {time.time()-t0:.0f}s\n")

    def summarise(key, label):
        print(f"  by {label}:")
        print(f"{'':>6}{'#':>5}{'mean totgap':>13}{'max totgap':>12}{'mean maxgap':>13}")
        for v in sorted({r[key] for r in rows}):
            sel = [r for r in rows if r[key] == v]
            print(f"{v:>6}{len(sel):>5}{np.mean([s[7] for s in sel]):>13.4f}"
                  f"{max(s[7] for s in sel):>12.4f}{np.mean([s[8] for s in sel]):>13.4f}")
        print()
    summarise(3, "minimum degree delta")
    summarise(5, "vertex connectivity kappa")

    print("  cross-tab, mean total gap width (rows delta, cols kappa):")
    ds = sorted({r[3] for r in rows}); ks = sorted({r[5] for r in rows})
    print("      " + "".join(f"{k:>9}" for k in ks))
    for d in ds:
        line = f"{d:>6}"
        for k in ks:
            sel = [r for r in rows if r[3] == d and r[5] == k]
            line += f"{np.mean([s[7] for s in sel]):>9.4f}" if sel else f"{'-':>9}"
        print(line)

    lo = [r for r in rows if r[3] <= 2]
    hi = [r for r in rows if r[3] >= 3]
    print(f"\n  delta<=2: {len(lo)} graphs, mean total gap {np.mean([r[7] for r in lo]):.4f}, "
          f"max {max((r[7] for r in lo), default=0):.4f}")
    if hi:
        print(f"  delta>=3: {len(hi)} graphs, mean total gap {np.mean([r[7] for r in hi]):.4f}, "
              f"max {max(r[7] for r in hi):.4f}")
        print("\n  P1 holds" if np.mean([r[7] for r in hi]) < 0.4 * np.mean([r[7] for r in lo])
              else "\n  P1 FAILS: delta>=3 keeps its gaps")
    return 0


if __name__ == '__main__':
    sys.exit(main())
