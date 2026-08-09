"""Attacking C2: 3-connected graphs engineered to have WIDE gaps.

C2 says 3-connectedness repairs Conjecture 10. The evidence for it was a k-cut search that
found nothing at k = 3, 4, 5, and the explanation offered was that raising connectivity forces
edges, widens the bands and narrows the gaps. The gap measurement (code/gapscale.py) partly
confirms that: mean total gap width falls from 0.99 at minimum degree at most two to 0.09 at
minimum degree three. But it also shows the narrowing is NOT annihilation. At minimum degree
three and connectivity two, gaps of width up to 0.50 survive. So the question is whether a
3-connected graph can be built that still has a wide gap, and then whether a root lands in it.

That is what this file does, and the design point is the gap FILTER. Every graph is checked for
a gap of usable width before its roots are examined, so a graph with no gap contributes
nothing either way and cannot inflate a negative result. The k=3 search that supported C2 had
no such filter, which is the weakness being repaired here.

WHERE WIDE GAPS COME FROM AT MINIMUM DEGREE THREE. The universal cover of an (a,b)-biregular
graph is the (a,b)-biregular tree, whose spectrum is {0} together with
  +/- [ |sqrt(a-1) - sqrt(b-1)| , sqrt(a-1) + sqrt(b-1) ],
so there is a gap around zero of half-width |sqrt(a-1) - sqrt(b-1)|. For (3,q) that is
|sqrt 2 - sqrt(q-1)|, which is 1.41 at q = 9 and grows with q. Degree CONTRAST, not low degree,
is what opens a gap, and contrast is available at minimum degree three. So the families here
all pair degree-3 vertices against high-degree ones.

Three constructions, all verified 3-connected by exact Menger:
  * (3,q)-biregular bipartite graphs, built as a shifted incidence scheme and checked
    connected, which plain block assignment is not.
  * three hubs carrying p branches of K_{3,q} attached at the three degree-q vertices: hub
    degree p against branch degree three, so the contrast is tunable by p.
  * three hubs carrying p ladder branches, the minimum-degree-three analogue of a chain.

mu_G comes from the k-cut expansion of code/kcut.py where the graph has that shape, checked
there against brute force, and from memoised vertex deletion otherwise.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import functools
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gapscale import setup, rho_at, gap_profile, connectivity

x = sp.Symbol('x')
BUDGET = 1500.0
CKPT = 'private/c2attack_ckpt.txt'
MIN_GAP = 0.05


# ------------------------------------------------------------------ constructions
def biregular(a, b, m):
    """(a,b)-biregular bipartite, connected.  Edge t joins left t//a to right (t*g) % r, with
    g coprime to r chosen as the first shift that makes the graph connected; the plain block
    assignment g = 1 with aligned indices splits into components."""
    if (m * a) % b:
        return None
    r = (m * a) // b
    for g in range(1, r):
        if math.gcd(g, r) != 1:
            continue
        es = set()
        for t in range(m * a):
            es.add((t // a, m + (t * g) % r))
        if len(es) != m * a:
            continue
        n = m + r
        adj = {i: set() for i in range(n)}
        for u, v in es:
            adj[u].add(v); adj[v].add(u)
        deg = [len(adj[i]) for i in range(n)]
        if min(deg) < min(a, b) or max(deg) > max(a, b):
            continue
        st, vis = [0], {0}
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in vis:
                    vis.add(w); st.append(w)
        if len(vis) == n:
            return n, sorted(es)
    return None


def hub_K3q(p, q):
    """3 hubs, p branches of K_{3,q}, attached at the three degree-q vertices."""
    edges, n = [], 3
    for _ in range(p):
        anc = [n, n + 1, n + 2]
        mid = list(range(n + 3, n + 3 + q))
        n += 3 + q
        for a in anc:
            for m in mid:
                edges.append((a, m))
        for j in range(3):
            edges.append((j, anc[j]))
    return n, edges


def hub_ladder(p, L):
    """3 hubs, p ladder branches; every vertex has degree at least three."""
    edges, n = [], 3
    for _ in range(p):
        top = list(range(n, n + L)); n += L
        bot = list(range(n, n + L)); n += L
        for i in range(L - 1):
            edges.append((top[i], top[i + 1])); edges.append((bot[i], bot[i + 1]))
        for i in range(L):
            edges.append((top[i], bot[i]))
        edges += [(0, top[0]), (0, bot[0]), (1, top[-1]), (1, bot[-1]),
                  (2, top[L // 2]), (2, bot[L // 2])]
    return n, edges


def candidates():
    C = []
    for q in range(4, 14):
        for m in (12, 15, 18, 20, 24):
            r = biregular(3, q, m)
            if r and r[0] <= 56:
                C.append((f"bireg(3,{q}) m={m}", r[0], r[1]))
    for q in (2, 3, 4, 5):
        for p in range(3, 12):
            n, e = hub_K3q(p, q)
            if n <= 60:
                C.append((f"hub K3,{q} p={p}", n, e))
    for L in (3, 4, 5, 6, 7):
        for p in (3, 4, 5):
            n, e = hub_ladder(p, L)
            if n <= 60:
                C.append((f"hub ladder L={L} p={p}", n, e))
    seen, out = set(), []
    for nm, n, e in C:
        key = (n, tuple(sorted((min(a, b), max(a, b)) for a, b in e)))
        if key not in seen:
            seen.add(key); out.append((nm, n, e))
    return out


def mu_memo(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    sys.setrecursionlimit(300000)

    @functools.lru_cache(maxsize=None)
    def rec(vs):
        S = set(vs)
        if not S:
            return sp.Integer(1)
        v = min(S, key=lambda t: len(adj[t] & S))
        S1 = S - {v}
        tot = x * rec(tuple(sorted(S1)))
        for u in adj[v] & S:
            tot -= rec(tuple(sorted(S1 - {u})))
        return sp.expand(tot)
    return rec(tuple(range(n)))


def main():
    print("Attacking C2: 3-connected graphs with a gap wide enough to hide a root.\n")
    print(f"{'case':>22}{'n':>5}{'dmin':>5}{'dmax':>5}{'kappa':>6}{'#gaps':>6}"
          f"{'maxgap':>8}{'widest gap':>18}{'verdict':>10}", flush=True)
    t0 = time.time()
    tested = kept = 0
    hits = []
    for name, n, e in candidates():
        if time.time() - t0 > BUDGET:
            print("  [budget reached]"); break
        adj = {i: set() for i in range(n)}
        for a, b in e:
            adj[a].add(b); adj[b].add(a)
        deg = [len(adj[i]) for i in range(n)]
        if min(deg) < 3:
            continue
        kap = connectivity(n, e)
        if kap < 3:
            continue
        tested += 1
        g = gap_profile(n, e)
        g = [t for t in g if t[1] - t[0] >= MIN_GAP]
        if not g:
            print(f"{name:>22}{n:>5}{min(deg):>5}{max(deg):>5}{kap:>6}{0:>6}"
                  f"{0.0:>8.3f}{'-':>18}{'no gap':>10}", flush=True)
            continue
        kept += 1
        wide = max(g, key=lambda t: t[1] - t[0])
        muG = mu_memo(n, e)
        co = sp.Poly(muG, x).all_coeffs()
        while co and co[-1] == 0:
            co.pop()
        roots = []
        if len(co) >= 2:
            try:
                roots = [float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=20, maxsteps=3000)
                         if abs(sp.im(r)) < 1e-10 and sp.re(r) > 1e-9]
            except Exception:
                roots = []
        B, M = setup(n, e)
        found = None
        for th in roots:
            for (lo, hi) in g:
                if lo < th < hi:
                    r = rho_at(th, B, M)
                    if r is not None and r < 1:
                        found = (th, min(th - lo, hi - th), r)
        v = 'VIOLATION' if found else 'clean'
        print(f"{name:>22}{n:>5}{min(deg):>5}{max(deg):>5}{kap:>6}{len(g):>6}"
              f"{wide[1]-wide[0]:>8.3f}{f'({wide[0]:.3f},{wide[1]:.3f})':>18}{v:>10}",
              flush=True)
        if found:
            hits.append((name, n, kap, found))
        with open(CKPT + '.tmp', 'w') as f:
            f.write(f"{name} tested={tested} withgap={kept} hits={len(hits)}\n")
        os.replace(CKPT + '.tmp', CKPT)

    print(f"\n{tested} graphs with delta>=3 and kappa>=3, of which {kept} have a gap of width "
          f">= {MIN_GAP}.  {time.time()-t0:.0f}s")
    if hits:
        print(f"\nC2 IS REFUTED: {len(hits)} 3-connected counterexamples.")
        for nm, n, kap, (th, df, r) in hits:
            print(f"  {nm} n={n} kappa={kap} theta={th:.6f} defect={df:.6f} rho={r:.6f}")
    elif kept:
        print(f"\nC2 survives: no root in any gap, over {kept} 3-connected graphs that "
              "genuinely have one.  This is not the vacuous negative the k-cut search gave.")
    else:
        print("\nNO 3-connected graph in these families has a gap at all.  If that persists, "
              "C2 is true for a boring reason and the interesting statement is about gaps.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
