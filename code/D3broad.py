"""D3 without a construction: broad random search at minimum degree three.

Every engine aimed at D3 so far has been CUT-BASED. The two-hub engine and the 102-graph sweep
used separating pairs; D1cut and D1cut_adv used a cut vertex, which is what makes mu_H divide
mu_G and lets a root be placed by choosing a block. Both are now exhausted -- 468 configurations
between them, clean on the corrected instrument -- and both share an assumption: that a
counterexample must localize a root on a piece of the graph that a small separator cuts off.

Hall's does. But nothing says it has to, and a route that assumes it cannot find a counterexample
that does not. This searches with no construction at all: random graphs at minimum degree three,
with degree sequences deliberately SPREAD, since gaps in spec(T) need degree inhomogeneity --
Kesten gives the regular tree no gaps at all, so a regular graph can never refute anything here.

WHAT IS TESTED. For each graph, every positive root of mu_G, against membership in spec(T). A
root outside spec(T) refutes Conjecture 10 at d = 1, and at minimum degree three it refutes D3.
The instrument is the one arrived at the hard way earlier today:

  * roots by FACTORING mu_G and solving each irreducible factor, since np.roots at a
    multiplicity-m root errs by ~eps^(1/m), which at m = 4 is 1e-4 and is enough to move a root
    off a spectral atom and into an adjacent gap;
  * membership POINTWISE by the Angel-Friedman-Hoory ratio system, not by scanning a grid whose
    cell is as wide as the gap being looked for;
  * every `outside` verdict gated by the DENSITY OF STATES, because the ratio system converges
    below one at a spectral atom and reports `outside` there although the point is in the
    spectrum. The cavity iteration is initialised on the physical branch, Im g < 0; the other
    branch returns negative densities, which is how that bug announced itself.

FROZEN BEFORE THE DATA:
  P22. No graph found by this search has a root of mu_G outside spec(T).

A hit refutes D3 and is re-checked in exact arithmetic before it is reported anywhere. Absence of
a hit is weaker evidence than the engineered searches were, since random graphs are not adversarial,
but it covers the case those searches structurally could not: a counterexample with no small
separator at all.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import itertools
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twocut import mu_of, x
from gapscale import setup, rho_at
from D1cut_adv import dos_at, outside_spectrum
import quickmode

BUDGET_S = 2700.0


def spread_graph(n, rng, nhub, hubdeg):
    """Random connected graph, minimum degree 3, with `nhub` deliberately high-degree vertices."""
    edges = set()
    # a random 3-regular-ish backbone: random perfect matchings union
    for _ in range(3):
        perm = list(rng.permutation(n))
        for i in range(0, n - 1, 2):
            a, b = perm[i], perm[i + 1]
            if a != b:
                edges.add((min(a, b), max(a, b)))
    # hubs
    for h in range(nhub):
        targets = rng.choice([v for v in range(n) if v != h], size=min(hubdeg, n - 1),
                             replace=False)
        for t in targets:
            edges.add((min(h, int(t)), max(h, int(t))))
    deg = {v: 0 for v in range(n)}
    for (a, b) in edges:
        deg[a] += 1; deg[b] += 1
    # repair minimum degree three
    for v in range(n):
        while deg[v] < 3:
            u = int(rng.integers(n))
            if u == v or (min(u, v), max(u, v)) in edges:
                continue
            edges.add((min(u, v), max(u, v))); deg[u] += 1; deg[v] += 1
    return sorted(edges)


def connected(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    seen = {0}; stack = [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w); stack.append(w)
    return len(seen) == n


def has_cut_vertex(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    for v in range(n):
        rem = [u for u in range(n) if u != v]
        if not rem:
            continue
        seen = {rem[0]}; stack = [rem[0]]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w != v and w not in seen:
                    seen.add(w); stack.append(w)
        if len(seen) != len(rem):
            return True
    return False


def mu_roots(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    poly = sp.expand(mu_of(adj, set(range(n))))
    out = set()
    for (f, _m) in sp.factor_list(poly)[1]:
        for r in sp.Poly(f, x).nroots(n=30):
            if abs(sp.im(r)) < 1e-20:
                val = float(sp.re(r))
                if val > 1e-9:
                    out.add(round(val, 12))
    return sorted(out)


def main():
    t0 = time.time()
    rng = np.random.default_rng(20260825)
    print("P22 (frozen): no graph found by this search has a root of mu_G outside spec(T).\n")
    print("No construction: random graphs at delta >= 3 with spread degree sequences, no cut")
    print("vertex, tested pointwise with the DOS gate.\n")
    print(f"{'n':>4}{'|E|':>5}{'degrees':>22}{'cutv':>6}{'roots':>7}{'min AFH rho':>13}"
          f"{'verdict':>12}")

    viol, amb, tested = [], [], 0
    for n in quickmode.few((10, 12, 14, 16, 18), 2):
        for trial in range(10 if quickmode.QUICK else 60):
            if time.time() - t0 > BUDGET_S:
                break
            nhub = int(rng.integers(1, 4))
            hubdeg = int(rng.integers(max(4, n // 2), n))
            E = spread_graph(n, rng, nhub, hubdeg)
            if not connected(n, E):
                continue
            deg = [0] * n
            for a, b in E:
                deg[a] += 1; deg[b] += 1
            if min(deg) < 3 or max(deg) - min(deg) < 3:      # spread is required for gaps
                continue
            cutv = has_cut_vertex(n, E)
            if cutv:
                continue                                     # this route is the non-cut one
            roots = mu_roots(n, E)
            if not roots:
                continue
            B, M = setup(n, E)
            rho_top = 2.0 * math.sqrt(max(deg) - 1)
            cand = [r for r in roots if r < rho_top]
            tested += 1
            hit = a_ = False
            best = None
            for r in cand:
                verdict, rr = outside_spectrum(r, B, M, n, E)
                if rr is not None and (best is None or abs(rr - 1.0) < best):
                    best = abs(rr - 1.0)
                if verdict is True:
                    viol.append((n, tuple(sorted(deg)), r, rr)); hit = True
                elif verdict is None:
                    amb.append((n, r, rr)); a_ = True
            if tested % 12 == 1 or hit or a_:
                dtxt = f"{min(deg)}..{max(deg)}"
                print(f"{n:>4}{len(E):>5}{dtxt:>22}{str(cutv):>6}{len(cand):>7}"
                      f"{(best if best is not None else float('nan')):>13.5f}"
                      f"{('REFUTES D3' if hit else ('ambiguous' if a_ else 'clean')):>12}")

    print(f"\n  graphs tested: {tested}   violations: {len(viol)}   ambiguous: {len(amb)}")
    if viol:
        print("  P22 IS FALSE and D3 WITH IT:")
        for (n, dg, r, rr) in viol[:10]:
            print(f"    n={n}, degrees={dg}, root {r:.9f}, AFH decay {rr}")
        print("  RE-CHECK in exact arithmetic before this leaves the machine.")
    else:
        print("  P22 holds. D3 survives a search that assumes no separator at all, which is the")
        print("  case both cut engines structurally could not reach.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
