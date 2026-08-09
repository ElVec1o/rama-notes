"""The discriminating experiment: is it connectivity, or the minimum degree behind it?

Every counterexample to Conjecture 10 ever found has minimum degree at most two.  Hall's has
leaves, the 31-vertex graph has degree-2 vertices, and so do all three 2-cut graphs that killed
C1.  Meanwhile 3-connectedness forces minimum degree three, so the C2 evidence is consistent
with two quite different explanations and cannot tell them apart:

  C2. every 3-connected graph satisfies Conjecture 10
  D3. every graph of minimum degree at least three satisfies Conjecture 10

D3 implies C2, since kappa >= 3 forces delta >= 3, and D3 is by far the more natural
hypothesis: it is a local condition, and it would say connectivity was never the point.

THE DISCRIMINATING CASE is delta >= 3 together with a SEPARATING PAIR, that is kappa = 2.  C2
says nothing about those graphs.  D3 says they are clean.  And they are exactly where the
engine that killed C1 lives, so this is a fair fight rather than a fishing trip:

  mu_G = A^{p-2} ( x^2 A^2 - p x (Bu + Bv) A + p D A + p(p-1) Bu Bv ),

with two hubs and p branches attached to both.  The C1 counterexamples used branches that had
degree-2 vertices, K_{2,q} with a tail.  Here the same engine is run with branches whose every
vertex has degree at least three, so the only thing that changes is the minimum degree.

  * ladder branches, anchored at both ends of both rails, so all four corners reach a hub;
  * K_{3,q} branches with two of the three degree-q vertices anchored and the third internal.

If a violation appears, D3 is false and connectivity was doing real work.  If none does, D3 is
the statement and C2 is a corollary of it, which would mean the whole connectivity story was a
confound.

FROZEN BEFORE THE DATA: D3.

The 2-cut bracket is checked against a brute-force matching polynomial for each branch type
before use, since the multi-vertex anchor sets are a case the earlier check did not cover.
Every candidate root is tested against spec(T) by the Angel-Friedman-Hoory decay rate, and
every graph's vertex connectivity is computed exactly by Menger.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twocut import branch_data, bracket, assemble, mu_of, x
from gapscale import setup, rho_at, gap_profile, connectivity

BUDGET = 1500.0
CKPT = 'private/mindeg3_ckpt.txt'
MIN_GAP = 0.05


# ------------------------------------------------------------------ delta>=3 branches
def br_ladder(L):
    """ladder on 2L vertices; both ends of both rails are anchored, so every vertex of the
    assembled graph has degree at least three."""
    top = list(range(L))
    bot = list(range(L, 2 * L))
    e = []
    for i in range(L - 1):
        e.append((top[i], top[i + 1])); e.append((bot[i], bot[i + 1]))
    for i in range(L):
        e.append((top[i], bot[i]))
    return 2 * L, e, [top[0], bot[0]], [top[-1], bot[-1]]


def br_K3q(q):
    """K_{3,q}: two of the degree-q vertices anchored, the third left internal."""
    e = []
    for a in range(3):
        for m in range(3, 3 + q):
            e.append((a, m))
    return 3 + q, e, [0], [1]


def br_prism(L):
    """circular ladder (prism) with one rung's ends anchored: 3-regular inside."""
    top = list(range(L)); bot = list(range(L, 2 * L))
    e = []
    for i in range(L):
        e.append((top[i], top[(i + 1) % L])); e.append((bot[i], bot[(i + 1) % L]))
        e.append((top[i], bot[i]))
    return 2 * L, e, [top[0]], [top[L // 2]]


def br_ladder_mid(L):
    """ladder anchored at one end and in the middle: an asymmetric resonator."""
    top = list(range(L)); bot = list(range(L, 2 * L))
    e = []
    for i in range(L - 1):
        e.append((top[i], top[i + 1])); e.append((bot[i], bot[i + 1]))
    for i in range(L):
        e.append((top[i], bot[i]))
    return 2 * L, e, [top[0], bot[0]], [top[-1], bot[-1], top[L // 2]]


FAMILIES = ([(f"ladder L={L}", br_ladder(L)) for L in range(2, 9)]
            + [(f"K3,{q}", br_K3q(q)) for q in range(3, 8)]
            + [(f"prism L={L}", br_prism(L)) for L in range(3, 8)]
            + [(f"ladderM L={L}", br_ladder_mid(L)) for L in range(3, 8)])


def selfcheck():
    ok = True
    for name, (nb, be, Su, Sv) in (FAMILIES[0], FAMILIES[8], FAMILIES[13], FAMILIES[18]):
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        for p in (2, 3):
            n, edges = assemble(nb, be, Su, Sv, p)
            adj = {i: set() for i in range(n)}
            for a, b in edges:
                adj[a].add(b); adj[b].add(a)
            good = sp.expand(A ** (p - 2) * bracket(A, Bu, Bv, D, p)
                             - mu_of(adj, set(range(n)))) == 0
            ok = ok and good
            print(f"  {name:>12} p={p} n={n:>3}: {'OK' if good else 'MISMATCH'}", flush=True)
    return ok


def main():
    print("D3 (frozen): minimum degree >= 3 suffices for Conjecture 10.")
    print("Testing the case C2 cannot see: delta >= 3 WITH a separating pair.\n")
    print("self-check of the 2-cut identity on multi-anchor branches:", flush=True)
    if not selfcheck():
        print("IDENTITY WRONG - nothing below is meaningful.")
        return 1
    print()
    print(f"{'branch':>12}{'p':>3}{'n':>5}{'dmin':>5}{'dmax':>5}{'kappa':>6}"
          f"{'#gaps':>6}{'maxgap':>8}{'verdict':>11}", flush=True)
    t0 = time.time()
    tested = kept = 0
    hits = []
    for name, (nb, be, Su, Sv) in FAMILIES:
        if time.time() - t0 > BUDGET:
            print("  [budget reached]"); break
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        for p in range(2, 10):
            n = 2 + p * nb
            if n > 58 or time.time() - t0 > BUDGET:
                continue
            edges = assemble(nb, be, Su, Sv, p)[1]
            adj = {i: set() for i in range(n)}
            for a, b in edges:
                adj[a].add(b); adj[b].add(a)
            deg = [len(adj[i]) for i in range(n)]
            if min(deg) < 3:
                continue
            kap = connectivity(n, edges)
            tested += 1
            g = [t for t in gap_profile(n, edges) if t[1] - t[0] >= MIN_GAP]
            if not g:
                print(f"{name:>12}{p:>3}{n:>5}{min(deg):>5}{max(deg):>5}{kap:>6}"
                      f"{0:>6}{0.0:>8.3f}{'no gap':>11}", flush=True)
                continue
            kept += 1
            F = bracket(A, Bu, Bv, D, p)
            co = sp.Poly(sp.expand(F), x).all_coeffs()
            while co and co[-1] == 0:
                co.pop()
            roots = []
            if len(co) >= 2:
                try:
                    roots = [float(sp.re(r)) for r in
                             sp.Poly(co, x).nroots(n=20, maxsteps=3000)
                             if abs(sp.im(r)) < 1e-10 and sp.re(r) > 1e-9]
                except Exception:
                    roots = []
            B, M = setup(n, edges)
            found = None
            for th in roots:
                for (lo, hi) in g:
                    if lo < th < hi:
                        r = rho_at(th, B, M)
                        if r is not None and r < 1:
                            found = (th, min(th - lo, hi - th), r)
            mx = max(t[1] - t[0] for t in g)
            print(f"{name:>12}{p:>3}{n:>5}{min(deg):>5}{max(deg):>5}{kap:>6}"
                  f"{len(g):>6}{mx:>8.3f}{('VIOLATION' if found else 'clean'):>11}", flush=True)
            if found:
                hits.append((name, p, n, kap, found))
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"{name} p={p} tested={tested} withgap={kept} hits={len(hits)}\n")
            os.replace(CKPT + '.tmp', CKPT)

    print(f"\n{tested} graphs with delta>=3, of which {kept} have a gap of width >= {MIN_GAP}."
          f"  {time.time()-t0:.0f}s")
    k2 = [h for h in hits if h[3] <= 2]
    if k2:
        print(f"\nD3 IS FALSE, and connectivity is doing real work: {len(k2)} counterexamples "
              "with minimum degree three and a separating pair.")
        for nm, p, n, kap, (th, df, r) in k2:
            print(f"  {nm} p={p} n={n} kappa={kap} theta={th:.6f} defect={df:.6f} rho={r:.6f}")
    elif hits:
        print(f"\n{len(hits)} violations, but none at kappa <= 2; inconclusive.")
    else:
        print("\nD3 survives.  The 2-cut engine that killed C1 does NOT fire once the branches "
              "have minimum degree three, so minimum degree, not connectivity, is what the "
              "evidence is really about.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
