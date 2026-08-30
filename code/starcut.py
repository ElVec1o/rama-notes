"""SUPERSEDED. This script's spectral verdict cannot be trusted.

It uses the density-of-states and ratio-system machinery of code/d3_counterexample.py, whose
spectral verdict is retracted: in the graphs built here the branch union is a theta-Aomoto subset,
so the root is an EIGENVALUE of the universal cover and lies IN spec(T_G), not outside it. The
graph constructions, the two-cut identity and the gap scans are still correct; only the conclusion
drawn about spec(T_G) is wrong. See code/aomoto_obstruction.py. Conjectures D3 and C2 are OPEN.
"""

"""Hall's divisor, rebuilt under minimum degree three.

Hall's counterexample has matching polynomial x^21 (x^4-11x^2+25)^4 (x^2-5)(x^2-11), and the root
that violates the covering bound is sqrt5, the top matching root of the star K_{1,5}, whose matching
polynomial is x^4(x^2-5). So the engine is a STAR divisor.

That matters for D3, because a star's leaves have degree one IN H however large their degree is IN G.
Minimum degree three constrains G, not the divisor, so it does not forbid a star divisor on its face.
code/mindeg3.py and code/mindeg3adv.py sweep ladders, prisms, K_{3,q} and asymmetric ladders, none of
which is a star; they never put Hall's actual shape under the hypothesis.

THE CONSTRUCTION. Take the branch to be the star K_{1,m} and anchor EVERY leaf to both hubs. In the
assembled graph a leaf then has degree 1 + 2 = 3 and the centre has degree m, so G has minimum degree
three while the divisor is exactly Hall's star:

    A = mu_{K_{1,m}} = x^{m-1} (x^2 - m),   top root sqrt(m),   and A^{p-2} | mu_G.

This is the closest a minimum-degree-three graph can come to Hall's counterexample inside the two-cut
family. If D3 has a soft spot, it is here.

Zero is not a violation. The paper records the biregular cover spectrum as {0} u +-[|s-t|, s+t], an
isolated point at the origin together with two bands, so the gap is the OPEN interval (0, |s-t|) and
the root of A at the origin, present whenever the branch has an odd number of vertices, lies in
spec(T). Only the nonzero roots are tested below.

FROZEN BEFORE THE DATA:
  P62. (a) The two-cut identity holds on star branches, so A^(p-2) really divides mu_G here.
       (b) No nonzero root of A reaches a gap of spec(T_G), for 3 <= m <= 8 and 3 <= p <= 8.
       (c) The margin at star branches is TIGHTER than the -0.12 to -0.29 the ladders and prisms
           gave in code/mindeg3adv.py, since this is Hall's shape rather than a generic one: the
           worst approach here exceeds -0.12.

The reason (b) is predicted rather than (b) negated: anchoring a leaf to both hubs is what buys the
third edge, and it also puts that leaf on many four-cycles through the hubs. A leaf of H becomes a
degree-three vertex of G lying on short cycles, and short cycles are what fill in a spectral gap.
The claim of D3 is that this trade is forced, that one cannot have the third edge without the
cycles. If (b) fails, D3 is dead and so is the minimum-degree repair of Conjecture 10.

FALSIFICATION. One (m, p) with sqrt(m), or any other nonzero root of A, strictly inside a gap of
spec(T_G) at minimum degree three. That is a counterexample of Hall's own type satisfying the
hypothesis meant to exclude it.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from twocut import branch_data, bracket, assemble, mu_of, x
from gapscale import setup, rho_at, gap_profile, connectivity
from mindeg3adv import pos_roots, margin_of, refine
import quickmode

BUDGET = 1200.0
CKPT = quickmode.ckpt('private/starcut_ckpt.txt')
MIN_GAP = 0.05
NMAX = 62


def br_star(m):
    """K_{1,m} with centre 0. Every leaf is anchored to both hubs, which is the cheapest way to
    give a leaf degree three without adding an edge inside the branch and so without changing A."""
    e = [(0, i) for i in range(1, m + 1)]
    leaves = list(range(1, m + 1))
    return m + 1, e, leaves, leaves


def br_dstar(m):
    """Double star: two adjacent centres with m leaves each, all leaves anchored to both hubs.
    A = mu of the double star, whose top root exceeds sqrt(m)."""
    e = [(0, 1)]
    leaves = []
    v = 2
    for _ in range(m):
        e.append((0, v)); leaves.append(v); v += 1
    for _ in range(m):
        e.append((1, v)); leaves.append(v); v += 1
    return v, e, leaves, leaves


def br_star_c(m):
    """K_{1,m} again, but the centre is anchored to one hub as well. Same A, different assembled
    spectrum: it separates the divisor from the graph it sits in."""
    e = [(0, i) for i in range(1, m + 1)]
    leaves = list(range(1, m + 1))
    return m + 1, e, leaves, leaves + [0]


FAMILIES = ([(f"star m={m}", br_star(m)) for m in range(3, 9)]
            + [(f"dstar m={m}", br_dstar(m)) for m in range(2, 6)]
            + [(f"starC m={m}", br_star_c(m)) for m in range(3, 9)])


def selfcheck():
    ok = True
    for name, (nb, be, Su, Sv) in (FAMILIES[0], FAMILIES[7], FAMILIES[11]):
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
    print("P62 (frozen): Hall's star divisor, rebuilt so that the assembled graph has minimum")
    print("degree three. If D3 has a soft spot this is where it is.\n")
    print("self-check of the two-cut identity on star branches:", flush=True)
    if not selfcheck():
        print("IDENTITY WRONG on these branches - nothing below is meaningful.")
        return 1
    print()

    print(f"{'branch':>12}{'p':>3}{'n':>5}{'dmin':>5}{'kappa':>6}{'#gaps':>6}{'maxgap':>8}"
          f"{'topA':>8}{'worstA':>9}{'worstBr':>9}{'verdict':>11}", flush=True)
    t0 = time.time()
    tested = kept = 0
    hits = []
    worst_overall = None
    for name, (nb, be, Su, Sv) in quickmode.few(FAMILIES, 2):
        if time.time() - t0 > BUDGET:
            print("  [budget reached]"); break
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        rootsA = pos_roots(A)
        for p in range(3, 9):
            n = 2 + p * nb
            if n > NMAX or time.time() - t0 > BUDGET:
                continue
            edges = assemble(nb, be, Su, Sv, p)[1]
            adj = {i: set() for i in range(n)}
            for a, b in edges:
                adj[a].add(b); adj[b].add(a)
            deg = [len(adj[i]) for i in range(n)]
            if min(deg) < 3:
                continue
            tested += 1
            gaps = [t for t in gap_profile(n, edges) if t[1] - t[0] >= MIN_GAP]
            topA = max(rootsA) if rootsA else 0.0
            if not gaps:
                print(f"{name:>12}{p:>3}{n:>5}{min(deg):>5}{connectivity(n, edges):>6}"
                      f"{0:>6}{0.0:>8.3f}{topA:>8.4f}{'-':>9}{'-':>9}{'no gap':>11}", flush=True)
                continue
            kept += 1
            kap = connectivity(n, edges)
            B, M = setup(n, edges)
            rootsBr = pos_roots(bracket(A, Bu, Bv, D, p))
            wA = max((margin_of(th, gaps) for th in rootsA), default=-9.9)
            wB = max((margin_of(th, gaps) for th in rootsBr), default=-9.9)
            bad = []
            for tag, rts in (('A', rootsA), ('bracket', rootsBr)):
                for th in rts:
                    d = margin_of(th, gaps)
                    if d is not None and d > 0 and refine(th, B, M):
                        bad.append((tag, th, d))
            mx = max(t[1] - t[0] for t in gaps)
            w = max(wA, wB)
            worst_overall = w if worst_overall is None else max(worst_overall, w)
            print(f"{name:>12}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{len(gaps):>6}{mx:>8.3f}"
                  f"{topA:>8.4f}{wA:>9.4f}{wB:>9.4f}"
                  f"{('VIOLATION' if bad else 'clean'):>11}", flush=True)
            if bad:
                hits.append((name, p, n, kap, bad))
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"{name} p={p} tested={tested} withgap={kept} hits={len(hits)}\n")
            os.replace(CKPT + '.tmp', CKPT)

    print(f"\n{tested} star-divisor graphs of minimum degree three, {kept} with a gap of width "
          f">= {MIN_GAP}.  {time.time()-t0:.0f}s")
    if hits:
        print("\nD3 IS FALSE, and it fails on Hall's own shape:")
        for nm, p, n, kap, bad in hits:
            for tag, th, d in bad:
                print(f"  {nm} p={p} n={n} kappa={kap} factor={tag} "
                      f"theta={th:.6f} depth={d:.6f}")
        print("  The minimum-degree repair of Conjecture 10 does not survive the star divisor,")
        print("  and P62(b) is refuted.")
    elif worst_overall is not None:
        print(f"\n  worst approach on star branches: {worst_overall:.4f}")
        print("  P62(b) HOLDS: the star divisor does not reach a gap once every leaf carries a")
        print("  third edge. P62(c) predicted this margin would be tighter than -0.12; compare.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
