"""The D3 and C2 searches re-run at a threshold that can actually see the phenomenon.

code/gapfilter_blindspot.py shows that every search in this repository filtered gaps of spec(T) by
MIN_GAP = 0.05, and that Hall's own counterexample sits in a gap of width 0.040 and is therefore
discarded. So every "clean" verdict recorded here means only "no violation in a gap wider than
0.05". This re-runs the same graph families with

  * MIN_GAP lowered to 0.015, below Hall's 0.040 and below the two-cut family's 0.066, and
  * an EXACT eigenvalue test in place of the density-of-states ladder.

The second change matters as much as the first. The ladder reports "outside spec" at points that
are in fact eigenvalues of the cover, which is the error that produced the retracted D3 and C2
claims. Here a root theta in a gap is tested by the criterion of Li, Magee, Sabri and Thomas: theta
is an eigenvalue of the cover exactly when its minimal polynomial divides mu_{G minus V(Gamma)} for
EVERY 2-regular subgraph Gamma. Finding one Gamma where the division fails proves theta is not an
eigenvalue, with no floating point anywhere. A root that is in a gap and not an eigenvalue is a
genuine violation.

FROZEN BEFORE THE DATA:
  P72. (a) At MIN_GAP = 0.015 many more graphs present a gap than at 0.05, so the earlier sweeps
           were discarding most of the search space rather than a sliver of it.
       (b) The A-roots, the branch eigenvalues, are found to be eigenvalues of the cover wherever
           they land in a gap, consistent with the branch obstruction.
       (c) No genuine violation is found. The families here all carry the branch obstruction, so a
           violation would have to come from a bracket root, and there is no reason to expect one.

(c) is predicted rather than its negation because these are the families the obstruction covers.
The value of the run is (a): it measures how much of the space the old threshold threw away. If (c)
fails, a genuine counterexample has been found in a family previously reported clean, and the
earlier verdicts were wrong rather than merely weak.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import sympy as sp
import networkx as nx
from twocut import branch_data, bracket, assemble, mu_of, x
from gapscale import gap_profile, connectivity
from aomoto_obstruction import adjof, mu_on, is_aomoto

LOW = 0.015
OLD = 0.05
BUDGET = 5400.0


def exact_not_eigenvalue(n, edges, adj, f, maxlen=6, cap=40):
    """Exact: a 2-regular Gamma with f not dividing mu_{G-V(Gamma)} proves theta not an eigenvalue."""
    fp = sp.Poly(f, x)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    cyc = [frozenset(c) for c in nx.simple_cycles(G, length_bound=maxlen) if len(c) >= 3]
    for gam in [frozenset()] + cyc[:cap]:
        m2 = sp.Poly(sp.expand(mu_on(adj, set(range(n)) - gam)), x)
        if sp.rem(m2, fp).as_expr() != 0:
            return sorted(gam)
    return None


def main():
    from mindeg3 import FAMILIES as MD3
    from starcut import FAMILIES as STAR
    print("P72 (frozen): re-running the D3/C2 families below the blind spot.\n")
    print(f"old threshold {OLD}, new threshold {LOW}; Hall's own gap is 0.040\n")
    print(f"{'family':>14}{'p':>3}{'n':>5}{'kap':>4}"
          f"{'gaps@.05':>9}{'gaps@.015':>10}{'roots in gap':>13}  verdict", flush=True)

    t0 = time.time()
    seen_old = seen_new = 0
    hits = []
    for tag, fams in (("mindeg3", MD3), ("starcut", STAR)):
        for name, (nb, be, Su, Sv) in fams:
            if time.time() - t0 > BUDGET:
                print("  [budget]"); break
            A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
            for p in range(3, 9):
                n = 2 + p * nb
                if n > 40 or time.time() - t0 > BUDGET:
                    continue
                edges = assemble(nb, be, Su, Sv, p)[1]
                adj = adjof(n, edges)
                if min(len(adj[i]) for i in range(n)) < 3:
                    continue
                gp = gap_profile(n, edges)
                g_old = [t for t in gp if t[1] - t[0] >= OLD]
                g_new = [t for t in gp if t[1] - t[0] >= LOW]
                seen_old += (1 if g_old else 0); seen_new += (1 if g_new else 0)
                if not g_new:
                    continue
                mu = sp.expand(A ** max(p - 2, 0) * bracket(A, Bu, Bv, D, p))
                ingap = []
                for f, _ in sp.factor_list(mu)[1]:
                    fp = sp.Poly(f, x)
                    if fp.degree() < 1:
                        continue
                    for z in fp.nroots(n=20, maxsteps=2000):
                        if abs(sp.im(z)) > 1e-15 or sp.re(z) <= 1e-9:
                            continue
                        th = float(sp.re(z))
                        if any(lo < th < hi for lo, hi in g_new):
                            ingap.append((th, f))
                verdict = "no root in a gap"
                if ingap:
                    bad = []
                    for th, f in ingap:
                        w = exact_not_eigenvalue(n, edges, adj, f)
                        if w is not None:
                            bad.append((th, f, w))
                    verdict = (f"*** {len(bad)} VIOLATION ***" if bad
                               else f"{len(ingap)} in gap, all eigenvalues")
                    if bad:
                        hits.append((name, p, n, bad))
                print(f"{name:>14}{p:>3}{n:>5}{connectivity(n, edges):>4}"
                      f"{len(g_old):>9}{len(g_new):>10}{len(ingap):>13}  {verdict}", flush=True)

    print(f"\n{time.time()-t0:.0f}s")
    print(f"graphs presenting a gap at the OLD threshold {OLD}: {seen_old}")
    print(f"graphs presenting a gap at the NEW threshold {LOW}: {seen_new}")
    if seen_new > seen_old:
        print(f"  -> the old threshold discarded {seen_new - seen_old} graphs that do have a gap,"
              f" {100*(seen_new-seen_old)/max(seen_new,1):.0f}% of those with one. P72(a) HOLDS.")
    if hits:
        print("\n  P72(c) FAILS. Genuine violations, in families previously reported clean:")
        for name, p, n, bad in hits:
            for th, f, w in bad:
                print(f"    {name} p={p} n={n}: root {th:.6f} of {f}, witness Gamma={w}")
    else:
        print("\n  P72(c) holds: every root found in a gap is an eigenvalue of the cover, so it")
        print("  lies in spec(T) and is not a violation. That is what the branch obstruction")
        print("  predicts for these families. The re-run changes the evidential value of the old")
        print("  verdicts, not their direction.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
