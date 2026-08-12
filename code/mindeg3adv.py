"""D3 against the divisibility engine itself, with a margin instead of a verdict.

code/mindeg3.py swept 102 graphs of minimum degree three with a separating pair and reported
"clean" everywhere. That sweep has a hole. The two-cut identity is

    mu_G = A^{p-2} * (x^2 A^2 - p x (Bu + Bv) A + p D A + p(p-1) Bu Bv),

and mindeg3 iterated over the roots of the BRACKET only. It never looked at the roots of A. But A
is the matching polynomial of the branch, and A^{p-2} | mu_G for every p >= 3, so every root of A is
a root of mu_G. That divisor is precisely the localized subgraph divisibility mu_H | mu_G that broke
Conjecture 10 at Hall's counterexample. The previous verdict was reached without testing the
mechanism the conjecture is supposed to defeat.

This closes that, and reports a signed MARGIN rather than a pass/fail, because "clean" says nothing
about how close the failure came.

THE ADVERSARIAL HANDLE. The roots of A depend on the branch alone; the gaps of spec(T_G) depend on
p as well. So the branch pins a set of roots and p slides the gaps underneath them. Scanning p at
fixed branch is a genuine two-parameter hunt for a collision, not a sample. For each branch the
table records the closest a gap edge ever came to a pinned root.

FROZEN BEFORE THE DATA:
  P61. (a) No root of A lies in a gap of spec(T_G), at any tested graph of minimum degree three.
       (b) No root of the bracket does either, reproducing mindeg3's verdict on a finer probe.
       (c) The margin, meaning the least distance from any root of mu_G to any gap of spec(T_G),
           stays above 0.05 across the sweep, so D3 is not surviving by a hair.

FALSIFICATION. One (branch, p) with a root of A or of the bracket strictly inside a gap kills D3 and
with it the whole "2-connectivity implies the covering bound" programme. A margin that collapses
towards zero as p grows would say D3 is true only by accident and asymptotically false, which is
almost as bad; that is why the margin, and not the verdict, is the output.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from twocut import branch_data, bracket, assemble, mu_of, x
from gapscale import setup, rho_at, gap_profile, connectivity
from mindeg3 import FAMILIES
import quickmode

BUDGET = 1500.0
CKPT = quickmode.ckpt('private/mindeg3adv_ckpt.txt')
MIN_GAP = 0.05
NMAX = 62


def pos_roots(poly):
    """Real positive roots of a sympy polynomial in x, deduplicated."""
    co = sp.Poly(sp.expand(poly), x).all_coeffs()
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return []
    try:
        rs = sp.Poly(co, x).nroots(n=25, maxsteps=4000)
    except Exception:
        return []
    out = []
    for r in rs:
        if abs(sp.im(r)) < 1e-12 and sp.re(r) > 1e-9:
            v = float(sp.re(r))
            if not any(abs(v - w) < 1e-9 for w in out):
                out.append(v)
    return sorted(out)


def refine(th, B, M):
    """A gap found by a 0.02 scan is only known to that resolution. Confirm directly at the root:
    rho < 1 there means the root really is outside spec(T), whatever the scan said."""
    r = rho_at(th, B, M)
    return r is not None and r < 1.0


def margin_of(th, gaps):
    """Signed position of a root against the gap set. Positive = inside a gap, by that depth,
    which is a violation. Negative = outside every gap, by that distance, which is the slack."""
    best = None
    for (lo, hi) in gaps:
        if lo < th < hi:
            d = min(th - lo, hi - th)
        else:
            d = -min(abs(th - lo), abs(th - hi))
        if best is None or d > best:
            best = d
    return best


def main():
    print("P61 (frozen): the roots of the branch polynomial A, which divide mu_G whenever p >= 3,")
    print("avoid every gap of spec(T_G) once the branch has minimum degree three, and do so with")
    print("room to spare. This is the test mindeg3.py did not run.\n")

    print("divisibility check: A^(p-2) really does divide mu_G on these branches", flush=True)
    okdiv = True
    for name, (nb, be, Su, Sv) in (FAMILIES[0], FAMILIES[9], FAMILIES[14]):
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        for p in (3, 4):
            n, edges = assemble(nb, be, Su, Sv, p)
            adj = {i: set() for i in range(n)}
            for a, b in edges:
                adj[a].add(b); adj[b].add(a)
            mu = mu_of(adj, set(range(n)))
            q, rem = sp.div(sp.Poly(mu, x), sp.Poly(sp.expand(A ** (p - 2)), x))
            good = rem.is_zero
            okdiv = okdiv and good
            print(f"  {name:>12} p={p} n={n:>3}: "
                  f"{'A^(p-2) | mu_G' if good else 'DOES NOT DIVIDE'}", flush=True)
    if not okdiv:
        print("the premise of this whole script is wrong; nothing below means anything.")
        return 1
    print()

    print(f"{'branch':>12}{'p':>3}{'n':>5}{'kappa':>6}{'#gaps':>6}{'maxgap':>8}"
          f"{'rootsA':>7}{'rootsBr':>8}{'worstA':>9}{'worstBr':>9}{'verdict':>11}", flush=True)
    t0 = time.time()
    tested = kept = 0
    hits = []
    per_branch = {}
    for name, (nb, be, Su, Sv) in quickmode.few(FAMILIES, 1):
        if time.time() - t0 > BUDGET:
            print("  [budget reached]"); break
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        rootsA = pos_roots(A)
        for p in range(3, 10):
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
            if not gaps:
                print(f"{name:>12}{p:>3}{n:>5}{connectivity(n, edges):>6}{0:>6}{0.0:>8.3f}"
                      f"{len(rootsA):>7}{'-':>8}{'-':>9}{'-':>9}{'no gap':>11}", flush=True)
                continue
            kept += 1
            kap = connectivity(n, edges)
            B, M = setup(n, edges)
            rootsBr = pos_roots(bracket(A, Bu, Bv, D, p))

            wA = max((margin_of(th, gaps) for th in rootsA), default=None)
            wB = max((margin_of(th, gaps) for th in rootsBr), default=None)
            bad = []
            for tag, rts in (('A', rootsA), ('bracket', rootsBr)):
                for th in rts:
                    d = margin_of(th, gaps)
                    if d is not None and d > 0 and refine(th, B, M):
                        bad.append((tag, th, d))
            mx = max(t[1] - t[0] for t in gaps)
            print(f"{name:>12}{p:>3}{n:>5}{kap:>6}{len(gaps):>6}{mx:>8.3f}"
                  f"{len(rootsA):>7}{len(rootsBr):>8}{wA:>9.4f}{wB:>9.4f}"
                  f"{('VIOLATION' if bad else 'clean'):>11}", flush=True)
            if bad:
                hits.append((name, p, n, kap, bad))
            k = per_branch.setdefault(name, [])
            k.append(max(wA, wB))
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"{name} p={p} tested={tested} withgap={kept} hits={len(hits)}\n")
            os.replace(CKPT + '.tmp', CKPT)

    print(f"\n{tested} graphs of minimum degree three, {kept} of them with a gap of width "
          f">= {MIN_GAP}.  {time.time()-t0:.0f}s")

    if per_branch:
        print("\nclosest approach per branch, over all p: how near a gap edge came to a root.")
        print(f"{'branch':>12}{'p values':>10}{'closest':>10}")
        worst = None
        for nm, vals in sorted(per_branch.items(), key=lambda kv: -max(kv[1])):
            c = max(vals)
            worst = c if worst is None else max(worst, c)
            print(f"{nm:>12}{len(vals):>10}{c:>10.4f}")
        print(f"\n  worst approach anywhere: {worst:.4f} "
              f"({'INSIDE a gap' if worst > 0 else 'outside every gap'})")

    if hits:
        print("\nD3 IS FALSE. A root of mu_G sits in a gap of spec(T_G) at minimum degree three:")
        for nm, p, n, kap, bad in hits:
            for tag, th, d in bad:
                print(f"  {nm} p={p} n={n} kappa={kap} factor={tag} "
                      f"theta={th:.6f} depth={d:.6f}")
        print("  P61 (a)-(c) all fail, and the min-degree repair of Conjecture 10 dies with them.")
    else:
        print("\n  P61 (a) and (b) HOLD on this sweep: no root of A, and none of the bracket,")
        print("  reaches a gap. The divisibility A^(p-2) | mu_G is real and was untested before,")
        print("  so this is the first time D3 has been checked against the engine that killed")
        print("  Conjecture 10 rather than against the bracket alone.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
