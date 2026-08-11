"""D3, pushed where it was closest: fixed degrees, varying structure.

The near-miss was a block K_{2,12} plus a perfect matching, whose mu_H has a root at exactly 1
sitting inside a gap of half-width sqrt11 - sqrt2 = 1.90, saved only because 1 is a spectral ATOM
of the cover. Breaking the symmetry moved the root off the atom -- but into the continuous
spectrum, not into the gap, because changing the side graph also changed the DEGREES, and the
degrees are what place the gap.

So hold the degrees fixed and vary only the structure. With S an s-regular graph on the q-side,
H = K_{2,q} + S has degrees (2+s) on the q side and q at the hubs for EVERY choice of S, so the
gap is fixed while mu_H moves. Different s-regular S on the same q therefore probe a fixed gap
with a moving root, which is the configuration the earlier searches could not produce.

FROZEN BEFORE THE DATA:
  P31. No root of mu_H lands outside spec(T_G), over s-regular side graphs at fixed degrees.

Instrumentation follows the rules this session had to learn: roots by factoring, membership
pointwise with the DOS gate, a wall-clock budget tested in the INNER loop, and no allocation
that grows with the path tree.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import numpy as np
import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gapscale import setup
from D1cut_adv import outside_spectrum, mu_roots, glue, degrees
import quickmode

BUDGET = 25.0 if quickmode.QUICK else 2100.0


def block(q, S_edges):
    """K_{2,q} with S on the q-side; hubs 0,1, side vertices 2..q+1. Attachment is hub 1."""
    e = [(0, 2 + j) for j in range(q)] + [(1, 2 + j) for j in range(q)]
    e += [(2 + a, 2 + b) for (a, b) in S_edges]
    return 2 + q, e, 1


def main():
    t0 = time.time()
    print("P31 (frozen): no root of mu_H lands outside spec(T_G) at fixed degrees.\n")
    print("S ranges over s-regular graphs on q vertices, so H = K_{2,q}+S has the SAME degree")
    print("sequence for every S: the gap is fixed and only the roots move.\n")
    print(f"{'q':>4}{'s':>3}{'S'      :>12}{'p':>3}{'|G|':>5}{'delta':>6}{'roots<rho':>10}"
          f"{'verdict':>12}")
    viol, amb, tested = [], [], 0
    rng = np.random.default_rng(20260903)
    for (q, s) in ((12, 1), (12, 2), (12, 3), (10, 3), (14, 3), (12, 4), (10, 2)):
        if (q * s) % 2:
            continue
        seen = set()
        for trial in range(14):
            if time.time() - t0 > BUDGET:
                break
            try:
                S = nx.random_regular_graph(s, q, seed=int(rng.integers(1 << 30)))
            except Exception:
                continue
            key = nx.weisfeiler_lehman_graph_hash(S)
            if key in seen:
                continue
            seen.add(key)
            n, e, v = block(q, list(S.edges()))
            d = degrees(n, e)
            if d[v] < 2 or any(d[u] < 3 for u in range(n) if u != v):
                continue
            try:
                roots = mu_roots(n, e)
            except Exception:
                continue
            if not roots:
                continue
            for p in (3, 5):
                if time.time() - t0 > BUDGET:
                    break
                N, E = glue(n, e, v, p)
                if N > 120:
                    continue
                dg = degrees(N, E)
                if min(dg) < 3:
                    continue
                B, M = setup(N, E)
                rho = 2.0 * math.sqrt(max(dg) - 1)
                cand = [r for r in roots if r < rho]
                tested += 1
                hit = a_ = False
                for r in cand:
                    verdict, rr = outside_spectrum(r, B, M, N, E)
                    if verdict is True:
                        viol.append((q, s, p, r, rr)); hit = True
                    elif verdict is None:
                        amb.append((q, s, p, r, rr)); a_ = True
                if hit or a_ or tested % 6 == 1:
                    print(f"{q:>4}{s:>3}{key[:10]:>12}{p:>3}{N:>5}{min(dg):>6}{len(cand):>10}"
                          f"{('REFUTES D3' if hit else ('ambiguous' if a_ else 'clean')):>12}",
                          flush=True)

    print(f"\n  configurations tested: {tested}   violations: {len(viol)}   ambiguous: {len(amb)}")
    if viol:
        print("  P31 IS FALSE and D3 WITH IT:")
        for (q, s, p, r, rr) in viol[:8]:
            print(f"    q={q} s={s} p={p}: root {r:.9f} outside spec(T), AFH decay {rr}")
        print("  RE-CHECK in exact arithmetic before this leaves the machine.")
    else:
        print("  P31 holds. Holding the degrees fixed and moving the roots does not put one in")
        print("  a gap either, which was the configuration the earlier searches could not make.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
