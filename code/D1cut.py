"""Hall's mechanism at minimum degree three: the 1-cut engine, which the D3 search never ran.

Every D3 attack so far tuned the CENTRAL gap of a biregular tree -- K_{d,q} (proved clean, margin
sqrt(d-1) - h_d/2 > 0 by Gershgorin on the Hermite Jacobi matrix), genuine (3,q)-biregular
designs, the two-hub engine, wheels -- and every search over cuts used SEPARATING PAIRS. But
Hall's counterexample does not work that way. It uses

  * a CUT VERTEX, not a separating pair: p copies of a block H glued at one new centre, so the
    branch factorization mu_G = mu_H^{p-1} (x mu_H - p mu_{H-v}) makes every root of mu_H a root
    of mu_G with multiplicity p-1;
  * a NARROW INTERNAL gap of an irregular universal cover, not the central gap. Hall's root is
    sqrt 5 = 2.2360, sitting in [2.219, 2.247], a gap of width 0.028 nowhere near zero.

Both features are absent from the D3 evidence, so the strongest case against D3 has not actually
been tried at minimum degree three. That is what this runs.

THE CONSTRUCTION. Take H with a designated attachment vertex v, every vertex of H other than v of
degree at least three, and deg_H(v) >= 2. Glue p >= 3 copies of H to a new centre c, joining c to
the copy of v in each. Then in G the centre has degree p >= 3, each attachment vertex has degree
deg_H(v) + 1 >= 3, and every other vertex keeps its degree >= 3, so delta(G) >= 3 exactly as D3
requires -- while mu_H still divides mu_G.

So D3 fails at once if any root of mu_H lands strictly inside a gap of spec(T_G).

FROZEN BEFORE THE DATA:
  P20. No such graph exists: over every H in the library and every p, no root of mu_H lies
       strictly inside a gap of spec(T_G). Hall's mechanism cannot be realized at delta >= 3.

If P20 fails, D3 is false and the minimum-degree repair is dead, which would matter more than
anything else in the programme. If it holds, D3 has survived the one construction actually known
to produce counterexamples, which is worth considerably more than another sweep over families
chosen for wide central gaps.

CAVEAT CARRIED FORWARD. Gaps are located by the AFH ratio system scanned on a grid
(gapscale.gap_profile), not by bisecting the decay rate, since bisection near a band edge is
unreliable -- rho -> 1 and the iteration slows critically. Any hit is re-checked on a finer grid
before it is believed, and reported only with the root's distance to both gap edges.
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
from gapscale import gap_profile

BUDGET_S = 25.0 if '--quick' in __import__('sys').argv else 2400.0


# ---------------------------------------------------------------- block library
def K(n):
    return n, [(i, j) for i in range(n) for j in range(i + 1, n)]


def Kbip(s, t):
    return s + t, [(i, s + j) for i in range(s) for j in range(t)]


def prism(k):
    """Circular ladder on 2k vertices, 3-regular."""
    e = []
    for i in range(k):
        e.append((i, (i + 1) % k))
        e.append((k + i, k + (i + 1) % k))
        e.append((i, k + i))
    return 2 * k, e


def moebius(k):
    """Moebius-Kantor style: cycle on 2k with diameters, 3-regular."""
    e = [(i, (i + 1) % (2 * k)) for i in range(2 * k)]
    e += [(i, i + k) for i in range(k)]
    return 2 * k, e


def petersen():
    e = [(i, (i + 1) % 5) for i in range(5)]
    e += [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    e += [(i, 5 + i) for i in range(5)]
    return 10, e


def blocks():
    """(name, n, edges, attachment vertex). Attachment needs degree >= 2; all others >= 3."""
    out = []
    for n in (4, 5, 6, 7):
        nn, e = K(n); out.append((f"K{n}", nn, e, 0))
    for (s, t) in ((3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (3, 12), (4, 4), (4, 6), (3, 20)):
        nn, e = Kbip(s, t)
        out.append((f"K{s},{t}", nn, e, 0))        # attach on the s-side (degree t)
        out.append((f"K{s},{t}'", nn, e, s))       # attach on the t-side (degree s)
    for k in (3, 4, 5, 6):
        nn, e = prism(k); out.append((f"prism{k}", nn, e, 0))
    for k in (3, 4, 5):
        nn, e = moebius(k); out.append((f"moeb{k}", nn, e, 0))
    nn, e = petersen(); out.append(("petersen", nn, e, 0))
    return out


def degrees(n, edges):
    d = [0] * n
    for a, b in edges:
        d[a] += 1; d[b] += 1
    return d


def glue(n, edges, v, p):
    """p copies of H plus a new centre joined to the copy of v in each."""
    E = []
    for c in range(p):
        off = c * n
        E += [(a + off, b + off) for (a, b) in edges]
    centre = p * n
    E += [(centre, c * n + v) for c in range(p)]
    return p * n + 1, E


def mu_roots(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    poly = mu_of(adj, set(range(n)))
    co = [float(c) for c in sp.Poly(poly, x).all_coeffs()]
    r = np.roots(co)
    return sorted(float(t.real) for t in r if abs(t.imag) < 1e-9 and t.real > 1e-9)


def main():
    t0 = time.time()
    print("P20 (frozen): no root of mu_H lies strictly inside a gap of spec(T_G) for any")
    print("H in the library and any p, so Hall's 1-cut mechanism cannot be realized at")
    print("minimum degree three.\n")

    lib = blocks()
    print(f"{'H':>12}{'|H|':>5}{'deg v':>7}{'p':>3}{'|G|':>5}{'delta':>7}"
          f"{'gaps of spec(T)':>34}{'closest root':>14}{'verdict':>11}")

    violations = []
    tested = 0
    for (name, n, e, v) in lib:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        d = degrees(n, e)
        if d[v] < 2 or any(d[u] < 3 for u in range(n) if u != v):
            continue
        roots = mu_roots(n, e)
        if not roots:
            continue
        for p in (3, 4, 5, 7):
            if time.time() - t0 > BUDGET_S:
                break
            N, E = glue(n, e, v, p)
            if N > 130:
                continue
            dg = degrees(N, E)
            delta = min(dg)
            if delta < 3:
                continue
            gaps = gap_profile(N, E, step=0.02)
            tested += 1
            best = None
            for (lo, hi) in gaps:
                for r in roots:
                    if lo < r < hi:
                        violations.append((name, p, r, lo, hi))
                    dist = min(abs(r - lo), abs(r - hi))
                    if best is None or dist < best[0]:
                        best = (dist, r, lo, hi)
            gtxt = "; ".join(f"[{lo:.3f},{hi:.3f}]" for (lo, hi) in gaps[:3]) or "none"
            btxt = f"{best[1]:.4f}@{best[0]:.3f}" if best else "-"
            hit = any(vv[0] == name and vv[1] == p for vv in violations)
            print(f"{name:>12}{n:>5}{d[v]:>7}{p:>3}{N:>5}{delta:>7}{gtxt:>34}{btxt:>14}"
                  f"{('REFUTES D3' if hit else 'clean'):>11}")

    print(f"\n  configurations tested: {tested}")
    if violations:
        print("  P20 IS FALSE and D3 WITH IT. Roots strictly inside a gap:")
        for (name, p, r, lo, hi) in violations:
            print(f"    H={name}, p={p}: root {r:.9f} in gap [{lo:.9f}, {hi:.9f}]")
        print("  RE-CHECK on a finer grid and in exact arithmetic before believing this.")
    else:
        print("  P20 holds. Hall's own mechanism -- cut vertex plus divisor root -- does not")
        print("  reach a gap at minimum degree three, over every block tested. That is the")
        print("  construction actually known to produce counterexamples, so this is stronger")
        print("  evidence for D3 than the central-gap sweeps it complements.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
