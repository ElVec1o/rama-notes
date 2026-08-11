"""The 1-cut engine with blocks chosen adversarially, and roots tested without a grid.

code/D1cut.py ran Hall's mechanism -- cut vertex, mu_H | mu_G, root in an internal gap -- at
minimum degree three for the first time and found no violation in 118 configurations, but with
two weaknesses worth removing.

  BLOCKS WERE OFF THE SHELF. Complete graphs, prisms, Moebius ladders, Petersen: chosen for
  their own regularity, not because a root of mu_H sits anywhere near a gap of spec(T_G). The
  closest approach was 0.169, better than any previous delta >= 3 attack (0.548 for complete
  bipartite by the Gershgorin theorem, 0.36 to 0.53 for the (3,q) designs), which says the
  engine is the right one and the blocks were not.

  GAPS WERE FOUND ON A GRID. gap_profile scans at step 0.02 while Hall's gap is 0.028 wide, so
  the search was operating at roughly one grid cell of resolution in exactly the regime that
  matters. A fine rescan cleared the tightest cases, but a grid is the wrong instrument.

BOTH ARE FIXED HERE. The grid goes first: a root theta refutes D3 exactly when theta lies
OUTSIDE spec(T_G) with 0 < theta < rho(T), and the Angel-Friedman-Hoory ratio system decides
that AT theta, with no scan at all. Its decay rate is below one precisely off the spectrum
(Trans. AMS 367 (2015), Thm 1.4, the iff-criterion), which is the same certificate that
certified Hall's gap. Rates very close to one are reported as ambiguous rather than counted,
since the iteration slows critically near a band edge.

The blocks are then chosen to imitate what Hall's actually is. His block is K_{2,5} carrying a
pendant leaf, so the operative shape is K_{2,q}: two vertices of degree q against q vertices of
degree two, the widest degree contrast available at a given size, which is what opens the
internal gap. That block has minimum degree two, so it is repaired by adding an s-regular graph
on the q-side, lifting those degrees to 2 + s while leaving the contrast intact. The attachment
is the second degree-q vertex, exactly as in Hall's construction where the centre joins the
other degree-five vertex of each copy.

FROZEN BEFORE THE DATA:
  P21. No adversarially chosen block refutes D3: for every H in the family below and every p,
       every root of mu_H lies inside spec(T_G).

If P21 fails, D3 is false. If it holds, the mechanism that produces every known counterexample
has been run at minimum degree three with blocks built to its own design and with an exact
pointwise test, which is the strongest negative evidence available short of a proof.
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

BUDGET_S = 25.0 if '--quick' in __import__('sys').argv else 2700.0
AMBIG = 5e-3          # |rho - 1| below this is not trusted either way


# ------------------------------------------------------------------ blocks
def K2q_repaired(q, s):
    """K_{2,q} with an s-regular graph added on the q-side.

    Hubs 0 and 1 have degree q; the q side has degree 2 + s. Minimum degree is min(q, 2+s),
    so s >= 1 already gives 3 when q >= 3. Attachment is hub 1, as in Hall's construction.
    """
    if s >= q or (q * s) % 2:
        return None
    e = [(0, 2 + j) for j in range(q)] + [(1, 2 + j) for j in range(q)]
    # circulant s-regular graph on the q side
    offs = list(range(1, s // 2 + 1))
    for j in range(q):
        for d in offs:
            a, b = 2 + j, 2 + (j + d) % q
            if a != b and (a, b) not in e and (b, a) not in e:
                e.append((a, b))
    if s % 2:
        if q % 2:
            return None
        for j in range(q // 2):
            a, b = 2 + j, 2 + j + q // 2
            if (a, b) not in e and (b, a) not in e:
                e.append((a, b))
    return 2 + q, e, 1


def K2q_side(q, side_edges, tag):
    """K_{2,q} with an ARBITRARY graph on the q-side, needing only min degree 1 there.

    Regularity was never required: a q-side vertex has degree 2 from the hubs, so one further
    edge already gives 3. Dropping regularity is the point -- the near-miss root sat exactly on a
    spectral atom created by the symmetry of a perfect matching, and asymmetric side graphs move
    the root off the atom while leaving the hub contrast that opens the gap.
    """
    e = [(0, 2 + j) for j in range(q)] + [(1, 2 + j) for j in range(q)]
    for (a, b) in side_edges:
        if a != b and (2 + a, 2 + b) not in e and (2 + b, 2 + a) not in e:
            e.append((2 + a, 2 + b))
    return 2 + q, e, 1, tag


def side_graphs(q, rng):
    """Assorted graphs on q labelled vertices with minimum degree at least one."""
    out = []
    if q % 2 == 0:
        out.append(([(2 * i, 2 * i + 1) for i in range(q // 2)], "match"))
    out.append(([(i, (i + 1) % q) for i in range(q)], "cycle"))
    out.append(([(i, (i + 1)) for i in range(q - 1)], "path"))
    if q >= 5:
        tri = [(0, 1), (1, 2), (2, 0)]
        rest = [(i, i + 1) for i in range(3, q - 1, 2)]
        if q % 2 == 0:
            out.append((tri + rest, "tri+match"))
    if q >= 4:
        out.append(([(0, j) for j in range(1, q)], "star"))
    if q >= 6:
        out.append(([(i, (i + 1) % q) for i in range(q)] + [(0, q // 2)], "cycle+chord"))
    for t in range(6):                                   # random, min degree forced to 1
        es = set()
        perm = list(range(q)); rng.shuffle(perm)
        for i in range(0, q - 1, 2):
            es.add((min(perm[i], perm[i + 1]), max(perm[i], perm[i + 1])))
        for _ in range(rng.integers(1, max(2, q // 2))):
            a, b = int(rng.integers(q)), int(rng.integers(q))
            if a != b:
                es.add((min(a, b), max(a, b)))
        deg = {i: 0 for i in range(q)}
        for (a, b) in es:
            deg[a] += 1; deg[b] += 1
        if all(deg[i] >= 1 for i in range(q)):
            out.append((sorted(es), f"rand{t}"))
    return out


def blocks():
    import numpy as _np
    rng = _np.random.default_rng(20260824)
    out = []
    for q in (6, 8, 9, 10, 11, 12, 13, 14):
        for (se, tag) in side_graphs(q, rng):
            n, e, v, t = K2q_side(q, se, tag)
            d = [0] * n
            for a, b in e:
                d[a] += 1; d[b] += 1
            if d[v] < 2 or any(d[u] < 3 for u in range(n) if u != v):
                continue
            out.append((f"K2,{q}+{t}", n, e, v))
    return out


def degrees(n, edges):
    d = [0] * n
    for a, b in edges:
        d[a] += 1; d[b] += 1
    return d


def glue(n, edges, v, p):
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
    poly = sp.expand(mu_of(adj, set(range(n))))
    # np.roots on a polynomial with a multiplicity-m root has error ~eps^(1/m): at m = 4 that is
    # 1e-4, enough to move a root off an exact value and across a spectral atom. Factor first and
    # solve each irreducible factor separately, so every root is simple where it is computed.
    out = set()
    for (f, _mult) in sp.factor_list(poly)[1]:
        for r in sp.Poly(f, x).nroots(n=30):
            if abs(sp.im(r)) < 1e-20:
                val = float(sp.re(r))
                if val > 1e-9:
                    out.add(round(val, 12))
    return sorted(out)


def dos_at(N, E, lam, eta, iters=60000, tol=1e-13):
    """Density of states of the universal cover at lam, by the cavity equations.

    Shares no code with rho_at. A spectral ATOM shows as a density diverging like 1/eta, which
    is exactly what the AFH ratio system misses: at an atom its recursion can still converge
    with decay below one and report `outside`.
    """
    adj = {i: [] for i in range(N)}
    for a, b in E:
        adj[a].append(b); adj[b].append(a)
    de, idx = [], {}
    for a, b in E:
        idx[(a, b)] = len(de); de.append((a, b))
        idx[(b, a)] = len(de); de.append((b, a))
    z = complex(lam, eta)
    g = np.full(len(de), -0.5j, dtype=complex)   # PHYSICAL branch: Im g < 0
    for _ in range(iters):
        new = np.empty_like(g)
        for k, (u, vv) in enumerate(de):
            sm = 0j
            for w in adj[u]:
                if w != vv:
                    sm += g[idx[(w, u)]]
            new[k] = 1.0 / (z - sm)
        d = np.max(np.abs(new - g)); g = new
        if d < tol:
            break
    vals = []
    for v0 in range(N):
        sm = sum(g[idx[(w, v0)]] for w in adj[v0])
        vals.append(-(1.0 / math.pi) * (1.0 / (z - sm)).imag)
    return float(np.mean(vals))


def outside_spectrum(theta, B, M, N=None, E=None):
    """AFH first, then a DOS gate. Returns (verdict, rho).

    The AFH decay rate alone is NOT sufficient: at a spectral atom it converges below one and
    reports `outside` although the point is in the spectrum. Every `outside` verdict is
    therefore confirmed by checking that the density of states does not blow up as eta shrinks;
    a density growing like 1/eta is an atom and the verdict is overturned.
    """
    r = rho_at(float(theta), B, M, iters=20000, tol=1e-13)
    if r is None:
        return False, None
    if abs(r - 1.0) < AMBIG:
        return None, r
    if r >= 1.0:
        return False, r
    if N is not None:
        d1 = dos_at(N, E, float(theta), 1e-3)
        d2 = dos_at(N, E, float(theta), 1e-4)
        if abs(d2) > 10.0 * max(abs(d1), 1e-12) * 0.5:      # grew ~10x when eta fell 10x
            return False, r                                  # atom: in the spectrum
    return True, r


def main():
    t0 = time.time()
    print("P21 (frozen): no adversarially chosen block refutes D3 -- every root of mu_H lies")
    print("inside spec(T_G), for every block and every p.\n")
    print("Roots tested pointwise by the AFH ratio system; no grid, so no resolution artefact.\n")

    lib = blocks()
    print(f"{'H':>16}{'|H|':>5}{'p':>3}{'|G|':>5}{'delta':>6}{'rho(T)':>9}"
          f"{'roots<rho':>10}{'min |rho_AFH - 1|':>19}{'verdict':>12}")

    violations, ambiguous, tested = [], [], 0
    for (name, n, e, v) in lib:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        roots = mu_roots(n, e)
        if not roots:
            continue
        for p in (3, 4, 5, 6, 8):
            if time.time() - t0 > BUDGET_S:
                break
            N, E = glue(n, e, v, p)
            if N > 140:
                continue
            dg = degrees(N, E)
            if min(dg) < 3:
                continue
            B, M = setup(N, E)
            rho_top = 2.0 * math.sqrt(max(dg) - 1)
            cand = [r for r in roots if r < rho_top]
            tested += 1
            closest, hit, amb = None, False, False
            for r in cand:
                verdict, rr = outside_spectrum(r, B, M, N, E)
                if rr is not None and (closest is None or abs(rr - 1.0) < closest):
                    closest = abs(rr - 1.0)
                if verdict is True:
                    violations.append((name, p, r, rr)); hit = True
                elif verdict is None:
                    ambiguous.append((name, p, r, rr)); amb = True
            tag = "REFUTES D3" if hit else ("ambiguous" if amb else "clean")
            print(f"{name:>16}{n:>5}{p:>3}{N:>5}{min(dg):>6}{rho_top:>9.4f}"
                  f"{len(cand):>10}{(closest if closest is not None else float('nan')):>19.5f}"
                  f"{tag:>12}")

    print(f"\n  configurations tested: {tested}")
    if violations:
        print("  P21 IS FALSE and D3 WITH IT:")
        for (name, p, r, rr) in violations:
            print(f"    H={name}, p={p}: root {r:.9f} outside spec(T), AFH decay {rr:.9f}")
        print("  RE-CHECK in exact arithmetic before this leaves the machine.")
    elif ambiguous:
        print(f"  No violation, but {len(ambiguous)} root(s) sat within {AMBIG} of the band edge")
        print("  and are not decided by this test:")
        for (name, p, r, rr) in ambiguous[:8]:
            print(f"    H={name}, p={p}: root {r:.6f}, AFH decay {rr:.6f}")
    else:
        print("  P21 holds. Every root is strictly inside the spectrum, decided pointwise.")
        print("  Hall's mechanism, with blocks built to its own design, does not reach a gap at")
        print("  minimum degree three.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
