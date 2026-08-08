"""Spectrum and integrated density of states of the universal cover of a finite graph.

This is the instrument that was missing. Everything about Conjecture 10 beyond the
tree-substitution families needs spec(T) for an irregular G, and spec(T) is computable: the
universal cover is a tree whose local structure is finitely described by G, so the
non-backtracking cavity equations close on the directed edges of G.

For a directed edge u -> v write h_{u->v}(x) for the Green's function at u in the branch
hanging off u away from v. Then

    h_{u->v}(x) = 1 / ( x - sum over w ~ u, w != v of h_{w->u}(x) )
    G_vv(x)     = 1 / ( x - sum over u ~ v of h_{u->v}(x) )

a closed system in 2|E| unknowns. Evaluating at x = E + i eta with small eta > 0 and
iterating to a fixed point gives the resolvent on the real axis from above, so

    density(E) = -(1/pi) * average over v of Im G_vv(E + i eta)
    kappa(E)   = n * integral of density from E to infinity

kappa is the gap label: the trace of the negative spectral projection of E I - A_T, an
integer at every E outside spec(T) by Pimsner-Voiculescu. GAPCOUNT asserts it equals the
number of roots of mu_G above E.

What this script reports, for each graph:
  - the band structure of spec(T) read off from where the density is nonzero,
  - whether every root of mu_G lies in spec(T), which is Conjecture 10 at d = 1,
  - kappa(E) against the root count of mu_G at points in the gaps, which is GAPCOUNT,
  - how far kappa is from an integer, which is the honest error bar on the whole thing.

Numerics discipline (Rule 7). Floating point is evidence, not proof. eta is finite, so
band edges are smeared by O(eta) and kappa carries a quadrature error; both are reported
rather than hidden. The regression check is K4 with one pendant per vertex, where spec(T)
is known in closed form to be the union of plus and minus [sqrt3 - sqrt2, sqrt3 + sqrt2]:
if the solver does not reproduce that, nothing else here is trustworthy.

VALIDITY GATE. The density must integrate to 1. When the universal cover has point
spectrum, that is flat bands, the cavity fixed point is singular there and the damped
iteration can diverge; the symptom is a total mass wildly above 1, and every number from
such a run is meaningless. The gate rejects those runs outright rather than reporting them,
because a diverged kappa looks exactly like a violated GAPCOUNT and is nothing of the kind.
Graphs that fail the gate at one eta are retried at larger eta, which smooths the delta
functions at the cost of blurring band edges.
"""

import sys
import cmath
import math

ETA = 1e-6
MAXIT = 4000
TOL = 1e-12


def directed_edges(n, edges):
    adj = {v: [] for v in range(n)}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    de = []
    idx = {}
    for u in range(n):
        for v in adj[u]:
            idx[(u, v)] = len(de)
            de.append((u, v))
    return adj, de, idx


def cavity(n, edges, z, h0=None):
    """Solve the cavity equations at complex z.  Returns (h, converged)."""
    adj, de, idx = directed_edges(n, edges)
    h = [complex(0.0, -0.1)] * len(de) if h0 is None else list(h0)
    for it in range(MAXIT):
        new = [0j] * len(de)
        for k, (u, v) in enumerate(de):
            s = 0j
            for w in adj[u]:
                if w != v:
                    s += h[idx[(w, u)]]
            den = z - s
            if abs(den) < 1e-30:
                den = complex(1e-30, -1e-30)
            new[k] = 1.0 / den
        diff = max(abs(new[k] - h[k]) for k in range(len(de)))
        # damped update keeps the iteration stable inside the bands
        h = [0.5 * new[k] + 0.5 * h[k] for k in range(len(de))]
        if diff < TOL:
            return h, True
    return h, False


def density_at(n, edges, E, eta=ETA, h0=None):
    """(density, h) at energy E, with density = -(1/pi) mean_v Im G_vv.

    h0 warm-starts the iteration from the previous energy.  Without it the solver
    re-converges from scratch at every grid point, which costs a factor of a hundred and
    makes the scan hopeless in Python."""
    adj, de, idx = directed_edges(n, edges)
    z = complex(E, eta)
    h, conv = cavity(n, edges, z, h0)
    tot = 0.0
    for v in range(n):
        s = sum(h[idx[(u, v)]] for u in adj[v])
        G = 1.0 / (z - s)
        tot += -G.imag / math.pi
    return tot / n, h, conv


def matching_roots(n, edges):
    from functools import lru_cache
    import numpy as np
    m = len(edges)

    @lru_cache(maxsize=None)
    def rec(i, mask, k):
        if i == m:
            return 1 if k == 0 else 0
        t = rec(i + 1, mask, k)
        if k > 0:
            u, v = edges[i]
            bu, bv = 1 << u, 1 << v
            if not (mask & bu) and not (mask & bv):
                t += rec(i + 1, mask | bu | bv, k - 1)
        return t

    c = [0] * (n + 1)
    for k in range(n // 2 + 1):
        c[n - 2 * k] += (-1) ** k * rec(0, 0, k)
    rec.cache_clear()
    r = np.roots(list(reversed(c)))
    return sorted(r.real)[::-1]


def scan(n, edges, lo, hi, steps, eta=ETA):
    """Density on a grid, swept downward from above the spectrum with continuation.

    eta is passed explicitly rather than read from the module default, which is bound at
    definition time and so cannot be changed by a caller."""
    Es = [hi - (hi - lo) * i / steps for i in range(steps + 1)]
    ds = []
    h = None
    bad = 0
    for E in Es:
        d, h, conv = density_at(n, edges, E, eta=eta, h0=h)
        if not conv:
            bad += 1
        ds.append(max(d, 0.0))
    Es = Es[::-1]
    ds = ds[::-1]
    return Es, ds, bad


def bands(Es, ds, thresh):
    out = []
    inb = False
    for E, d in zip(Es, ds):
        if d > thresh and not inb:
            inb = True
            start = E
        elif d <= thresh and inb:
            inb = False
            out.append((start, E))
    if inb:
        out.append((start, Es[-1]))
    return out


def kappa_above(Es, ds, n, E0):
    """n * integral of density from E0 upward, by the trapezoid rule."""
    tot = 0.0
    for i in range(len(Es) - 1):
        a, b = Es[i], Es[i + 1]
        if b <= E0:
            continue
        a = max(a, E0)
        tot += 0.5 * (ds[i] + ds[i + 1]) * (b - a)
    return n * tot


GRAPHS = {
    # regression: spec(T) known in closed form, +-[sqrt3-sqrt2, sqrt3+sqrt2]
    'K4+pendant': (8, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                       (0, 4), (1, 5), (2, 6), (3, 7)]),
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)]),
    'bowtie': (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]),
    'theta': (5, [(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4)]),
}


MASS_TOL = 0.02


def main():
    import time
    t0 = time.time()
    print(f"grid 4001 points, swept downward with continuation, "
          f"validity gate |mass - 1| <= {MASS_TOL}\n")
    for name, (n, edges) in GRAPHS.items():
        roots = matching_roots(n, edges)
        R = max(4.0, 1.2 * max(abs(r) for r in roots) + 1.0)
        chosen = None
        for eta in (1e-6, 1e-4, 1e-3, 1e-2, 5e-2):
            Es, ds, bad = scan(n, edges, -R, R, 4000, eta=eta)
            mass = kappa_above(Es, ds, 1, -R)
            if abs(mass - 1.0) <= MASS_TOL:
                chosen = eta
                break
        if chosen is None:
            print(f"{name}  n={n}  SOLVER FAILED at every eta tried, last mass "
                  f"{mass:.2f}; no numbers reported")
            print("  cause: point spectrum makes the cavity fixed point singular\n")
            continue
        bs = bands(Es, ds, 1e-3)
        print(f"{name}  n={n}  eta={chosen:g}  total mass {mass:.4f}"
              f"  non-converged points: {bad}")
        print("  bands: " + ", ".join(f"[{a:.4f},{b:.4f}]" for a, b in bs))
        outside = [r for r in roots
                   if not any(a - 5e-3 <= r <= b + 5e-3 for a, b in bs)]
        print(f"  matching roots: {['%.4f' % r for r in roots]}")
        print(f"  Conjecture 10: {'OK' if not outside else 'ROOTS OUTSIDE ' + str(outside)}")
        # gap probes: midpoints of the complementary intervals inside [-R, R]
        gaps = []
        prev = -R
        for a, b in bs:
            if a - prev > 0.05:
                gaps.append(0.5 * (prev + a))
            prev = b
        for E0 in gaps:
            k = kappa_above(Es, ds, n, E0)
            NG = sum(1 for r in roots if r > E0)
            print(f"  gap E={E0:+.4f}  kappa={k:8.4f}  nearest int={round(k):3d}"
                  f"  |err|={abs(k - round(k)):.4f}   N_G={NG:3d}"
                  f"   {'MATCH' if round(k) == NG else 'MISMATCH'}")
        print()
    print(f"elapsed {time.time()-t0:.1f}s")
    return 0


if __name__ == '__main__':
    sys.exit(main())
