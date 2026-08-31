"""A gap detector that does not under-report widths.

code/gapwidth_underreport.py shows that gapscale.gap_profile reports gap widths up to 2.5 times too
small, and that this is what hid four counterexamples from the searches here. The cause is the
solver, not the scan. gap_profile calls rho_at, a real fixed-point iteration

    h <- 1/(lambda - B h)

on the directed edges, which fails to converge at most points INSIDE a gap and returns None; a None
is then scored as "in the spectrum". A gap is seen as a scatter of isolated converged points instead
of an interval, and its reported width collapses toward two scan steps. On the five known
counterexamples between 25 and 58 percent of fine-scan points converge.

THE FIX is to ask the question in the complex plane, where the same recursion is a contraction. With
z = lambda + i*eta and eta > 0,

    g_e = 1/(z - sum_{e -> f} g_f)

converges for every lambda, and the density of states is (1/pi) Im sum_w G_w. Its behaviour as
eta -> 0 separates the three cases cleanly:

    outside the bands   Im G falls linearly in eta
    inside a band       Im G tends to a positive constant
    at an atom          Im G grows like 1/eta

Two values of eta a factor of 100 apart suffice to tell them apart, so each point costs two solves
rather than one, and the solution at one lambda warm-starts the next.

WHAT THIS DETECTOR DOES AND DOES NOT DECIDE. It maps the BANDS, and it does so robustly. It does not
by itself decide membership of spec(T), because the point spectrum is invisible to it: at an Aomoto
eigenvalue lying in a band gap the resolvent reports "outside" although the point is in spec(T).
That blind spot is what produced the retracted D3 and C2 claims. The division of labour that works
is therefore

    bands            <- this file, numerically but robustly
    point spectrum   <- the exact criterion of Li-Magee-Sabri-Thomas, by polynomial divisibility
    in spec(T)       <- in a band, OR an eigenvalue

and a root is a violation only when it is in neither. code/aomoto_obstruction.py supplies the second.

FROZEN BEFORE THE DATA:
  P74. (a) On K_{a,b} the detector reproduces the exact biregular gap (0, |s-t|), s = sqrt(a-1),
           t = sqrt(b-1), and finds no other gap below the band top s+t.
       (b) On a 3-regular graph it reports no gap at all, the cover being the 3-regular tree.
       (c) Convergence is essentially total, against the 25 to 58 percent of rho_at, and the widths
           it reports for the five known counterexamples are at least those certified by fine
           scanning with rho_at.

FALSIFICATION. If (a) or (b) fails the detector is wrong on cases with known answers and nothing
else it says can be used. If (c) fails it is no improvement.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import numpy as np
from gapscale import setup

ETA_HI, ETA_LO = 1e-3, 1e-5


def _solve(B, M, adj, n, de_index, lam, eta, g0=None, damp=0.5, iters=200000, tol=1e-13):
    """Damped complex cavity solve. Returns (|Im sum_w G_w|, g) for warm starting."""
    z = complex(lam, eta)
    g = np.full(M, 0.1 + 0.1j) if g0 is None else g0.copy()
    for _ in range(iters):
        new = 1.0 / (z - B @ g)
        d = np.max(np.abs(new - g))
        g = (1 - damp) * g + damp * new
        if d < tol:
            break
    tot = 0.0
    for w in range(n):
        tot += (1.0 / (z - sum(g[de_index[(u, w)]] for u in adj[w]))).imag
    return abs(tot), g


def _prep(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    return adj, {e: k for k, e in enumerate(de)}


def classify_point(n, edges, lam, B=None, M=None, warm=None):
    """'outside' | 'band' | 'atom', from how Im G scales between two values of eta."""
    if B is None:
        B, M = setup(n, edges)
    adj, idx = _prep(n, edges)
    hi, g1 = _solve(B, M, adj, n, idx, lam, ETA_HI, warm)
    lo, g2 = _solve(B, M, adj, n, idx, lam, ETA_LO, g1)
    if hi <= 0:
        return 'outside', g2
    r = lo / hi
    if r > 3.0:
        return 'atom', g2
    if r < 0.1:                      # a hundredfold drop in eta gives a hundredfold drop in Im G
        return 'outside', g2
    return 'band', g2


def band_profile(n, edges, step=0.02, top=None):
    """Maximal intervals in (0, top) on which lambda lies outside every band.

    Unlike gapscale.gap_profile this never scores a non-convergent point as spectrum, because the
    complex recursion converges everywhere."""
    B, M = setup(n, edges)
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    if top is None:
        top = 2 * math.sqrt(max(deg) - 1) + 0.5
    out, cur, warm = [], None, None
    t = step
    while t < top:
        kind, warm = classify_point(n, edges, t, B, M, warm)
        outside = (kind == 'outside')
        if outside and cur is None:
            cur = t
        if not outside and cur is not None:
            out.append((cur, t)); cur = None
        t += step
    if cur is not None:
        out.append((cur, top))
    return [g for g in out if g[1] < top - step]


def main():
    import json
    from gapscale import gap_profile
    from aomoto_obstruction import hall
    print("P74 (frozen): a detector that maps the bands without under-reporting.\n")

    print("(a),(b) against covers whose spectrum is known exactly")
    ok = True
    for (a, b) in [(3, 4), (2, 3)]:
        e = [(i, a + j) for i in range(a) for j in range(b)]
        s, t = math.sqrt(a - 1), math.sqrt(b - 1)
        g = band_profile(a + b, e, step=0.02)
        got = [x for x in g if x[0] < 0.05]
        good = bool(got) and abs(got[0][1] - abs(s - t)) < 0.05
        ok = ok and good
        print(f"    K_{{{a},{b}}}: exact gap (0, {abs(s-t):.4f})   detected "
              f"{[(round(u,3), round(v,3)) for u, v in g]}   {'OK' if good else 'MISMATCH'}")
    e4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    g = band_profile(4, e4, step=0.02)
    good = (len(g) == 0)
    ok = ok and good
    print(f"    K_4 3-regular: exact answer no gap   detected {g}   {'OK' if good else 'MISMATCH'}")
    if not ok:
        print("  the detector fails a known case.")
        return 1

    print("\n(c) the five known counterexamples: old detector vs new")
    print(f"{'example':>26}  {'gap_profile':>12}  {'band_profile':>26}  {'width':>8}  {'ratio':>6}")
    cases = []
    n, e, _ = hall(5, 5, True)
    cases.append(("Hall 41v", n, e, math.sqrt(5)))
    for o in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..',
                                         'data', 'lowgap_counterexamples.json'))):
        cases.append((f"new n={o['n']} root {o['root']:.4f}", o['n'],
                      [tuple(x) for x in o['edges']], o['root']))
    for nm, n, e, th in cases:
        old = [x for x in gap_profile(n, e) if x[0] < th < x[1]]
        ow = (old[0][1] - old[0][0]) if old else 0.0
        new = [x for x in band_profile(n, e, step=0.005, top=th + 0.3) if x[0] < th < x[1]]
        nw = (new[0][1] - new[0][0]) if new else 0.0
        print(f"{nm:>26}  {ow:>12.4f}  "
              f"{(f'[{new[0][0]:.4f}, {new[0][1]:.4f}]' if new else 'none'):>26}  "
              f"{nw:>8.4f}  {(nw/ow if ow else 0):>6.2f}x")
    return 0


if __name__ == '__main__':
    sys.exit(main())
