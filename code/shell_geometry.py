"""Is the wrong-parity region actually a thin shell?

G38 is the last link of the upper half of G37. It asks that every point of the wrong-parity
region lie within a constant times its measure of the boundary, that is

    reach(A) = sup_{z in A} dist(z, boundary A)   satisfies   reach <= c * m(A).

The relevant quantity is the INRADIUS, not the diameter. A shell wrapping around the torus
has diameter of order one however thin it is, so a diameter hypothesis is false here and
would have been the wrong thing to try to prove.

For a shell of width w around a codimension-one locus of (b-1)-area A, the measure is about
w*A and the inradius about w/2, so reach ~ m/(2A) and G38 holds as soon as A is bounded
below uniformly. This script measures, at points across a gap:

    m        measure of the wrong-parity region,
    reach    its inradius, by a grid BFS from the boundary in the torus metric,
    ratio    reach / m, which G38 asserts is bounded,
    xings    the crossing count per scan line, a proxy for the area of the locus
             {z : det S(x,z) = 0} that is bounded iff the locus does not proliferate.

If ratio blows up, G38 is false as stated. If xings blows up while ratio stays bounded, the
locus is proliferating and the constant degrades but the shape survives.
"""

import sys
import math
import cmath
from collections import deque
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

GRAPHS = {
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (0, 3)),
}
STEPS = 96          # grid per torus direction; b = 2 here, so 9216 cells


def inertia_grid(n, edges, cot, W, x, steps, b):
    """delta_ab and det on a steps^b grid (b = 2)."""
    grid = [2 * math.pi * k / steps for k in range(steps)]
    dm = np.zeros((steps, steps), dtype=int)
    dt = np.zeros((steps, steps))
    for i in range(steps):
        for j in range(steps):
            S = schur_2x2(magnetic(n, edges, cot, [grid[i], grid[j]]), x, list(W))
            S = 0.5 * (S + S.conj().T)
            w = np.linalg.eigvalsh(S)
            dm[i, j] = int(np.sum(w < 0))
            dt[i, j] = np.real(np.linalg.det(S))
    return dm, dt


def reach_of(mask, steps):
    """Inradius of the True region of `mask`, in grid steps, torus metric, by BFS from
    the complement. Returns the max BFS depth reached inside the region."""
    dist = -np.ones((steps, steps), dtype=int)
    q = deque()
    for i in range(steps):
        for j in range(steps):
            if not mask[i, j]:
                dist[i, j] = 0
                q.append((i, j))
    if not q:                      # region is everything
        return steps // 2
    while q:
        i, j = q.popleft()
        for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            a, b2 = (i + di) % steps, (j + dj) % steps
            if dist[a, b2] < 0:
                dist[a, b2] = dist[i, j] + 1
                q.append((a, b2))
    return int(dist[mask].max()) if mask.any() else 0


def crossings(dt, steps):
    """Sign changes of det along both grid directions, per scan line."""
    c = 0
    for i in range(steps):
        row = dt[i, :]
        c += int(np.sum(row[:-1] * row[1:] < 0)) + (1 if row[-1] * row[0] < 0 else 0)
        col = dt[:, i]
        c += int(np.sum(col[:-1] * col[1:] < 0)) + (1 if col[-1] * col[0] < 0 else 0)
    return c / (2 * steps)


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    for name, (n, edges, W) in GRAPHS.items():
        nF, eF = delete(n, edges, set(W))
        cF = matching_coeffs(nF, eF)
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        assert b == 2, "grid BFS written for b = 2"

        R = 5.0
        got = None
        for eta in (1e-6, 1e-4, 1e-3, 1e-2):
            es, ds, bad = scan(n, edges, -R, R, 3000, eta=eta)
            if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.02:
                got = (es, ds); break
        if got is None:
            print(f"{name}: gated"); continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.06]

        cell = 2 * math.pi / STEPS
        for lo, hi in internal:
            print(f"\n{name}  gap ({lo:.4f}, {hi:.4f})  grid {STEPS}^2")
            print(f"{'x':>9}{'delta':>6}{'m':>9}{'reach':>9}{'reach/m':>10}"
                  f"{'xings':>8}")
            for frac in (0.08, 0.25, 0.5, 0.75, 0.92):
                x = lo + frac * (hi - lo)
                k = kappa_above(es, ds, n, x)
                delta = round(k) - roots_above(cF, x)
                dm, dt = inertia_grid(n, edges, cot, W, x, STEPS, b)
                wrong = (dm % 2) != (delta % 2)
                m = wrong.mean()
                reach = reach_of(wrong, STEPS) * cell / (2 * math.pi)   # as a fraction
                ratio = reach / m if m > 1e-9 else float('nan')
                print(f"{x:>9.4f}{delta:>6}{m:>9.4f}{reach:>9.4f}{ratio:>10.3f}"
                      f"{crossings(dt, STEPS):>8.2f}")
    print("\nreach is the inradius as a fraction of the torus side; G38 asserts reach/m")
    print("is bounded. xings is the sign-change count per scan line, a proxy for the")
    print("area of the crossing locus.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
