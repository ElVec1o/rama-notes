"""Does moving the polytorus radii settle the residue?

mu_G(x) is the constant Fourier coefficient of the Laurent polynomial

    P_x(z) = det(x I - A_G(z)),   A_G(z)_{uv} = z_e,  A_G(z)_{vu} = z_e^{-1},

and a constant coefficient does not change when the polytorus radii change:

    mu_G(x) = integral over T^b of P_x(r . w) dw       for EVERY r in (0,inf)^b.

At r = 1 the matrix is Hermitian, P_x is real, and if it never vanishes then connectedness of
the torus forces one sign and the average is nonzero. That is the localization, and it settles
exactly the points outside spec(G^ab). Off r = 1 the matrix is no longer Hermitian and P_x is
complex, so sign is meaningless, but the conclusion survives in the right form:

    CONTRACT. If there are r in (0,inf)^b and a unit xi in C with Re(xi P_x(r . w)) > 0 for
    all w in T^b, then mu_G(x) != 0.

    Proof: xi mu_G(x) = integral of xi P_x(r.w) dw has positive real part.

The r = 1, xi = +-1 case is the localization, so this is a strict generalisation with b + 1
new parameters. The question is whether the extra freedom reaches the residue, that is the
points that lie in a gap of spec(T) and inside spec(G^ab), where r = 1 gives nothing.

The test is exact in the following sense: the image of the polytorus lies in an open
half-plane through the origin if and only if the angles of the sampled values span an arc
shorter than pi, which is checked by finding the largest circular gap between consecutive
angles and asking whether it exceeds pi. The grid can only make the arc look shorter than it
is, so a NO here is provisional while a YES is one refinement away from certain; the script
reports the arc length so the margin is visible.
"""

import sys
import math
import cmath
import itertools
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

GRAPHS = {
    'twotri': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)]),
    'theta': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3)]),
    'bowtie': (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]),
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
}
STEPS = 64
LOGR = [round(-1.2 + 0.15 * k, 3) for k in range(17)]      # log r from -1.2 to 1.2


def laurent(n, edges, cot, x, rz):
    """P_x on the polytorus of radii |rz|, sampled on a STEPS^b grid. rz is the vector of
    radii; the analytic continuation puts z_e on one direction and z_e^{-1} on the other."""
    b = len(cot)
    cotidx = {i: j for j, i in enumerate(cot)}
    A0 = np.zeros((n, n), dtype=complex)
    for i, (u, v) in enumerate(edges):
        if i not in cotidx:
            A0[u, v] += 1.0
            A0[v, u] += 1.0
    M = STEPS ** b
    A = np.broadcast_to(A0, (M, n, n)).copy()
    th = 2 * math.pi * np.arange(STEPS) / STEPS
    for i, (u, v) in enumerate(edges):
        if i in cotidx:
            j = cotidx[i]
            z = rz[j] * np.exp(1j * th[(np.arange(M) // (STEPS ** j)) % STEPS])
            A[:, u, v] += z
            A[:, v, u] += 1.0 / z
    return np.linalg.det(x * np.eye(n) - A)


def arc_length(vals, tol=1e-12):
    """Length of the shortest arc containing all sampled values. Returns 2*pi if some value
    is at the origin (no half-plane can work)."""
    if np.min(np.abs(vals)) < tol:
        return 2 * math.pi
    a = np.sort(np.angle(vals))
    gaps = np.diff(a)
    wrap = a[0] + 2 * math.pi - a[-1]
    g = max(float(gaps.max()) if gaps.size else 0.0, float(wrap))
    return 2 * math.pi - g


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    print(f"{'graph':>8}{'b':>3}{'x':>9}{'arc r=1':>10}{'best arc':>10}"
          f"{'best log r':>22}{'settled':>9}")
    for name, (n, edges) in GRAPHS.items():
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        if b > 2:
            print(f"{name:>8}{b:>3}   b > 2, radius search skipped")
            continue
        got = None
        for eta in (1e-4, 1e-3, 1e-2):
            es, ds, _ = scan(n, edges, -5.0, 5.0, 1000, eta=eta)
            if abs(kappa_above(es, ds, 1, -5.0) - 1.0) <= 0.03:
                got = (es, ds); break
        if got is None:
            print(f"{name:>8}{b:>3}   spec(T) unresolved"); continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.06]
        if not internal:
            print(f"{name:>8}{b:>3}   spec(T) has no internal gap"); continue
        for lo, hi in internal:
            for f in (0.25, 0.5, 0.75):
                x = lo + f * (hi - lo)
                a1 = arc_length(laurent(n, edges, cot, x, [1.0] * b))
                best, bestr = a1, [0.0] * b
                for lr in itertools.product(LOGR, repeat=b):
                    a = arc_length(laurent(n, edges, cot, x,
                                           [math.exp(t) for t in lr]))
                    if a < best:
                        best, bestr = a, list(lr)
                ok = best < math.pi - 1e-9
                print(f"{name:>8}{b:>3}{x:>9.4f}{a1:>10.4f}{best:>10.4f}"
                      f"{str(bestr):>22}{('YES' if ok else 'no'):>9}")
    print(f"\narc is the shortest arc containing the image; below pi = {math.pi:.4f} means")
    print("the image lies in an open half-plane and mu_G(x) != 0 follows. arc = 2 pi means")
    print("the image passes through the origin, so no half-plane can exist at that radius.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
