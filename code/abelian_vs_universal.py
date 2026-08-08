"""Does the universal-cover gap label equal the abelian band count?

The research log claimed (entry G25) that delta = delta_ab off spec(G^ab), proved by
pushing the negative spectral projection through a *-homomorphism C*_r(F_b) -> C(T^b).
THAT MAP DOES NOT EXIST. For N normal in Gamma, the quotient descends to reduced
C*-algebras iff N is amenable, not iff Gamma/N is. Here N = [F_b, F_b] is free of infinite
rank for b >= 2, hence not amenable.

The premise is refutable outright, not merely unsupported. A unital *-homomorphism does not
increase spectra, so if pi existed then S(x) invertible would force S(x,z) invertible for
every z, hence det(xI - A_G(z)) = mu_F(x) det S(x,z) nonzero for every z, hence
spec(G^ab) contained in spec(T) union the roots of mu_F. For K_4 with a two-element
feedback set, x = 3 is the Perron eigenvalue of A_G, so 3 is in spec(G^ab), while
rho(T) = 2 sqrt 2 < 3 and mu_{K_2}(3) = 8. Contradiction.

So the PROOF of G25 is retracted. This script asks whether the CONCLUSION survives, by
computing both sides independently:

  c(x)     = number of eigenvalues of A_G(z) above x, which is z-independent off spec(G^ab),
             obtained by diagonalising the magnetic adjacency matrix over a grid of phases;
  kappa(x) = n * (universal cover density integrated above x), from the cavity solver.

Equality of these two is equivalent to delta = delta_ab, since Haynsworth gives
kappa = N_F + delta on the free side and scalar inertia additivity gives c = N_F + delta_ab
on the abelian side. They are counts for genuinely different operators, so equality is a
claim and not a triviality.
"""

import sys
import math
import cmath
import numpy as np

sys.path.insert(0, 'code')


def spanning_tree(n, edges):
    """Return (tree_edge_indices, cotree_edge_indices)."""
    par = list(range(n))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    tree, cot = [], []
    for i, (u, v) in enumerate(edges):
        ru, rv = find(u), find(v)
        if ru != rv:
            par[ru] = rv
            tree.append(i)
        else:
            cot.append(i)
    return tree, cot


def magnetic(n, edges, cot, thetas):
    A = np.zeros((n, n), dtype=complex)
    ph = {}
    for j, i in enumerate(cot):
        ph[i] = thetas[j]
    for i, (u, v) in enumerate(edges):
        w = cmath.exp(1j * ph.get(i, 0.0))
        A[u, v] += w
        A[v, u] += w.conjugate()
    return A


def abelian_spectrum(n, edges, steps):
    """All eigenvalues over a phase grid, plus a function giving the count above x."""
    tree, cot = spanning_tree(n, edges)
    b = len(cot)
    evs = []
    counts = []
    grid = [2 * math.pi * k / steps for k in range(steps)]
    idx = [0] * b
    total = steps ** b
    for t in range(total):
        th = []
        r = t
        for _ in range(b):
            th.append(grid[r % steps])
            r //= steps
        w = np.linalg.eigvalsh(magnetic(n, edges, cot, th))
        evs.append(w)
    return np.array(evs), b


def c_of(evs, x):
    """Counts of eigenvalues above x, one per phase point."""
    return np.sum(evs > x, axis=1)


GRAPHS = {
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)]),
    'theta': (5, [(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4)]),
    'K4+pendant': (8, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                       (0, 4), (1, 5), (2, 6), (3, 7)]),
}


def main():
    src = open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:')
    ns = {}
    exec(src, ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    print(f"{'graph':<13}{'b':>2}{'abelian gap x':>15}{'c(x)':>7}{'kappa(x)':>11}"
          f"{'c==kappa?':>11}")
    for name, (n, edges) in GRAPHS.items():
        steps = 24 if len(edges) - n + 1 <= 2 else 12
        evs, b = abelian_spectrum(n, edges, steps)
        lo, hi = evs.min(), evs.max()
        # An abelian gap is exactly where the count above x does not depend on the phase.
        # Using distance to the nearest sampled eigenvalue instead is wrong: a coarse phase
        # grid misses band interiors and reports them as gaps, which is what the earlier
        # version of this script did.
        xs = np.linspace(lo - 1.0, hi + 1.0, 2000)
        gapxs = []
        for x in xs:
            cc = np.sum(evs > x, axis=1)
            if cc.min() == cc.max():
                gapxs.append(x)
        # cluster gap points and take midpoints
        probes = []
        if gapxs:
            start = gapxs[0]
            prev = gapxs[0]
            for x in gapxs[1:]:
                if x - prev > 0.01:
                    probes.append(0.5 * (start + prev))
                    start = x
                prev = x
            probes.append(0.5 * (start + prev))
        # universal side
        R = max(4.0, abs(lo) + 1.5, abs(hi) + 1.5)
        got = None
        for eta in (1e-6, 1e-4, 1e-3, 1e-2):
            es, ds, bad = scan(n, edges, -R, R, 3000, eta=eta)
            mass = kappa_above(es, ds, 1, -R)
            if abs(mass - 1.0) <= 0.02:
                got = (es, ds)
                break
        if got is None:
            print(f"{name:<13}{b:>2}   solver gated, no numbers")
            continue
        es, ds = got
        for x in probes:
            cc = c_of(evs, x)
            if cc.min() != cc.max():
                verdict = f"c not constant ({cc.min()}..{cc.max()})"
                cval = -1
            else:
                cval = int(cc[0])
                verdict = ""
            k = kappa_above(es, ds, n, x)
            same = (cval == round(k)) if cval >= 0 else False
            print(f"{name:<13}{b:>2}{x:>15.4f}{cval:>7}{k:>11.4f}"
                  f"{('YES' if same else 'NO'):>11}  {verdict}")
        print()
    return 0


if __name__ == '__main__':
    sys.exit(main())
