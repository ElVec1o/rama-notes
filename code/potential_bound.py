"""Is the Mahler measure Delta bounded below in a way that survives growing n?

G44 needs Delta > 2 I_wrong. The Mahler route of MahlerRoute.lean would get there from a
Newton-polytope coefficient, which requires identifying a coefficient that never vanishes.
There is a second route that needs no coefficient at all. Since

    det(x I - A_G(z)) = prod_k ( x - lambda_k(z) ),

averaging the logarithm over the torus gives

    log M(P_x) = sum_k integral log |x - lambda_k(z)| dz = n * integral log|x - t| d rho_ab(t),

the logarithmic potential of the density of states of the maximal abelian cover, and

    Delta = M(P_x) / |mu_F(x)|.

Potential theory bounds this below with no reference to mu_G: a probability measure with
density at most D has log-potential at least -log(2D) - 1 at every point, the worst case
being all admissible mass packed against x. That gives

    log Delta  >=  -n (log(2D) + 1) - log|mu_F(x)|,

unconditional, but with n in the exponent. The upper half gives I_wrong <= M L c^{-1/2}
m^{3/2}, whose constants also grow with n, so whether the comparison is n-uniform is an
empirical question before it is a theorem.

This script measures, at gap midpoints of spec(T):

    logDelta   what has to stay bounded below,
    K          how many bands actually contain x, which is what drives the exponent,
    minpot     the most negative single-band potential, the term that could blow up,
    Dloc       the local density of states of the abelian cover at x,
    bound      the potential lower bound -n(log(2 Dloc) + 1) - log|mu_F(x)|.

If logDelta drifts down linearly in n the route needs the constants on the other side to
drift with it. If it stays flat while the bound falls, the bound is lossy but the truth is
fine, and the useful theorem is a bound on K rather than on n.
"""

import sys
import os
import math
import cmath
import itertools
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

STEPS = 40          # torus grid per direction; b = 2 so 1600 points


def connected(n, edges):
    adj = {i: [] for i in range(n)}
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    seen, st = {0}, [0]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == n


def is_forest(n, edges):
    par = list(range(n))

    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for u, v in edges:
        ru, rv = f(u), f(v)
        if ru == rv:
            return False
        par[ru] = rv
    return True


def fvs2_pair(n, edges):
    for a in range(n):
        for b_ in range(a + 1, n):
            keep = [(u, v) for u, v in edges if u not in (a, b_) and v not in (a, b_)]
            if is_forest(n, keep):
                return (a, b_)
    return None


def sample():
    """Two controlled families with b = 2 and feedback vertex number 2, so that n grows
    while the structure stays fixed. A lexicographic sweep over all graphs of a given order
    returns near-duplicates with no internal gap, which measures nothing."""
    # two triangles joined by a path with L edges
    for L in range(1, 7):
        e = [(0, 1), (1, 2), (2, 0)]
        prev = 0
        nxt = 6
        path = []
        for i in range(L - 1):
            path.append(nxt); nxt += 1
        chain = [0] + path + [3]
        for a, b_ in zip(chain, chain[1:]):
            e.append((a, b_))
        e += [(3, 4), (4, 5), (5, 3)]
        n = 6 + (L - 1)
        e = [(min(a, b_), max(a, b_)) for a, b_ in e]
        yield f"tri-P{L}-tri", n, e, (1, 4)
    # two cycles of length c joined by an edge
    for c in range(3, 8):
        e = [(i, (i + 1) % c) for i in range(c)]
        e += [(c + i, c + (i + 1) % c) for i in range(c)]
        e.append((0, c))
        n = 2 * c
        e = [(min(a, b_), max(a, b_)) for a, b_ in e]
        yield f"C{c}-e-C{c}", n, e, (1, c + 1)


def bandwise(n, edges, cot, x, steps):
    """Per-band log potentials at x, the band ranges, and a local density estimate."""
    grid = [2 * math.pi * k / steps for k in range(steps)]
    lam = np.empty((steps * steps, n))
    t = 0
    for a in grid:
        for b2 in grid:
            lam[t] = np.linalg.eigvalsh(magnetic(n, edges, cot, [a, b2]))
            t += 1
    pot = np.mean(np.log(np.abs(lam - x) + 1e-300), axis=0)     # one per band
    lo, hi = lam.min(axis=0), lam.max(axis=0)
    K = int(np.sum((lo <= x) & (x <= hi)))
    # local density of states: fraction of all n * steps^2 eigenvalues within h of x, over 2h
    h = 0.05
    Dloc = float(np.sum(np.abs(lam - x) <= h)) / (lam.size * 2 * h)
    return pot, K, Dloc


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    print(f"{'n':>3}{'b':>3}{'x':>9}{'K':>4}{'logDelta':>10}{'sumpot':>9}"
          f"{'minpot':>9}{'Dloc':>7}{'bound':>9}")
    rows = []
    for name, n, edges, W in sample():
        nF, eF = delete(n, edges, set(W))
        cF = matching_coeffs(nF, eF)
        tree, cot = spanning_tree(n, edges)
        if len(cot) != 2:
            continue
        R = 5.0
        got = None
        for eta in (1e-4, 1e-3, 1e-2):
            es, ds, _ = scan(n, edges, -R, R, 700, eta=eta)
            if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.03:
                got = (es, ds); break
        if got is None:
            continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.08]
        for lo, hi in internal:
            x = 0.5 * (lo + hi)
            pot, K, Dloc = bandwise(n, edges, cot, x, STEPS)

            def ev(c, t):
                a = 0.0
                for j in range(len(c) - 1, -1, -1):
                    a = a * t + c[j]
                return a
            muF = abs(ev(cF, x))
            if muF < 1e-12:
                continue
            logDelta = float(pot.sum()) - math.log(muF)
            bound = -n * (math.log(2 * max(Dloc, 1e-6)) + 1) - math.log(muF)
            print(f"{n:>3}{2:>3}{x:>9.4f}{K:>4}{logDelta:>10.4f}{pot.sum():>9.4f}"
                  f"{pot.min():>9.4f}{Dloc:>7.3f}{bound:>9.2f}   {name}")
            rows.append((n, K, logDelta, float(pot.min())))

    if not rows:
        print("no gap points"); return 0
    print("\nby vertex count:")
    print(f"{'n':>3}{'pts':>5}{'min logDelta':>14}{'mean logDelta':>15}{'max K':>7}")
    for n in sorted({r[0] for r in rows}):
        v = [r for r in rows if r[0] == n]
        print(f"{n:>3}{len(v):>5}{min(r[2] for r in v):>14.4f}"
              f"{sum(r[2] for r in v)/len(v):>15.4f}{max(r[1] for r in v):>7}")
    print("\nlogDelta must stay bounded below for the potential route to be n-uniform.")
    print("K counts the bands containing x and is what the exponent should really involve.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
