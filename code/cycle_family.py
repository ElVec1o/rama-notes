"""A third counterexample family, to break the sample dependence of D1.

All thirteen counterexamples supporting D1 come from two related constructions, both with a
star or tree skeleton, so the evidence is narrower than the table suggests. This builds a
family whose skeleton is a CYCLE: two-connected, no cut vertices at all, no high-degree
centre, and no leaves. If D1 survives here it is being tested against a different boundary
rather than a variation of the same one.

WHY THE BOUNDARY IS THE RIGHT THING TO VARY. By Godsil the roots of mu_G are eigenvalues of
the path tree of G, whose vertices are the paths out of a fixed vertex; that tree is an
induced finite subtree of the universal cover. So a root in a gap of spec(T) is an eigenvalue
of a finite subtree sitting in a gap of the ambient infinite tree, which is the surface-state
phenomenon: truncating a periodic operator produces states in its gaps, and how deep they sit
is a property of the boundary. Changing the skeleton from a tree to a cycle changes the
boundary, which is precisely the variable D1 should be stressed against.

CONSTRUCTION. A cycle C_L; at each cycle vertex, one gadget. With a triangle gadget sharing
its attachment vertex with the cycle, degrees are 4 on the cycle and 2 elsewhere, minimum
degree two and no cut vertex.

mu_G comes from the memoised vertex-deletion recursion, which is independent of the rooted
pair recursion used for the tree-skeleton family and was cross-checked against it on the
31-vertex graph. spec(T) comes from the Angel-Friedman-Hoory decay rate, with gap edges
located by scanning outward for the first crossing of rho = 1 and then bisecting inside that
bracket; plain bisection is invalid because rho drops below one again beyond the spectral
radius.
"""

import sys
import os
import math
import time
import random
import functools
import sympy as sp

CKPT = 'private/cycle_family_ckpt.txt'
x = sp.Symbol('x')


def cycle_gadget(L, gadget='triangle'):
    """Cycle C_L; each cycle vertex also carries a gadget."""
    edges = []
    cyc = list(range(L))
    for i in range(L):
        edges.append((cyc[i], cyc[(i + 1) % L]))
    n = L
    for i in range(L):
        if gadget == 'triangle':
            a, b = n, n + 1; n += 2
            edges += [(cyc[i], a), (a, b), (b, cyc[i])]
        elif gadget == 'square':
            a, b, c = n, n + 1, n + 2; n += 3
            edges += [(cyc[i], a), (a, b), (b, c), (c, cyc[i])]
        elif gadget == 'K23':
            # cycle vertex is one degree-2 side of K_{2,3}
            a, b, c, d = n, n + 1, n + 2, n + 3; n += 4
            edges += [(cyc[i], a), (cyc[i], b), (cyc[i], c),
                      (a, d), (b, d), (c, d)]
    return n, edges


def mu_memo(n, edges):
    """mu_G by memoised vertex deletion, independent of the pair recursion."""
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    sys.setrecursionlimit(200000)

    @functools.lru_cache(maxsize=None)
    def mu(vs):
        S = set(vs)
        if not S:
            return sp.Integer(1)
        v = min(S, key=lambda t: len(adj[t] & S))
        S1 = S - {v}
        tot = x * mu(tuple(sorted(S1)))
        for u in adj[v] & S:
            tot -= mu(tuple(sorted(S1 - {u})))
        return sp.expand(tot)
    return mu(tuple(range(n))), mu.cache_info().currsize


def setup(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    foll = [[idx[(b, c)] for c in adj[b] if c != a] for (a, b) in de]
    return foll, len(de)


def rho_at(lam, foll, M, iters=20000, tol=1e-12):
    h = [0.5] * M
    for _ in range(iters):
        new = [0.0] * M
        d = 0.0
        for k in range(M):
            s = lam
            for f in foll[k]:
                s -= h[f]
            if abs(s) < 1e-12:
                return None
            v = 1.0 / s
            d = max(d, abs(v - h[k])); new[k] = v
        h = new
        if d < tol:
            break
    else:
        return None
    random.seed(1)
    vec = [random.random() + 0.1 for _ in range(M)]
    r2 = 0.0
    for _ in range(3000):
        w1 = [h[k] * h[k] * sum(vec[f] for f in foll[k]) for k in range(M)]
        w2 = [h[k] * h[k] * sum(w1[f] for f in foll[k]) for k in range(M)]
        nr = max(abs(t) for t in w2)
        if nr == 0:
            return 0.0
        vec = [t / nr for t in w2]
        r2 = nr
    return math.sqrt(r2)


def edge_toward(theta, foll, M, direction, span=0.6, step=0.004, tol=1e-6):
    prev, t = theta, theta
    good = bad = None
    while abs(t - theta) < span:
        t += direction * step
        r = rho_at(t, foll, M)
        if r is None or r >= 1:
            good, bad = prev, t; break
        prev = t
    if good is None:
        return None
    for _ in range(40):
        if abs(bad - good) < tol:
            break
        mid = (good + bad) / 2
        r = rho_at(mid, foll, M)
        if r is not None and r < 1:
            good = mid
        else:
            bad = mid
    return good


def main():
    print("third family: cycle skeleton, two-connected, no leaves, no cut vertices\n",
          flush=True)
    print(f"{'case':>18}{'n':>5}{'dmin':>5}{'dmax':>5}{'root':>10}"
          f"{'defect':>11}{'width':>9}{'verdict':>9}", flush=True)
    rows = []
    t0 = time.time()
    for gadget in ('triangle', 'square', 'K23'):
        for L in range(3, 13):
            n, edges = cycle_gadget(L, gadget)
            if n > 46:
                continue
            deg = [0] * n
            for a, b in edges:
                deg[a] += 1; deg[b] += 1
            muG, sub = mu_memo(n, edges)
            co = sp.Poly(muG, x).all_coeffs()
            while co and co[-1] == 0:
                co.pop()
            if len(co) < 2:
                continue
            try:
                roots = [float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=18, maxsteps=2500)
                         if abs(sp.im(r)) < 1e-9 and sp.re(r) > 1e-9]
            except Exception:
                continue
            foll, M = setup(n, edges)
            found = False
            for th in roots:
                r = rho_at(th, foll, M)
                if r is None or r >= 1:
                    continue
                lo = edge_toward(th, foll, M, -1)
                hi = edge_toward(th, foll, M, +1)
                if lo is None or hi is None:
                    continue
                defect = min(th - lo, hi - th)
                rows.append((f"{gadget} C{L}", n, th, defect, hi - lo))
                print(f"{gadget+' C'+str(L):>18}{n:>5}{min(deg):>5}{max(deg):>5}"
                      f"{th:>10.5f}{defect:>11.6f}{hi-lo:>9.5f}{'GAP':>9}", flush=True)
                found = True
            if not found:
                print(f"{gadget+' C'+str(L):>18}{n:>5}{min(deg):>5}{max(deg):>5}"
                      f"{'-':>10}{'-':>11}{'-':>9}{'in spec':>9}", flush=True)
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"{gadget} L={L} rows={len(rows)}\n")
            os.replace(CKPT + '.tmp', CKPT)
    print(f"\n{time.time()-t0:.0f}s")
    if rows:
        d = [r[3] for r in rows]
        print(f"third-family defects: min {min(d):.6f}  max {max(d):.6f}  ({len(rows)} points)")
        print("D1 survives here if these stay below the 0.035 seen in the first two families.")
    else:
        print("no counterexample in the cycle family; D1 untested against this boundary.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
