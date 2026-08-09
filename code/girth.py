"""The quantitative form: the defect should decay exponentially in the girth.

WHERE THE PREDICTION COMES FROM. By Godsil a root theta of mu_G is an eigenvalue of the path
tree P, the tree of self-avoiding walks from a fixed vertex, which is an INDUCED subtree of the
universal cover T. Let psi be the eigenvector and psi~ its extension by zero to T. For u in P
every T-neighbour of u lies in P or contributes nothing, so (A_T - theta) psi~ vanishes on P and
is supported on T minus P, where its value at u is the sum of psi over the P-neighbours of u.
Hence

    dist(theta, spec T)  <=  || (A_T - theta) psi~ ||  /  || psi~ ||,

which is the boundary flux of the path-tree eigenvector. That is exact, and it is the
quantitative statement Conjecture 10 was the qualitative version of.

Now the two structural facts. A vertex of P is a path (v, ..., v_k), and it fails to have its
full set of T-children exactly when some neighbour of v_k already lies on the path, that is when
the path closes a cycle. The shortest such path has length the GIRTH. So the boundary of P sits
at depth at least girth(G) - 1. And theta lies in a gap, so the Angel-Friedman-Hoory decay rate
rho(theta) is below one and the eigenvector decays into the tree at that rate. Together:

    dist(theta, spec T)  <~  C rho^{girth}.

FROZEN BEFORE THE DATA:
  G1. The defect decays exponentially in the girth, at a rate at most the AFH decay rate.

This is testable now, and it is testable against the counterexamples we already have, all of
which have small girth: the 31-vertex graph has triangles, and every 2-cut graph contains
K_{2,q} and so has girth four.

THE FAMILY. A hub carrying p branches, each branch a cycle C_L joined to the hub by a path of T
vertices. The girth is exactly L and is tunable independently of everything else, which is what
makes this a test of G1 rather than of the construction.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import functools
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gapscale import setup, rho_at, gap_profile

x = sp.Symbol('x')
BUDGET = 1500.0
CKPT = 'private/girth_ckpt.txt'


def girth(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    best = 10 ** 9
    for s in range(n):
        dist = {s: 0}; par = {s: None}; q = [s]
        while q:
            u = q.pop(0)
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; par[w] = u; q.append(w)
                elif w != par[u]:
                    best = min(best, dist[u] + dist[w] + 1)
        if best == 3:
            break
    return best


def cycle_branch_hub(p, L, T):
    """hub, p branches; each branch is C_L joined to the hub by a path of T vertices."""
    edges, n = [], 1
    for _ in range(p):
        cyc = list(range(n, n + L)); n += L
        for i in range(L):
            edges.append((cyc[i], cyc[(i + 1) % L]))
        prev = cyc[0]
        for _ in range(T):
            edges.append((prev, n)); prev = n; n += 1
        edges.append((0, prev))
    return n, edges


def mu_memo(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    sys.setrecursionlimit(300000)

    @functools.lru_cache(maxsize=None)
    def rec(vs):
        S = set(vs)
        if not S:
            return sp.Integer(1)
        v = min(S, key=lambda z: len(adj[z] & S))
        S1 = S - {v}
        t = x * rec(tuple(sorted(S1)))
        for u in adj[v] & S:
            t -= rec(tuple(sorted(S1 - {u})))
        return sp.expand(t)
    return rec(tuple(range(n)))


def edge_toward(theta, B, M, direction, span=0.7, step=0.004, tol=1e-7):
    prev, t, good, bad = theta, theta, None, None
    while abs(t - theta) < span:
        t += direction * step
        r = rho_at(t, B, M)
        if r is None or r >= 1:
            good, bad = prev, t; break
        prev = t
    if good is None:
        return None
    for _ in range(45):
        if abs(bad - good) < tol:
            break
        mid = (good + bad) / 2
        r = rho_at(mid, B, M)
        if r is not None and r < 1:
            good = mid
        else:
            bad = mid
    return good


def main():
    print("G1 (frozen): the defect decays exponentially in the girth.\n")
    print(f"{'p':>3}{'L':>3}{'T':>3}{'n':>5}{'girth':>7}{'theta':>10}{'rho':>9}"
          f"{'defect':>11}{'log10 def':>11}")
    t0 = time.time()
    rows = []
    for T in (1, 2):
        for p in (3, 4, 5):
            for L in range(3, 13):
                n = 1 + p * (L + T)
                if n > 58 or time.time() - t0 > BUDGET:
                    continue
                edges = cycle_branch_hub(p, L, T)[1]
                gr = girth(n, edges)
                co = sp.Poly(mu_memo(n, edges), x).all_coeffs()
                while co and co[-1] == 0:
                    co.pop()
                if len(co) < 2:
                    continue
                try:
                    roots = [float(sp.re(r)) for r in
                             sp.Poly(co, x).nroots(n=22, maxsteps=4000)
                             if abs(sp.im(r)) < 1e-11 and sp.re(r) > 1e-9]
                except Exception:
                    continue
                B, M = setup(n, edges)
                best = None
                for th in roots:
                    r = rho_at(th, B, M)
                    if r is None or r >= 1:
                        continue
                    lo = edge_toward(th, B, M, -1)
                    hi = edge_toward(th, B, M, +1)
                    if lo is None or hi is None:
                        continue
                    d = min(th - lo, hi - th)
                    if best is None or d > best[2]:
                        best = (th, r, d)
                if best is None:
                    print(f"{p:>3}{L:>3}{T:>3}{n:>5}{gr:>7}{'-':>10}{'-':>9}"
                          f"{'no gap root':>11}{'':>11}", flush=True)
                    continue
                th, r, d = best
                rows.append((p, L, T, n, gr, th, r, d))
                print(f"{p:>3}{L:>3}{T:>3}{n:>5}{gr:>7}{th:>10.5f}{r:>9.5f}"
                      f"{d:>11.7f}{math.log10(max(d,1e-16)):>11.3f}", flush=True)
                with open(CKPT + '.tmp', 'w') as f:
                    f.write(f"p={p} L={L} T={T} rows={len(rows)}\n")
                os.replace(CKPT + '.tmp', CKPT)

    print(f"\n{time.time()-t0:.0f}s,  {len(rows)} counterexamples\n")
    if len(rows) < 4:
        print("too few points to test G1.")
        return 0
    print("  defect against girth, grouped:")
    print(f"{'girth':>7}{'#':>4}{'max defect':>13}{'min defect':>13}{'mean rho':>10}")
    for g in sorted({r[4] for r in rows}):
        sel = [r for r in rows if r[4] == g]
        print(f"{g:>7}{len(sel):>4}{max(s[7] for s in sel):>13.7f}"
              f"{min(s[7] for s in sel):>13.7f}{np.mean([s[6] for s in sel]):>10.5f}")
    gs = np.array([r[4] for r in rows], float)
    ds = np.log(np.array([r[7] for r in rows]))
    A = np.vstack([gs, np.ones_like(gs)]).T
    slope, icpt = np.linalg.lstsq(A, ds, rcond=None)[0]
    rate = math.exp(slope)
    mean_rho = float(np.mean([r[6] for r in rows]))
    print(f"\n  log(defect) = {slope:.4f} * girth + {icpt:.4f}")
    print(f"  implied decay per unit girth: {rate:.5f}   (mean AFH rho = {mean_rho:.5f})")
    if slope < -0.05:
        print(f"\n  G1 HOLDS: the defect decays exponentially in girth, at rate {rate:.4f}.")
        print("  Every counterexample must therefore have small girth, which is what we see:")
        print("  the 31-vertex graph has triangles and every 2-cut graph contains K_{2,q}.")
        if rate <= mean_rho + 0.05:
            print(f"  The rate is at most the AFH decay rate, as predicted.")
        else:
            print(f"  But the rate {rate:.4f} EXCEEDS the AFH rate {mean_rho:.4f}: the decay is "
                  "real, the predicted mechanism for it is not confirmed.")
    else:
        print("\n  G1 FAILS: the defect does not decay in girth.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
