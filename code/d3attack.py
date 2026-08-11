"""Attacking D3 where the gap is widest: large degree contrast at minimum degree three.

D3 says minimum degree three suffices for Conjecture 10. The widest gaps available at minimum
degree three come from degree CONTRAST, not low degree: the universal cover of an
(a,b)-biregular graph is the (a,b)-biregular tree, whose spectrum is {0} together with

    +/- [ |sqrt(a-1) - sqrt(b-1)| , sqrt(a-1) + sqrt(b-1) ],

so there is a gap around zero of half-width g = |sqrt(a-1) - sqrt(b-1)|. For (3,q) that is
sqrt(q-1) - sqrt 2, which grows without bound. A root of mu_G with 0 < |theta| < g refutes D3.
It would also settle Song, Fan and Miao's Problem 1, which the biregular case of Conjecture 10
is equivalent to.

PART A, the analytic probe. For K_{3,q} the matching polynomial factors: with y = x^2,

    mu = x^{q-3} ( y^3 - 3q y^2 + 3q(q-1) y - q(q-1)(q-2) ),

so the smallest positive root is exactly computable for any q. Setting y = q(1+e) the cubic
becomes e^3 - 3e/q - 2/q^2 = 0 to leading order, giving e = -sqrt3/sqrt q and

    x_min  ~  sqrt q - sqrt3 / 2  =  sqrt q - 0.866,
    g      ~  sqrt q - sqrt 2     =  sqrt q - 1.414,

so the margin x_min - g tends to sqrt2 - sqrt3/2 = 0.548 and never closes. K_{3,q} alone
cannot refute D3, but the margin is a CONSTANT, not growing, so a perturbation worth 0.55 in
the smallest root would do it. Part A checks the asymptotic claim numerically and reports the
margin, which is the budget any refutation has to beat.

PART B spends that budget. Genuine (3,q)-biregular graphs that are not complete bipartite have
more structure and a different smallest root; they are built from balanced 3-uniform designs on
r right vertices, every left vertex of degree three and every right vertex of degree q.

PART C changes the tuning knob. Every engine so far resonates by varying the branch COUNT p.
At minimum degree three that has failed, so here the branches themselves are varied: two hubs
carrying p1 branches of one type and p2 of another, which turns one knob into two. With
distinct branches the 2-cut expansion reads

    mu_G = x^2 prod A_i - x sum_i (Bu_i + Bv_i) prod_{j!=i} A_j
           + sum_i D_i prod_{j!=i} A_j + sum_{i!=j} Bu_i Bv_j prod_{k!=i,j} A_k,

checked against a brute-force matching polynomial before use.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import itertools
import functools
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twocut import branch_data, mu_of, x
from gapscale import setup, rho_at, gap_profile, connectivity
from mindeg3 import br_ladder, br_K3q, br_prism, br_ladder_mid
import quickmode

BUDGET = quickmode.budget(1400.0, 25.0)
CKPT = quickmode.ckpt('private/d3attack_ckpt.txt')
# ------------------------------------------------------------------ A: the analytic probe
def partA():
    print("A. K_{3,q}: smallest positive root against the gap edge sqrt(q-1)-sqrt(2)\n")
    print(f"{'q':>6}{'x_min':>12}{'gap edge g':>13}{'margin':>11}{'x_min-sqrt(q)':>15}")
    worst = None
    for q in (4, 6, 9, 12, 20, 40, 80, 200, 500, 2000, 20000):
        y = sp.Symbol('y')
        cub = y**3 - 3*q*y**2 + 3*q*(q-1)*y - q*(q-1)*(q-2)
        rts = [complex(r) for r in sp.Poly(cub, y).nroots(n=30, maxsteps=4000)]
        ys = sorted(r.real for r in rts if abs(r.imag) < 1e-12 and r.real > 1e-12)
        if not ys:
            continue
        xmin = math.sqrt(ys[0])
        g = math.sqrt(q - 1) - math.sqrt(2)
        m = xmin - g
        print(f"{q:>6}{xmin:>12.6f}{g:>13.6f}{m:>11.6f}{xmin-math.sqrt(q):>15.6f}")
        if worst is None or m < worst[1]:
            worst = (q, m)
    print(f"\n  predicted limits: x_min - sqrt(q) -> -sqrt(3)/2 = {-math.sqrt(3)/2:.6f}, "
          f"margin -> sqrt(2)-sqrt(3)/2 = {math.sqrt(2)-math.sqrt(3)/2:.6f}")
    print(f"  smallest margin seen: {worst[1]:.6f} at q={worst[0]}")
    print("  => a refutation from this direction must move the smallest root by that much.\n")
    return worst[1]


# ------------------------------------------------------------------ B: real biregular graphs
def biregular_design(r, t):
    """left vertices are the 3-subsets of [r], each taken t times; right degree is
    t*C(r-1,2), left degree 3, and the graph is connected for r >= 3."""
    trips = list(itertools.combinations(range(r), 3))
    edges, n = [], r
    for _ in range(t):
        for T in trips:
            for a in T:
                edges.append((a, n))
            n += 1
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
        tot = x * rec(tuple(sorted(S1)))
        for u in adj[v] & S:
            tot -= rec(tuple(sorted(S1 - {u})))
        return sp.expand(tot)
    return rec(tuple(range(n)))


def roots_of(muG):
    co = sp.Poly(muG, x).all_coeffs()
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return []
    try:
        return sorted(float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=22, maxsteps=4000)
                      if abs(sp.im(r)) < 1e-11 and sp.re(r) > 1e-9)
    except Exception:
        return []


def partB(t0):
    print("B. genuine (3,q)-biregular graphs, from balanced 3-uniform designs\n")
    print(f"{'r':>3}{'t':>3}{'n':>5}{'q':>5}{'kappa':>6}{'gap edge':>10}"
          f"{'x_min':>11}{'margin':>10}{'verdict':>11}")
    hits = []
    for r in (4, 5, 6, 7):
        for t in (1, 2, 3):
            n, edges = biregular_design(r, t)
            if n > 44 or time.time() - t0 > BUDGET:
                continue
            adj = {i: set() for i in range(n)}
            for a, b in edges:
                adj[a].add(b); adj[b].add(a)
            deg = [len(adj[i]) for i in range(n)]
            if min(deg) < 3:
                continue
            q = max(deg)
            g = math.sqrt(q - 1) - math.sqrt(2)
            if g <= 0.02:
                continue
            kap = connectivity(n, edges)
            rts = roots_of(mu_memo(n, edges))
            if not rts:
                continue
            xmin = rts[0]
            B, M = setup(n, edges)
            bad = None
            if xmin < g:
                rr = rho_at(xmin, B, M)
                if rr is not None and rr < 1:
                    bad = (xmin, rr)
            print(f"{r:>3}{t:>3}{n:>5}{q:>5}{kap:>6}{g:>10.5f}{xmin:>11.6f}"
                  f"{xmin-g:>10.5f}{('VIOLATION' if bad else 'clean'):>11}", flush=True)
            if bad:
                hits.append((f"design r={r} t={t}", n, q, kap, xmin, g, bad[1]))
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"B r={r} t={t} hits={len(hits)}\n")
            os.replace(CKPT + '.tmp', CKPT)
    print()
    return hits


# ------------------------------------------------------------------ C: two branch types
def mu_mixed(specs, p_list):
    """2-cut expansion with DISTINCT branches: specs[i]=(A,Bu,Bv,D), p_list[i] copies."""
    A, Bu, Bv, D = [], [], [], []
    for (a, bu, bv, d), p in zip(specs, p_list):
        A += [a] * p; Bu += [bu] * p; Bv += [bv] * p; D += [d] * p
    N = len(A)
    prodA = sp.Integer(1)
    for a in A:
        prodA *= a
    # prod over all except i, and except i,j -- built by division in the polynomial ring
    def without(idxs):
        r = sp.Integer(1)
        for i in range(N):
            if i not in idxs:
                r *= A[i]
        return r
    tot = x**2 * prodA
    for i in range(N):
        wi = without({i})
        tot += -x * (Bu[i] + Bv[i]) * wi + D[i] * wi
    for i in range(N):
        for j in range(N):
            if i != j:
                tot += Bu[i] * Bv[j] * without({i, j})
    return sp.expand(tot)


def assemble_mixed(brs, p_list):
    edges, n = [], 2
    for (nb, be, Su, Sv), p in zip(brs, p_list):
        for _ in range(p):
            for a, b in be:
                edges.append((a + n, b + n))
            for w in Su:
                edges.append((0, w + n))
            for w in Sv:
                edges.append((1, w + n))
            n += nb
    return n, edges


def partC(t0):
    print("C. two hubs, TWO branch types: tuning the branches instead of the count\n")
    TYPES = [("lad3", br_ladder(3)), ("lad4", br_ladder(4)), ("lad5", br_ladder(5)),
             ("K3,3", br_K3q(3)), ("K3,4", br_K3q(4)), ("K3,5", br_K3q(5)),
             ("prism4", br_prism(4)), ("ladM4", br_ladder_mid(4))]
    # self-check the mixed expansion against brute force
    b1, b2 = TYPES[0][1], TYPES[3][1]
    s1 = branch_data(*b1); s2 = branch_data(*b2)
    n, edges = assemble_mixed([b1, b2], [2, 1])
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    ok = sp.expand(mu_mixed([s1, s2], [2, 1]) - mu_of(adj, set(range(n)))) == 0
    print(f"  mixed-branch expansion self-check (n={n}): {'OK' if ok else 'MISMATCH'}\n",
          flush=True)
    if not ok:
        return []
    print(f"{'types':>16}{'p1':>3}{'p2':>3}{'n':>5}{'dmin':>5}{'kappa':>6}"
          f"{'#gaps':>6}{'maxgap':>8}{'verdict':>11}")
    hits = []
    cache = {}
    for (n1, br1), (n2, br2) in itertools.combinations(TYPES, 2):
        if time.time() - t0 > BUDGET:
            print("  [budget reached]"); break
        for k in (n1, n2):
            pass
        s1 = cache.setdefault(n1, branch_data(*br1))
        s2 = cache.setdefault(n2, branch_data(*br2))
        for p1 in range(1, 6):
            for p2 in range(1, 6):
                if p1 + p2 < 3:
                    continue
                n, edges = assemble_mixed([br1, br2], [p1, p2])
                if n > 50 or time.time() - t0 > BUDGET:
                    continue
                adj = {i: set() for i in range(n)}
                for a, b in edges:
                    adj[a].add(b); adj[b].add(a)
                deg = [len(adj[i]) for i in range(n)]
                if min(deg) < 3:
                    continue
                g = [t for t in gap_profile(n, edges) if t[1] - t[0] >= 0.05]
                if not g:
                    continue
                kap = connectivity(n, edges)
                rts = roots_of(mu_mixed([s1, s2], [p1, p2]))
                B, M = setup(n, edges)
                bad = None
                for th in rts:
                    for (lo, hi) in g:
                        if lo < th < hi:
                            rr = rho_at(th, B, M)
                            if rr is not None and rr < 1:
                                bad = (th, min(th - lo, hi - th), rr)
                print(f"{n1+'/'+n2:>16}{p1:>3}{p2:>3}{n:>5}{min(deg):>5}{kap:>6}"
                      f"{len(g):>6}{max(t[1]-t[0] for t in g):>8.3f}"
                      f"{('VIOLATION' if bad else 'clean'):>11}", flush=True)
                if bad:
                    hits.append((f"{n1}/{n2}", p1, p2, n, kap, bad))
                with open(CKPT + '.tmp', 'w') as f:
                    f.write(f"C {n1}/{n2} p={p1},{p2} hits={len(hits)}\n")
                os.replace(CKPT + '.tmp', CKPT)
    return hits


def main():
    t0 = time.time()
    margin = partA()
    hb = partB(t0)
    hc = partC(t0)
    print(f"\n{time.time()-t0:.0f}s")
    if hb or hc:
        print(f"\nD3 IS REFUTED: {len(hb)+len(hc)} counterexamples of minimum degree three.")
        for h in hb:
            print(f"  {h[0]} n={h[1]} q={h[2]} kappa={h[3]} theta={h[4]:.6f} "
                  f"gap edge={h[5]:.6f} rho={h[6]:.6f}")
        for nm, p1, p2, n, kap, (th, df, rr) in hc:
            print(f"  {nm} p=({p1},{p2}) n={n} kappa={kap} theta={th:.6f} "
                  f"defect={df:.6f} rho={rr:.6f}")
    else:
        print(f"\nD3 survives both attacks.  The K_{{3,q}} margin is {margin:.4f} and does not "
              "close;\n  no biregular design and no mixed-branch resonator reaches into a gap.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
