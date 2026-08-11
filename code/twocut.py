"""The 2-cut attack on C1.

C1 says every 2-connected finite graph satisfies Conjecture 10. The evidence is that the
mechanism needs a cut vertex, since every counterexample runs on

    mu_G = mu_H^{p-1} ( x mu_H - p mu_{H-v} ),

which exists only because one vertex separates the graph. But 2-connected is not the same as
having no separation: a 2-connected graph can still have a 2-VERTEX separator, and a 2-cut
supports its own recurrence. If C1 is false, this is how it dies.

THE CONSTRUCTION. Two hubs u and v, and p identical branches, each attached to both hubs.
Removing u leaves everything joined through v and vice versa, so there is no cut vertex at all,
yet {u, v} separates the graph into p pieces.

THE RECURRENCE. Deleting u and then v, with A = mu_B the branch polynomial, Bu and Bv the sums
of mu_{B-w} over the hub neighbours in the branch, and D the sum of mu_{B-w-w'} over pairs
with w a neighbour of u and w' of v,

    mu_G = A^{p-2} [ x^2 A^2 - p x (Bu + Bv) A + p D A + p(p-1) Bu Bv ].

The bracket is QUADRATIC in p where the cut-vertex version was linear, so a 2-cut offers MORE
tuning freedom, not less. That is what makes this the attack most likely to break C1.

The identity is checked against a brute-force matching polynomial before it is used, and the
branch quantities A, Bu, Bv, D are computed by brute force too, so any branch can be dropped in.
Every candidate root is tested against spec(T) by the Angel-Friedman-Hoory decay rate, with gap
edges bracketed by an outward scan before bisection, and the graph is verified to have no cut
vertex before anything is claimed.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
           'NUMEXPR_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import functools
import numpy as np
import sympy as sp
from scipy.sparse import csr_matrix
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode

x = sp.Symbol('x')
BUDGET = quickmode.budget(1500.0, 25.0)  # wall-clock seconds; Rule on long searches
CKPT = quickmode.ckpt('private/twocut_ckpt.txt')
# ------------------------------------------------------------------ matching polynomial
def mu_of(adj, S):
    """mu of the induced subgraph on S, by memoised vertex deletion."""
    @functools.lru_cache(maxsize=None)
    def rec(vs):
        T = set(vs)
        if not T:
            return sp.Integer(1)
        w = min(T, key=lambda t: len(adj[t] & T))
        T1 = T - {w}
        tot = x * rec(tuple(sorted(T1)))
        for z in adj[w] & T:
            tot -= rec(tuple(sorted(T1 - {z})))
        return sp.expand(tot)
    return rec(tuple(sorted(S)))


def branch_data(nb, bedges, Su, Sv):
    """A, Bu, Bv, D for one branch with hub-attachment sets Su (to u) and Sv (to v)."""
    adj = {i: set() for i in range(nb)}
    for a, b in bedges:
        adj[a].add(b); adj[b].add(a)
    V = set(range(nb))
    A = mu_of(adj, V)
    Bu = sum((mu_of(adj, V - {w}) for w in Su), sp.Integer(0))
    Bv = sum((mu_of(adj, V - {w}) for w in Sv), sp.Integer(0))
    D = sp.Integer(0)
    for w in Su:
        for w2 in Sv:
            if w != w2:
                D += mu_of(adj, V - {w, w2})
    return sp.expand(A), sp.expand(Bu), sp.expand(Bv), sp.expand(D)


def bracket(A, Bu, Bv, D, p):
    return sp.expand(x**2 * A**2 - p * x * (Bu + Bv) * A + p * D * A
                     + p * (p - 1) * Bu * Bv)


def assemble(nb, bedges, Su, Sv, p):
    """the whole graph: hubs 0,1 and p copies of the branch."""
    edges = []
    n = 2
    for _ in range(p):
        off = n
        for a, b in bedges:
            edges.append((a + off, b + off))
        for w in Su:
            edges.append((0, w + off))
        for w in Sv:
            edges.append((1, w + off))
        n += nb
    return n, edges


def cut_vertices(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    out = []
    for w in range(n):
        rest = [t for t in range(n) if t != w]
        seen, st = {rest[0]}, [rest[0]]
        while st:
            t = st.pop()
            for z in adj[t]:
                if z != w and z not in seen:
                    seen.add(z); st.append(z)
        if len(seen) != len(rest):
            out.append(w)
    return out


# ------------------------------------------------------------------ spec(T) by AFH
def setup(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    rows, cols = [], []
    for k, (a, b) in enumerate(de):
        for c in adj[b]:
            if c != a:
                rows.append(k); cols.append(idx[(b, c)])
    M = len(de)
    B = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(M, M))
    return B, M


def rho_at(lam, B, M, iters=6000, tol=1e-13):
    h = np.full(M, 0.5)
    for _ in range(iters):
        s = lam - B @ h
        if np.min(np.abs(s)) < 1e-12:
            return None
        new = 1.0 / s
        d = np.max(np.abs(new - h))
        h = new
        if d < tol:
            break
    else:
        return None
    h2 = h * h
    vec = np.abs(np.sin(np.arange(M) * 1.7)) + 0.1
    r2 = 0.0
    for _ in range(3000):
        w = h2 * (B @ (h2 * (B @ vec)))
        nr = np.max(np.abs(w))
        if nr == 0:
            return 0.0
        vec = w / nr
        r2 = nr
    return math.sqrt(r2)


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


# ------------------------------------------------------------------ branch families
def br_K2q(q):
    """K_{2,q}: s attached to u, t attached to v."""
    e = []
    for j in range(q):
        e.append((0, 2 + j)); e.append((2 + j, 1))
    return 2 + q, e, [0], [1]


def br_path(L):
    """path on L vertices, ends attached to the two hubs (generalized theta)."""
    return L, [(i, i + 1) for i in range(L - 1)], [0], [L - 1]


def br_K2q_both(q):
    """K_{2,q} with BOTH degree-q vertices attached to BOTH hubs."""
    e = []
    for j in range(q):
        e.append((0, 2 + j)); e.append((2 + j, 1))
    return 2 + q, e, [0, 1], [0, 1]


def br_K2q_tail(q, L):
    """K_{2,q} at the u end, a path of length L to the v end: unequal hub geometry."""
    e = []
    for j in range(q):
        e.append((0, 2 + j)); e.append((2 + j, 1))
    n = 2 + q
    prev = 1
    for _ in range(L):
        e.append((prev, n)); prev = n; n += 1
    return n, e, [0], [prev]


def br_tri_pair(q):
    """two K_{2,q} blocks in series, hubs at the far ends: a longer resonator."""
    e = []
    n = 2
    for j in range(q):
        e.append((0, n)); e.append((n, 1)); n += 1
    a = n; n += 1
    e.append((1, a))
    b = a + 1; n += 1
    for j in range(q):
        e.append((a, n)); e.append((n, b)); n += 1
    return n, e, [0], [b]


FAMILIES = []
for q in range(2, 8):
    FAMILIES.append((f"K2,{q}", br_K2q(q)))
for L in range(2, 8):
    FAMILIES.append((f"path{L}", br_path(L)))
for q in range(2, 7):
    FAMILIES.append((f"K2,{q}both", br_K2q_both(q)))
for q in range(2, 6):
    for L in (1, 2, 3):
        FAMILIES.append((f"K2,{q}+t{L}", br_K2q_tail(q, L)))
for q in range(2, 5):
    FAMILIES.append((f"2xK2,{q}", br_tri_pair(q)))


# ------------------------------------------------------------------ self-check
def selfcheck():
    """the 2-cut identity, against a brute-force matching polynomial."""
    ok = True
    for (name, (nb, be, Su, Sv)), p in (((FAMILIES[1]), 3), ((FAMILIES[8]), 4),
                                        ((FAMILIES[14]), 3)):
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        pred = sp.expand(A**(p - 2) * bracket(A, Bu, Bv, D, p))
        n, edges = assemble(nb, be, Su, Sv, p)
        adj = {i: set() for i in range(n)}
        for a, b in edges:
            adj[a].add(b); adj[b].add(a)
        true = mu_of(adj, set(range(n)))
        good = sp.expand(pred - true) == 0
        ok = ok and good
        print(f"  identity {name:>10} p={p} n={n:>3}: "
              f"{'OK' if good else 'MISMATCH'}", flush=True)
    return ok


def main():
    print("2-cut attack on C1: two hubs, p identical branches attached to both.\n")
    print("self-check of the 2-cut identity:", flush=True)
    if not selfcheck():
        print("IDENTITY WRONG - nothing below is meaningful.")
        return 1
    print()
    print(f"{'branch':>12}{'p':>3}{'n':>5}{'cuts':>6}{'root':>11}"
          f"{'defect':>11}{'width':>9}{'verdict':>9}", flush=True)
    t0 = time.time()
    hits, tested = [], 0
    for name, (nb, be, Su, Sv) in FAMILIES:
        if time.time() - t0 > BUDGET:
            print("  [budget reached]"); break
        A, Bu, Bv, D = branch_data(nb, be, Su, Sv)
        for p in range(2, 11):
            n = 2 + p * nb
            if n > 64 or time.time() - t0 > BUDGET:
                continue
            F = bracket(A, Bu, Bv, D, p)
            co = sp.Poly(F, x).all_coeffs()
            while co and co[-1] == 0:
                co.pop()
            if len(co) < 2:
                continue
            try:
                roots = [float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=20, maxsteps=3000)
                         if abs(sp.im(r)) < 1e-10 and sp.re(r) > 1e-9]
            except Exception:
                continue
            edges = assemble(nb, be, Su, Sv, p)[1]
            cuts = cut_vertices(n, edges)
            B, M = setup(n, edges)
            tested += 1
            found = False
            for th in roots:
                r = rho_at(th, B, M)
                if r is None or r >= 1:
                    continue
                lo = edge_toward(th, B, M, -1)
                hi = edge_toward(th, B, M, +1)
                if lo is None or hi is None:
                    continue
                hits.append((name, p, n, len(cuts), th, min(th - lo, hi - th), hi - lo))
                print(f"{name:>12}{p:>3}{n:>5}{len(cuts):>6}{th:>11.6f}"
                      f"{min(th-lo, hi-th):>11.6f}{hi-lo:>9.5f}{'GAP':>9}", flush=True)
                found = True
            if not found:
                print(f"{name:>12}{p:>3}{n:>5}{len(cuts):>6}{'-':>11}"
                      f"{'-':>11}{'-':>9}{'in spec':>9}", flush=True)
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"{name} p={p} tested={tested} hits={len(hits)}\n")
            os.replace(CKPT + '.tmp', CKPT)
    print(f"\n{tested} configurations, {time.time()-t0:.0f}s")
    live = [h for h in hits if h[3] == 0]
    if live:
        print(f"\nC1 IS REFUTED: {len(live)} counterexamples with NO cut vertex.")
        for h in sorted(live, key=lambda t: t[2])[:8]:
            print(f"  {h[0]} p={h[1]} n={h[2]} root={h[4]:.6f} "
                  f"defect={h[5]:.6f} width={h[6]:.5f}")
    elif hits:
        print(f"\n{len(hits)} gap roots, but all in graphs that still have a cut vertex; "
              "C1 not refuted.")
    else:
        print("\nno gap root anywhere in the 2-cut family. C1 survives the attack "
              "most likely to break it.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
