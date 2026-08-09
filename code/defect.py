"""The out-of-sample test of the frozen defect conjecture.

FROZEN BEFORE THIS DATA (research log, invention gate):
  D1. There is an absolute C with dist(theta, spec(T_G)) <= C for every finite graph G and
      every root theta of mu_G.
  D2. The same with C / |V(G)|.

Motivation: the three certified counterexamples all barely poke into their gaps, with defects
near 0.011, 0.0017 and 0.005. If the defect stays bounded, a quantitative theorem replaces the
false conjecture; if it grows, D1 dies and D2 with it.

LOCATING THE GAP EDGE SHARPLY. A density-of-states scan resolves an edge only as well as its
step size. Angel-Friedman-Hoory give an exact characterization instead: lambda lies outside
spec(A_T) exactly when a finite nonzero ratio system has decay rate below one, and their
Theorem 1.6 says a system with rate exactly one forces non-invertibility. So rho(lambda) = 1
IS the gap edge, and bisecting rho - 1 locates it to whatever precision the cavity solve
supports.

rho is computed period-safely from J squared: the follower digraph of these graphs has only
even cycles, so naive power iteration oscillates between two values and reports neither.

Reported per counterexample: the root, both gap edges, the defect, and the two scaled forms
defect * n and defect / (gap width). Rule 8: progress, ETA, checkpoint, backgrounded.
"""

import sys
import os
import math
import time
import random
import sympy as sp

CKPT = 'private/defect_ckpt.txt'
x = sp.Symbol('x')


# ---------------------------------------------------------------- constructions
def hall_family(p, q, gadget='leaf'):
    """p branches of K_{2,q} at a centre; gadget at each w."""
    e, n = [], 1
    for _ in range(p):
        off = n
        v, w = off, off + 1
        us = list(range(off + 2, off + 2 + q))
        cur = off + 2 + q
        for u in us:
            e.append((v, u)); e.append((u, w))
        if gadget == 'leaf':
            e.append((w, cur)); cur += 1
        else:
            k = int(gadget[1:])
            cyc = list(range(cur, cur + k - 1)); cur += k - 1
            prev = w
            for a in cyc:
                e.append((prev, a)); prev = a
            e.append((prev, w))
        e.append((0, v))
        n = cur
    return n, e


def tri_skeleton(depth):
    """binary tree of given depth, each leaf identified with a triangle vertex."""
    edges, c = [], [0]
    def place():
        off = c[0]; c[0] += 3
        for (a, b) in [(0, 1), (1, 2), (2, 0)]:
            edges.append((a + off, b + off))
        return off
    def rec(d):
        if d == 0:
            return place()
        r = c[0]; c[0] += 1
        for _ in range(2):
            rt = rec(d - 1); edges.append((r, rt))
        return r
    rec(depth)
    return c[0], edges


# ---------------------------------------------------------------- spectral side
def setup(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    foll = [[idx[(b, c)] for c in adj[b] if c != a] for (a, b) in de]
    return adj, de, foll


def rho_at(lam, foll, M, iters=20000, tol=1e-12):
    """decay rate of the real cavity fixed point at lam; None if it fails to settle."""
    h = [0.5] * M
    for _ in range(iters):
        new = [0.0] * M
        d = 0.0
        ok = True
        for k in range(M):
            s = lam
            for f in foll[k]:
                s -= h[f]
            if abs(s) < 1e-12:
                ok = False; break
            v = 1.0 / s
            d = max(d, abs(v - h[k])); new[k] = v
        if not ok:
            return None
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


def first_bad(theta, foll, M, direction, span=0.6, step=0.004):
    """Walk away from theta until rho >= 1 or the solve fails; return the bracket.
    Bisection alone is invalid here: beyond the spectral radius rho drops below one again,
    so both endpoints of a wide interval can look like gap points."""
    prev = theta
    t = theta
    while abs(t - theta) < span:
        t = t + direction * step
        r = rho_at(t, foll, M)
        if r is None or r >= 1:
            return prev, t
        prev = t
    return None


def edge_toward(theta, foll, M, direction, tol=1e-6):
    """The gap edge on one side of theta, by scan then bisect inside the bracket."""
    br = first_bad(theta, foll, M, direction)
    if br is None:
        return None
    good, bad = br
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


# ---------------------------------------------------------------- roots
def mu_brute(nv, elist):
    m = len(elist); cnt = {}
    for bits in range(1 << m):
        used, ok, k = set(), True, 0
        b, t = bits, 0
        while b:
            if b & 1:
                a, c = elist[t]
                if a in used or c in used:
                    ok = False; break
                used.add(a); used.add(c); k += 1
            b >>= 1; t += 1
        if ok:
            cnt[k] = cnt.get(k, 0) + 1
    return sum((-1) ** k * c * x ** (nv - 2 * k) for k, c in cnt.items())


def hall_roots(p, q, gadget):
    """roots of the last factor, via the branch recurrence."""
    if gadget == 'leaf':
        eb = [(0, 2 + j) for j in range(q)] + [(2 + j, 1) for j in range(q)] + [(1, q + 2)]
        nb = q + 3
    else:
        k = int(gadget[1:])
        eb = [(0, 2 + j) for j in range(q)] + [(2 + j, 1) for j in range(q)]
        nb = 2 + q
        cyc = list(range(nb, nb + k - 1)); nb += k - 1
        prev = 1
        for a in cyc:
            eb.append((prev, a)); prev = a
        eb.append((prev, 1))
    muH = sp.expand(mu_brute(nb, eb))
    muHv = sp.expand(mu_brute(nb - 1, [(a - 1, b - 1) for a, b in eb if 0 not in (a, b)]))
    last = sp.expand(x * muH - p * muHv)
    co = sp.Poly(last, x).all_coeffs()
    while co and co[-1] == 0:
        co.pop()
    return [float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=20, maxsteps=2000)
            if abs(sp.im(r)) < 1e-10 and sp.re(r) > 1e-9]


def tri_roots(depth):
    A0, B0 = x ** 3 - 3 * x, x ** 2 - 1
    A, B = A0, B0
    for _ in range(depth):
        A, B = sp.expand(x * A ** 2 - 2 * B * A), sp.expand(A ** 2)
    co = sp.Poly(A, x).all_coeffs()
    while co and co[-1] == 0:
        co.pop()
    return [float(sp.re(r)) for r in sp.Poly(co, x).nroots(n=20, maxsteps=3000)
            if abs(sp.im(r)) < 1e-10 and sp.re(r) > 1e-9]


def main():
    cases = []
    for (p, q) in [(7, 3), (6, 4), (5, 5), (6, 5), (6, 6), (7, 6), (7, 7)]:
        cases.append((f"leaf({p},{q})", hall_family(p, q, 'leaf'), hall_roots(p, q, 'leaf')))
    for (p, q, k) in [(7, 7, 5), (7, 8, 4), (8, 8, 3)]:
        cases.append((f"C{k}({p},{q})", hall_family(p, q, f'C{k}'),
                      hall_roots(p, q, f'C{k}')))
    for d in (3, 4):
        cases.append((f"tri(depth {d})", tri_skeleton(d), tri_roots(d)))

    print(f"{'case':>14}{'n':>5}{'root':>10}{'lo edge':>11}{'hi edge':>11}"
          f"{'defect':>10}{'width':>9}{'defect*n':>10}", flush=True)
    rows = []
    t0 = time.time()
    for i, (name, (n, edges), roots) in enumerate(cases):
        if n > 100:
            print(f"{name:>14}{n:>5}   skipped (too large)", flush=True); continue
        adj, de, foll = setup(n, edges)
        M = len(de)
        for th in roots:
            r = rho_at(th, foll, M)
            if r is None or r >= 1:
                continue                       # not in a gap
            lo = edge_toward(th, foll, M, -1)
            hi = edge_toward(th, foll, M, +1)
            if lo is None or hi is None:
                continue
            defect = min(th - lo, hi - th)
            width = hi - lo
            rows.append((name, n, th, defect, width))
            print(f"{name:>14}{n:>5}{th:>10.5f}{lo:>11.5f}{hi:>11.5f}"
                  f"{defect:>10.6f}{width:>9.5f}{defect*n:>10.4f}", flush=True)
        with open(CKPT + '.tmp', 'w') as f:
            f.write(f"{i+1}/{len(cases)} rows={len(rows)}\n")
        os.replace(CKPT + '.tmp', CKPT)

    if not rows:
        print("\nno gap points located"); return 0
    print(f"\n{time.time()-t0:.0f}s")
    d = [r[3] for r in rows]
    dn = [r[3] * r[1] for r in rows]
    dw = [r[3] / r[4] for r in rows]
    print(f"defects      : min {min(d):.6f}  max {max(d):.6f}")
    print(f"defect * n   : min {min(dn):.4f}  max {max(dn):.4f}")
    print(f"defect/width : min {min(dw):.4f}  max {max(dw):.4f}")
    print("\nD1 survives if the defect column is bounded; D2 if defect * n is.")
    print("A defect growing with n kills both.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
