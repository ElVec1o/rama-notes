"""Out-of-sample test of the frozen bounded-degree pattern (Rule I3).

FROZEN STATEMENT P1, written before this data was generated:
    for every finite connected simple graph G with Delta(G) <= 5,
    Zeros(mu_G) is contained in spec(T_G).

The in-sample evidence is that every counterexample so far has Delta(G) >= 6. That evidence
cannot confirm P1, because in both families the number of branches IS the degree of the
central vertex: many branches forced high degree, so the two were never separable.

THE OUT-OF-SAMPLE CONSTRUCTION decouples them. Replace the star centre by a rooted tree
skeleton of fixed arity, and hang one branch on each skeleton leaf. Internal skeleton vertices
have degree arity+1, independent of how many branches there are, so a binary skeleton carries
2^d branches at maximum degree three. With a branch K_{2,q} plus a pendant leaf at w, the
degrees are

    skeleton internal: arity+1,   v: q+1,   w: q+1,   u: 2,   leaf: 1,

so Delta = max(arity+1, q+1), and arity 2 with q <= 4 gives Delta <= 5.

PRE-REGISTERED PREDICTION (Rule I15), recorded before running: P1 will be refuted. The
mechanism plausibly depends on the number of resonating branches rather than on degree, and
the skeleton supplies branches without degree.

mu_G comes from the standard rooted pair recursion. For a piece rooted at r with subpieces
P_1..P_k attached by edges from r,

    mu_whole      = x prod A_i  -  sum_i B_i prod_{j != i} A_j
    mu_whole - r  = prod A_i,        (A_i, B_i) = (mu_{P_i}, mu_{P_i - root}),

with the branch supplying its own (A, B) by brute force. The same recursion builds the
explicit graph, so the polynomial and the cavity computation cannot drift apart.
"""

import sys
import os
import math
import time
import sympy as sp

sys.path.insert(0, 'code')
g = {}
exec(open('code/mindeg2.py').read().split("def main():")[0], g)
mu_brute, dos_ladder = g['mu_brute'], g['dos_ladder']
x = sp.Symbol('x')


def branch_pieces(q):
    """K_{2,q} with a pendant leaf at w, rooted at v. Returns (A, B, nverts, edges)."""
    e = [(0, 2 + j) for j in range(q)] + [(2 + j, 1) for j in range(q)] + [(1, q + 2)]
    nv = q + 3
    A = sp.expand(mu_brute(nv, e))
    B = sp.expand(mu_brute(nv - 1, [(a - 1, b - 1) for a, b in e if 0 not in (a, b)]))
    return A, B, nv, e


def build(q, arity, depth):
    """Skeleton tree of given arity and depth; each leaf carries a branch.
    Returns (A, B, n, edges, root) with A = mu_G."""
    Ab, Bb, nvb, eb = branch_pieces(q)
    edges = []
    counter = [0]

    def new():
        counter[0] += 1
        return counter[0] - 1

    def place_branch():
        off = counter[0]
        counter[0] += nvb
        for (a, b) in eb:
            edges.append((a + off, b + off))
        return Ab, Bb, off          # branch root is local 0, i.e. global off

    def rec(d):
        if d == 0:
            return place_branch()
        r = new()
        subs = [rec(d - 1) for _ in range(arity)]
        for (_, _, rt) in subs:
            edges.append((r, rt))
        As = [s[0] for s in subs]
        Bs = [s[1] for s in subs]
        prodA = sp.prod(As)
        A = sp.expand(x * prodA - sum(Bs[i] * sp.prod(As[:i] + As[i + 1:])
                                      for i in range(len(subs))))
        return A, sp.expand(prodA), r

    A, B, root = rec(depth)
    return A, B, counter[0], edges, root


def maxdeg(n, edges):
    d = [0] * n
    for a, b in edges:
        d[a] += 1; d[b] += 1
    return max(d), min(d)


def main():
    print("FROZEN P1: Delta(G) <= 5  implies  Zeros(mu_G) inside spec(T_G)")
    print("PREDICTION, pre-registered: P1 will be refuted.\n", flush=True)
    print(f"{'arity':>6}{'d':>3}{'q':>3}{'branches':>10}{'n':>5}{'Dmax':>6}"
          f"{'root':>10}{'DOS/eta':>24}{'verdict':>10}", flush=True)
    hits = []
    t0 = time.time()
    for arity in (2, 3):
        for q in (2, 3, 4):
            for depth in (2, 3, 4):
                nb = arity ** depth
                A, B, n, edges, root = build(q, arity, depth)
                if n > 140:
                    continue
                Dmax, Dmin = maxdeg(n, edges)
                co = sp.Poly(sp.expand(A), x).all_coeffs()
                while co and co[-1] == 0:
                    co.pop()
                if len(co) < 2:
                    continue
                rts = [sp.re(r) for r in sp.Poly(co, x).nroots(n=25, maxsteps=800)
                       if abs(sp.im(r)) < 1e-12 and sp.re(r) > 1e-9]
                found = False
                for r in rts:
                    lad = dos_ladder(n, edges, float(r), etas=(1e-5, 1e-7, 1e-9))
                    if max(lad) < 50.0:
                        hits.append((Dmax, n, arity, depth, q, float(r)))
                        print(f"{arity:>6}{depth:>3}{q:>3}{nb:>10}{n:>5}{Dmax:>6}"
                              f"{float(r):>10.5f}{str([f'{t:.2f}' for t in lad]):>24}"
                              f"{'GAP':>10}", flush=True)
                        found = True
                if not found:
                    print(f"{arity:>6}{depth:>3}{q:>3}{nb:>10}{n:>5}{Dmax:>6}"
                          f"{'-':>10}{'-':>24}{'in spec':>10}", flush=True)
    print(f"\n{time.time()-t0:.0f}s")
    if hits:
        lo = min(hits)
        print(f"\nP1 IS REFUTED. smallest maximum degree with a root in a gap: {lo[0]}")
        print(f"  n={lo[1]}, arity={lo[2]}, depth={lo[3]}, q={lo[4]}, root={lo[5]:.6f}")
    else:
        print("\nno counterexample with Delta <= 5 in this family; P1 survives "
              "this out-of-sample test")
    return 0


if __name__ == '__main__':
    sys.exit(main())
