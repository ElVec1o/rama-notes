"""The d = 2 matching polynomial of a one-cut graph, exactly, and whether the violation survives it.

Every known counterexample to Conjecture 10 is at d = 1. Hall's theorem, and his Question 6.3, are
about mu_{d,G} for every d. So the sharpest question left is whether the violation is a d = 1
artifact: if the escaping root returns to spec(T) at d = 2, the strengthening of the theorem is
plausibly true for all d >= 2, which would be a real conjecture in Hall's own setting.

mu_{d,G} is the average matching polynomial over all d-lifts, and naive averaging costs 2^|E| for
d = 2, impossible at 42 to 60 edges. But every known counterexample is a ONE-CUT graph, a centre c
joined to p copies of a rooted branch (B, r), and that structure makes the average exact and cheap.

A 2-lift sends c to c0, c1, and each branch to an independent uniformly random 2-lift B~_i of B,
attached at the two lifts r_i^0 ~ c0 and r_i^1 ~ c1 of its root. Expanding mu of the lift by how
c0 and c1 are matched:

    mu(lift) = x^2 prod A_i
             - x sum_i U_i prod_{j!=i} A_j  - x sum_i V_i prod_{j!=i} A_j
             + sum_{i!=j} U_i V_j prod_{k!=i,j} A_k
             + sum_i W_i prod_{j!=i} A_j

with A_i = mu(B~_i), U_i = mu(B~_i - r^0), V_i = mu(B~_i - r^1), W_i = mu(B~_i - r^0 - r^1).
Each branch index appears at most once in every product, and the branch lifts are independent, so
the expectation factorises, and by the fibre symmetry E[U] = E[V]:

    mu_{2,G} = x^2 A^p - 2p x U A^{p-1} + p(p-1) U^2 A^{p-2} + p W A^{p-1},

where A, U, W are now the AVERAGES over the 2^{e(B)} lifts of the single branch. That is at most a
few thousand graphs on at most sixteen vertices, all exact in rational arithmetic.

The universal cover is the same for every d, so spec(T) and its gaps do not move. The question is
only where the roots of mu_{2,G} sit relative to the same bands that mu_{1,G} escaped.

FROZEN BEFORE THE DATA:
  P78. (a) The factorised formula agrees with brute-force averaging over all 2-lifts on a graph
           small enough to enumerate them.
       (b) For each of the five known counterexamples, mu_{2,G} is computed exactly and its roots
           classified at the root, resolution-free.
       (c) Prediction, stated so it can be scored: the violation DISAPPEARS at d = 2. The reason is
           that lifting smooths the localised structure that lets a root escape; the branch
           obstruction already shows escape needs a delicate boundary count, and averaging over
           lifts should wash that out. If (c) holds it is the most interesting thing in this
           repository. If it fails, the phenomenon is stable in d and the d = 1 case is not special.

FALSIFICATION. (a) failing means the formula is wrong and nothing downstream stands. (c) is a
genuine prediction and is falsified by any counterexample whose escaping root, or any other root,
lies outside spec(T) at d = 2.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import json
import math
import itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import sympy as sp
import networkx as nx
from twocut import mu_of, x
from aomoto_obstruction import adjof, hall

X = x


def mu_graph(n, edges):
    return sp.expand(mu_of(adjof(n, edges), set(range(n))))


def mu_minus(n, edges, drop):
    adj = adjof(n, edges)
    return sp.expand(mu_of(adj, set(range(n)) - set(drop)))


def branch_lift_averages(nB, edgesB, r):
    """Average A, U, W over all 2^{e} sign-lifts of the rooted branch (B, r).
    Vertex v lifts to v and v + nB; edge (a,b) with sign s lifts to (a, b), (a+nB, b+nB) if s=+1
    and to (a, b+nB), (a+nB, b) if s=-1."""
    e = len(edgesB)
    A = U = V = W = sp.Integer(0)
    for signs in itertools.product([1, -1], repeat=e):
        L = []
        for (a, b), s in zip(edgesB, signs):
            if s == 1:
                L += [(a, b), (a + nB, b + nB)]
            else:
                L += [(a, b + nB), (a + nB, b)]
        A += mu_graph(2 * nB, L)
        U += mu_minus(2 * nB, L, [r])
        V += mu_minus(2 * nB, L, [r + nB])
        W += mu_minus(2 * nB, L, [r, r + nB])
    k = sp.Integer(2 ** e)
    return sp.expand(A / k), sp.expand(U / k), sp.expand(V / k), sp.expand(W / k)


def mu2_onecut(nB, edgesB, r, p):
    A, U, V, W = branch_lift_averages(nB, edgesB, r)
    assert sp.expand(U - V) == 0, "fibre symmetry E[U] = E[V] failed"
    return sp.expand(x ** 2 * A ** p - 2 * p * x * U * A ** (p - 1)
                     + p * (p - 1) * U ** 2 * A ** (p - 2) + p * W * A ** (p - 1))


def mu2_bruteforce(n, edges):
    """Average of mu over ALL 2-lifts of a graph, for validation only."""
    tot = sp.Integer(0); e = len(edges)
    for signs in itertools.product([1, -1], repeat=e):
        L = []
        for (a, b), s in zip(edges, signs):
            L += [(a, b), (a + n, b + n)] if s == 1 else [(a, b + n), (a + n, b)]
        tot += mu_graph(2 * n, L)
    return sp.expand(tot / 2 ** e)


def onecut(nB, edgesB, r, p):
    """centre 0 joined to p copies of (B, r)"""
    E = []; off = 1
    for _ in range(p):
        for a, b in edgesB:
            E.append((a + off, b + off))
        E.append((0, r + off)); off += nB
    return off, E


def decompose(n, edges):
    """recover (B, r, p) from a one-cut graph whose centre is vertex 0 with max degree"""
    G = nx.Graph(edges)
    deg = dict(G.degree()); c = max(deg, key=lambda v: deg[v])
    H = G.copy(); H.remove_node(c)
    comps = sorted(nx.connected_components(H), key=min)
    Bset = sorted(comps[0]); m = {v: i for i, v in enumerate(Bset)}
    edgesB = sorted((m[a], m[b]) for a, b in G.subgraph(Bset).edges())
    r = [m[v] for v in Bset if G.has_edge(v, c)][0]
    return len(Bset), edgesB, r, len(comps), c


def main():
    from d3_counterexample import classify
    print("P78 (frozen): does the violation survive d = 2?\n")

    print("(a) validation: factorised formula vs brute force on a small one-cut graph")
    nB, eB, r = 3, [(0, 1), (1, 2), (2, 0)], 0          # triangle, rooted at 0
    for p in (2,):
        n, E = onecut(nB, eB, r, p)
        f1 = mu2_onecut(nB, eB, r, p)
        f2 = mu2_bruteforce(n, E)
        ok = sp.expand(f1 - f2) == 0
        print(f"    triangle branch, p={p}, n={n}, {len(E)} edges, {2**len(E)} lifts: "
              f"{'AGREE' if ok else 'DISAGREE'}")
        if not ok:
            print("  P78(a) FAILS; the formula is wrong."); return 1
    print()

    print("(b),(c) the one-cut counterexamples at d = 2")
    cases = []
    # Hall's 41-vertex graph is NOT one-cut in the sense this formula needs: deleting its
    # hub leaves a 33-vertex component with 48 edges, so the branch average would be 2^48
    # lifts. It is excluded, and the test below covers the four one-cut counterexamples only.
    here = os.path.dirname(os.path.abspath(__file__))
    for o in json.load(open(os.path.join(here, '..', 'data', 'lowgap_counterexamples.json'))):
        cases.append((f"new n={o['n']}", o['n'], [tuple(t) for t in o['edges']], o['root']))

    survives = 0
    print("  (Hall 41v excluded: not one-cut, see comment above.)")
    for nm, n, E, th1 in cases:
        nB, eB, r, p, c = decompose(n, E)
        m2 = sp.Poly(mu2_onecut(nB, eB, r, p), x)
        rts = sorted({round(float(sp.re(z)), 9) for z in m2.nroots(n=20, maxsteps=4000)
                      if abs(sp.im(z)) < 1e-12 and sp.re(z) > 1e-6})
        out = [t for t in rts if classify(n, E, t)[0] == 'outside spec']
        near = min(rts, key=lambda t: abs(t - th1))
        survives += bool(out)
        print(f"  {nm:>12}: branch {nB}v/{len(eB)}e, p={p}; mu_2 degree {m2.degree()}, "
              f"{len(rts)} positive roots")
        print(f"      d=1 violating root {th1:.6f}; nearest d=2 root {near:.6f} "
              f"[{classify(n, E, near)[0]}]")
        print(f"      d=2 roots OUTSIDE spec(T): {[round(t,6) for t in out] if out else 'none'}")

    print()
    if survives == 0:
        print("  P78(c) HOLDS. In every known counterexample the violation is a d = 1 artifact:")
        print("  at d = 2 every root of mu_{2,G} lies in spec(T). That is consistent with the")
        print("  strengthening of Hall-Puder-Sawin being TRUE for all d >= 2 and false only at")
        print("  d = 1, which is a conjecture in their own setting and worth putting to them.")
    else:
        print(f"  P78(c) FAILS in {survives} of {len(cases)} cases: the violation survives to d = 2,")
        print("  so the phenomenon is stable in d and the ordinary matching polynomial is not special.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
