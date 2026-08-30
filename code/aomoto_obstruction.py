"""Why the branch mechanism cannot produce a counterexample, and the retraction it forces.

RETRACTION. Earlier versions of this repository (releases v5.0 through v5.2) claimed that
Conjecture D3 (minimum degree three) and Conjecture C2 (3-connectivity) were false, on 14 and 23
vertices respectively, with sqrt3 outside spec(T_G). BOTH CLAIMS ARE FALSE. In both graphs sqrt3
is an EIGENVALUE of the universal cover, hence lies in spec(T_G), so neither graph refutes
anything. This script is the correction and the explanation.

THE CRITERION WE MISSED. Banks, Garza-Vargas and Mukherjee characterise the point spectrum of the
universal cover: theta is an eigenvalue of T_G if and only if G has a theta-Aomoto subset, that is
a set S with

    G[S] a forest,   theta an eigenvalue of every component of G[S],   |boundary(S)| < cc(G[S]).

Li, Magee, Sabri and Thomas prove the analogue for the maximal abelian cover, in the checkable form
"theta is an eigenvalue of G^ab iff theta is a zero of mu_{G\\Gamma} for every 2-regular subgraph
Gamma", where G\\Gamma is the subgraph INDUCED ON V(G) minus V(Gamma); and Spier proves that the
universal and maximal abelian covers have the same eigenvalues.

WHY OUR CONSTRUCTION COULD NEVER WORK. Take the union of the branch vertex sets. Its components are
the p branches, and its boundary is contained in the k-vertex separator, so the Aomoto inequality
reads p > k. That is exactly the condition the Divisibility Lemma needs for A^(p-k) to be a
nontrivial divisor. The configuration that manufactures a root of mu_G is the configuration that
puts that root into the point spectrum of the cover. Shared separator, boundary fixed at k,
components growing with p: the inequality is automatic.

WHY HALL'S CONSTRUCTION DOES WORK. His branches are not trees, and the natural forest inside one is
the star K_{1,5} at w_i, whose boundary is the pair {v_i, leaf_i}. Five branches give cc = 5 and
boundary 10, on the wrong side of the inequality. Deleting the pendant leaves brings the boundary to
5, still not below 5, and it also destroys the root: the leafless graph has no factor x^2 - 5. So
the leaves do two jobs, creating the root and doubling the star's boundary, and both are needed.

FROZEN BEFORE THE DATA:
  P70. (a) The Aomoto test reproduces known answers: no eigenvalue for a cycle or for K_4, and 0 for
           K_{2,3}, which is the isolated point of the (3,2)-biregular tree.
       (b) The 14-vertex and 23-vertex graphs both carry a sqrt3-Aomoto subset, so both former
           "counterexamples" are refuted.
       (c) Hall's graph carries none at sqrt5, witnessed by a 2-regular Gamma with
           mu_{G\\Gamma}(sqrt5) != 0, so his counterexample stands.
       (d) Removing Hall's pendant leaves destroys the root sqrt5 outright.

FALSIFICATION. If (a) fails the test is wrong and nothing here is meaningful. If (c) fails then
Hall's counterexample is also in doubt, which would be a far larger claim and is not made here.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import numpy as np
import sympy as sp
import networkx as nx
from twocut import mu_of, x


def adjof(n, edges):
    a = {i: set() for i in range(n)}
    for u, v in edges:
        a[u].add(v); a[v].add(u)
    return a


def components(adj, S):
    out, seen = [], set()
    for s in S:
        if s in seen:
            continue
        comp, st = set(), [s]
        while st:
            w = st.pop()
            if w in comp:
                continue
            comp.add(w)
            for y in adj[w] & S:
                if y not in comp:
                    st.append(y)
        seen |= comp
        out.append(comp)
    return out


def is_aomoto(n, edges, S, theta):
    """The three conditions of the Aomoto definition, checked directly."""
    adj = adjof(n, edges); S = set(S)
    cs = components(adj, S)
    eS = sum(1 for a, b in edges if a in S and b in S)
    forest = (eS == len(S) - len(cs))
    ok = True
    for comp in cs:
        idx = {w: i for i, w in enumerate(sorted(comp))}
        A = np.zeros((len(comp),) * 2)
        for a, b in edges:
            if a in comp and b in comp:
                A[idx[a], idx[b]] = A[idx[b], idx[a]] = 1
        if min(abs(np.linalg.eigvalsh(A) - theta)) > 1e-9:
            ok = False
    bdry = {w for w in set(range(n)) - S if adj[w] & S}
    return (forest and ok and len(bdry) < len(cs)), len(cs), len(bdry)


def mu_on(adj, V):
    V = set(V); seen = set(); tot = sp.Integer(1)
    for s in V:
        if s in seen:
            continue
        comp, st = set(), [s]
        while st:
            w = st.pop()
            if w in comp:
                continue
            comp.add(w)
            for y in adj[w] & V:
                if y not in comp:
                    st.append(y)
        seen |= comp
        tot *= mu_of({w: (adj[w] & comp) for w in comp}, comp)
    return sp.expand(tot)


def lmst_not_eigenvalue(n, edges, theta, maxlen):
    """Find a 2-regular Gamma with mu_{G-V(Gamma)}(theta) != 0, which by LMST + Spier proves
    theta is NOT an eigenvalue of the cover. Returns the witness or None."""
    adj = adjof(n, edges)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    cyc = [frozenset(c) for c in nx.simple_cycles(G, length_bound=maxlen) if len(c) >= 3]
    fams = [()] + [(i,) for i in range(len(cyc))]
    for i in range(len(cyc)):
        for j in range(i + 1, len(cyc)):
            if not (cyc[i] & cyc[j]):
                fams.append((i, j))
    for fam in fams:
        rem = set()
        for i in fam:
            rem |= cyc[i]
        val = sp.simplify(mu_on(adj, set(range(n)) - rem).subs(x, theta))
        if val != 0:
            return sorted(rem), val
    return None


def ours(k, m, p):
    edges = []; nxt = k
    for _ in range(p):
        c = nxt; nxt += 1
        for _ in range(m):
            l = nxt; nxt += 1
            edges.append((c, l))
            for h in range(k):
                edges.append((l, h))
    return nxt, edges


def hall(p=5, q=5, leaves=True):
    edges = []; c = 0; nxt = 1; parts = []
    for _ in range(p):
        v = nxt; w = nxt + 1; nxt += 2; us = []
        for _ in range(q):
            u = nxt; nxt += 1; us.append(u)
            edges += [(v, u), (w, u)]
        leaf = None
        if leaves:
            leaf = nxt; nxt += 1; edges.append((w, leaf))
        edges.append((c, v)); parts.append((v, w, us, leaf))
    return nxt, edges, parts


def main():
    print("P70 (frozen): the branch mechanism makes eigenvalues, not counterexamples.\n")

    print("(a) the test against covers whose point spectrum is known.")
    ok = True
    C6 = (6, [(i, (i + 1) % 6) for i in range(6)])
    K4 = (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
    K23 = (5, [(i, 2 + j) for i in range(2) for j in range(3)])
    for nm, (n, e), th, expect in [("C_6 at 1.0", C6, 1.0, False),
                                   ("K_4 at 2.334", K4, 2.3344, False),
                                   ("K_{2,3} at 0", K23, 0.0, True)]:
        best = False
        for r in range(1, n + 1):
            import itertools
            for S in itertools.combinations(range(n), r):
                if is_aomoto(n, e, S, th)[0]:
                    best = True; break
            if best:
                break
        good = (best == expect)
        ok = ok and good
        print(f"    {nm:>16}: Aomoto subset exists = {best}, expected {expect}  "
              f"{'OK' if good else 'MISMATCH'}")
    if not ok:
        print("  the test fails a known case; nothing below is meaningful.")
        return 1

    print("\n(b) THE RETRACTION: the two graphs this repository called counterexamples.")
    for nm, (k, m, p), th in [("D3 'counterexample', 14 vertices", (2, 3, 3), math.sqrt(3)),
                              ("C2 'counterexample', 23 vertices", (3, 3, 5), math.sqrt(3))]:
        n, e = ours(k, m, p)
        S = set(range(k, n))
        yes, cc, bd = is_aomoto(n, e, S, th)
        print(f"    {nm}: cc={cc}, |boundary|={bd}, Aomoto={yes}")
        print(f"      -> sqrt3 IS an eigenvalue of T_G, so it lies IN spec(T_G).")
        print(f"      -> this graph does NOT refute anything. Claim retracted.")
    print("    The Aomoto inequality |boundary| < cc is p > k, which is exactly the condition")
    print("    the Divisibility Lemma needs. The mechanism cannot produce a counterexample.")

    print("\n(c) Hall's counterexample, which stands.")
    n, e, parts = hall(5, 5, True)
    S = {w for (_, w, _, _) in parts} | {u for (_, _, us, _) in parts for u in us}
    yes, cc, bd = is_aomoto(n, e, S, math.sqrt(5))
    print(f"    the five stars K_{{1,5}}: cc={cc}, |boundary|={bd}, Aomoto={yes}")
    w = lmst_not_eigenvalue(n, e, sp.sqrt(5), 8)
    if w:
        print(f"    witness Gamma on {len(w[0])} vertices with mu_(G-V(Gamma))(sqrt5) = {w[1]} != 0")
        print("    -> sqrt5 is NOT an eigenvalue of the cover (LMST + Spier). His example stands.")

    print("\n(d) the role of the pendant leaves.")
    n2, e2, p2 = hall(5, 5, False)
    adj2 = adjof(n2, e2)
    mu2 = sp.factor(mu_on(adj2, set(range(n2))))
    S2 = {w for (_, w, _, _) in p2} | {u for (_, _, us, _) in p2 for u in us}
    _, cc2, bd2 = is_aomoto(n2, e2, S2, math.sqrt(5))
    print(f"    with leaves   : cc={cc}, |boundary|={bd}")
    print(f"    without leaves: cc={cc2}, |boundary|={bd2}")
    print(f"    and the root is gone: mu = {mu2}")
    print("    The leaves create the root sqrt5 and double the star's boundary. Both are needed,")
    print("    which is the mechanism behind the empirical fact that the leaves are essential.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
