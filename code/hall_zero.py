"""Theorem: 0 is an eigenvalue of the universal cover T_G iff G has an independent set S
with |N(S)| < |S|, i.e. iff G fails Hall's condition.

By the criterion of Banks, Garza-Vargas and Mukherjee, 0 is an eigenvalue of T_G iff G has a
0-Aomoto subset. This script checks the equivalence of that condition with a Hall violation
exhaustively on all connected graphs up to six vertices. The constructive half is checked in
the companion run described in the paper; the counting core is machine-checked in
RamaLean/HallZero.lean.

Is a 0-Aomoto subset equivalent to a Hall violator?

P81 (frozen before the data):
  For every graph G,  (there is a 0-Aomoto subset)  <=>  (there is an independent set S
  with |N(S)| < |S|).
  (<=) is immediate: an independent set has all components K_1, eigenvalue 0, cc = |S|.
  (=>) is the claim under test.
FALSIFICATION: one graph with a 0-Aomoto subset and no Hall violator.
"""
import itertools, sys
from fractions import Fraction

def comps(n, adj, S):
    seen, out = set(), []
    for v in S:
        if v in seen: continue
        st, c = [v], []
        seen.add(v)
        while st:
            u = st.pop(); c.append(u)
            for w in adj[u]:
                if w in S and w not in seen:
                    seen.add(w); st.append(w)
        out.append(c)
    return out

def is_forest(adj, comp):
    cs = set(comp)
    e = sum(1 for u in comp for w in adj[u] if w in cs) // 2
    return e == len(comp) - 1

def has_pm(adj, comp):
    """perfect matching in a tree/forest component, by greedy leaf-stripping (exact for forests)"""
    cs = set(comp)
    deg = {u: sum(1 for w in adj[u] if w in cs) for u in cs}
    while cs:
        leaves = [u for u in cs if deg[u] <= 1]
        if not leaves: return False
        u = leaves[0]
        nb = [w for w in adj[u] if w in cs]
        if not nb: return False          # isolated vertex, cannot be matched
        m = nb[0]
        for x in (u, m):
            cs.discard(x)
            for w in adj[x]:
                if w in cs: deg[w] -= 1
    return True

def aomoto0(n, adj):
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            Ss = set(S)
            cc = comps(n, adj, Ss)
            if not all(is_forest(adj, c) for c in cc): continue
            if any(has_pm(adj, c) for c in cc): continue      # need 0 as eigenvalue: NO perfect matching
            b = len({w for u in S for w in adj[u] if w not in Ss})
            if b < len(cc): return S
    return None

def hall_violator(n, adj):
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            Ss = set(S)
            if any(w in Ss for u in S for w in adj[u]): continue   # independent
            N = {w for u in S for w in adj[u]}
            if len(N) < len(S): return S
    return None

def connected(n, adj):
    seen = {0}; st = [0]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == n

def run(n):
    pairs = list(itertools.combinations(range(n), 2))
    tot = bad = both = neither = 0
    for mask in range(1 << len(pairs)):
        adj = {i: set() for i in range(n)}
        for i, (a, b) in enumerate(pairs):
            if mask >> i & 1: adj[a].add(b); adj[b].add(a)
        if not connected(n, adj): continue
        tot += 1
        A = aomoto0(n, adj); H = hall_violator(n, adj)
        if (A is None) != (H is None):
            bad += 1
            print(f"  MISMATCH n={n} edges={[p for i,p in enumerate(pairs) if mask>>i&1]} "
                  f"aomoto={A} hall={H}")
            if bad > 5: return tot, bad
        elif A is not None: both += 1
        else: neither += 1
    return tot, bad, both, neither

for n in (3, 4, 5, 6):
    r = run(n)
    print(f"n={n}: connected graphs={r[0]}  mismatches={r[1]}  both={r[2]}  neither={r[3]}", flush=True)
