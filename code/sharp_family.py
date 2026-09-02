"""Sharpness of the refined degree bound at (delta, kappa) = (3,2), (3,3) and (4,2).

Delta > (delta-2) kappa + 2. Each row below builds a graph attaining it, from c disjoint copies of
the theta-critical tree B together with b boundary vertices, every branch vertex taking enough
boundary neighbours to reach degree delta, the resulting edges shared out equally.

The counting chain fixes every parameter. With e = ((delta-2)|B| + 2)c cross edges,
e <= Delta b and b <= c-1 force c, then b, then n, so each graph below is the smallest possible.

The matching polynomial is computed exactly through the boundary as a separator: G minus the
boundary is a union of copies of B, so a matching is a partial matching on the boundary-incident
edges together with matchings inside the truncated copies. That reaches n = 23 with no 2^n anywhere.
"""

import sys
from itertools import combinations
import sympy as sp

sys.path.insert(0, '.')
from freetrees import _mul, _add

x = sp.Symbol('x')


def match_counts_sep(n, edges, B):
    """m_k of G, computing through the separator B. Components of G - B must be small."""
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    Bs = set(B)
    # components of G - B
    seen = set()
    comps = []
    for s in range(n):
        if s in Bs or s in seen:
            continue
        st, c = [s], []
        seen.add(s)
        while st:
            v = st.pop(); c.append(v)
            for u in adj[v]:
                if u not in Bs and u not in seen:
                    seen.add(u); st.append(u)
        comps.append(sorted(c))
    # matching counts of each component with an arbitrary subset of its vertices deleted
    tab = []
    for c in comps:
        idx = {v: i for i, v in enumerate(c)}
        loc = [(idx[a], idx[b]) for a, b in edges if a in idx and b in idx]
        d = {}
        for mask in range(1 << len(c)):
            ed = [(p, q) for p, q in loc if not (mask >> p & 1) and not (mask >> q & 1)]
            cnt = [0] * (len(c) // 2 + 2)
            k = len(ed)
            for r in range(k + 1):
                for sel in combinations(range(k), r):
                    used = 0; ok = True
                    for i in sel:
                        p, q = ed[i]
                        if used >> p & 1 or used >> q & 1:
                            ok = False; break
                        used |= (1 << p) | (1 << q)
                    if ok:
                        cnt[r] += 1
            while len(cnt) > 1 and cnt[-1] == 0:
                cnt.pop()
            d[mask] = cnt
        tab.append((c, idx, d))
    total = [0]
    order = list(B)
    pos = {v: i for i, v in enumerate(order)}

    def rec(i, used, k):
        nonlocal total
        if i == len(order):
            prod = [1]
            for c, idx, d in tab:
                mask = 0
                for v in c:
                    if v in used:
                        mask |= 1 << idx[v]
                prod = _mul(prod, d[mask])
            shifted = [0] * k + prod
            total = _add(total, shifted)
            return
        v = order[i]
        if v in used:
            rec(i + 1, used, k); return
        rec(i + 1, used, k)                       # v unmatched
        for w in adj[v]:
            if w in used:
                continue
            # an edge with both ends in the separator must be initiated by its EARLIER end only,
            # or it is counted once from each end
            if w in pos and pos[w] < i:
                continue
            rec(i + 1, used | {v, w}, k + 1)

    rec(0, set(), 0)
    while len(total) > 1 and total[-1] == 0:
        total.pop()
    return total


def mu_expr(m, n):
    return sum((-1) ** k * mk * x ** (n - 2 * k) for k, mk in enumerate(m))


def build(branch_size, delta, c, b):
    """c copies of a path on branch_size vertices, plus b boundary vertices."""
    edges = []
    nxt = b
    branches = []
    for _ in range(c):
        vs = list(range(nxt, nxt + branch_size))
        nxt += branch_size
        for i in range(branch_size - 1):
            edges.append((vs[i], vs[i + 1]))
        branches.append(vs)
    # each branch vertex takes (delta - its internal degree) boundary neighbours, round robin
    slot = 0
    for vs in branches:
        for j, v in enumerate(vs):
            internal = (1 if j == 0 or j == branch_size - 1 else 2) if branch_size > 1 else 0
            need = delta - internal
            chosen = []
            while len(chosen) < need:
                cand = slot % b
                slot += 1
                if cand not in chosen:
                    chosen.append(cand)
            for hb in chosen:
                edges.append((v, hb))
    return nxt, sorted((min(a, bb), max(a, bb)) for a, bb in edges), list(range(b)), branches


def report(name, branch_size, delta, kappa, c, b, theta_sq):
    n, e, B, branches = build(branch_size, delta, c, b)
    assert len(set(e)) == len(e), "multi-edge"
    deg = [0] * n
    for a, bb in e:
        deg[a] += 1; deg[bb] += 1
    dmin, dmax = min(deg), max(deg)
    bound = (delta - 2) * kappa + 2
    S = [v for vs in branches for v in vs]
    boundary = set()
    for a, bb in e:
        if (a in S) != (bb in S):
            boundary.add(a if a not in S else bb)
    m = match_counts_sep(n, e, B)
    mu = sp.Poly(mu_expr(m, n), x)
    val = mu.eval(sp.sqrt(theta_sq))
    print(f"{name}")
    print(f"  n={n} delta={dmin} Delta={dmax}   bound requires Delta > (delta-2)kappa+2 = {bound}"
          f"  -> Delta >= {bound+1}   attained: {dmax == bound + 1}")
    print(f"  Aomoto: cc(G[S]) = {len(branches)} > |boundary| = {len(boundary)}  "
          f"-> {'YES' if len(branches) > len(boundary) else 'NO'}")
    print(f"  mu_G(sqrt{theta_sq}) = {sp.simplify(val)}   (must be 0)")
    print(f"  mu_G = {sp.factor(mu.as_expr())}\n")
    return dmax == bound + 1 and len(branches) > len(boundary) and sp.simplify(val) == 0


ok = True
ok &= report("(delta,kappa)=(3,2): c copies of K_2", 2, 3, 2, 5, 4, 1)
ok &= report("(delta,kappa)=(3,3): c copies of P_3", 3, 3, 3, 6, 5, 2)
ok &= report("(delta,kappa)=(4,2): c copies of K_2", 2, 4, 2, 7, 6, 1)
print("ALL SHARP" if ok else "SOMETHING FAILED")
