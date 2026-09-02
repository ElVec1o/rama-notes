"""The exact certificate for membership in the point spectrum, with no floating point.

Li, Magee, Sabri and Thomas prove that theta is an eigenvalue of the maximal abelian cover exactly
when theta is a zero of mu_{G-Gamma} for every 2-regular subgraph Gamma, that is every vertex
disjoint union of cycles; Spier proves the maximal abelian and universal covers have the same
eigenvalues. The empty subgraph is 2-regular, so Gamma = empty recovers the containment of the
point spectrum in the zeros of mu_G, and the content is the converse:

    a root theta of mu_G is NOT an eigenvalue of T_G  <=>  some 2-regular Gamma has
    mu_{G-Gamma}(theta) != 0.

Both halves are finite exact checks on integer polynomials. This is the test that should have been
used in the supplement. The density-of-states and ratio-system tests there decided eigenvalue
membership numerically, and that step is what produced the withdrawn claims about Conjectures D3
and C2: in each case the root was an eigenvalue after all.

FROZEN BEFORE THE DATA:
  P85. (a) The 14-vertex D3 construction at theta = sqrt3 has NO witness Gamma: every 2-regular
           subgraph leaves sqrt3 a root. The retraction is confirmed exactly, and the construction
           never came close.
       (b) Hall's 41-vertex graph at theta = sqrt5 DOES have a witness Gamma, so his counterexample
           is confirmed by an exact polynomial certificate rather than by a numerical gap estimate.
"""

import sys
from itertools import combinations


# ---------- exact matching polynomial by subset DP ----------

def matching_poly(n, edges):
    """Coefficients of mu_G(x) = sum_k (-1)^k m_k x^(n-2k), returned as the list [m_0, m_1, ...]."""
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    f = [None] * (1 << n)
    f[0] = [1]
    for S in range(1, 1 << n):
        v = (S & -S).bit_length() - 1
        cur = list(f[S & ~(1 << v)])          # v left unmatched
        nb = adj[v] & S
        while nb:
            u = (nb & -nb).bit_length() - 1
            nb &= nb - 1
            sub = f[S & ~(1 << v) & ~(1 << u)]
            for i, c in enumerate(sub):
                if i + 1 < len(cur):
                    cur[i + 1] += c
                else:
                    cur.append(c)
        f[S] = cur
    return f[(1 << n) - 1]


def eval_sqrt(m, n, d):
    """mu_G(sqrt d) as the pair (a, b) meaning a + b sqrt d, exactly, from the m_k list."""
    a = b = 0
    for k, mk in enumerate(m):
        e = n - 2 * k                       # power of x
        s = (-1) ** k * mk
        p, q = (1, 0)                       # (sqrt d)^e = p + q sqrt d, p,q integers
        if e % 2 == 0:
            p = d ** (e // 2)
        else:
            q = d ** ((e - 1) // 2)
        a += s * p
        b += s * q
    return a, b


# ---------- cycles and 2-regular subgraphs ----------

def all_cycles(n, edges):
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen = set()
    out = []

    def dfs(start, v, path, inpath):
        for u in adj[v]:
            if u == start and len(path) >= 3:
                key = frozenset(path)
                if key not in seen:
                    seen.add(key)
                    out.append(frozenset(path))
            elif u > start and not (inpath >> u & 1):
                dfs(start, u, path + [u], inpath | (1 << u))

    for s in range(n):
        dfs(s, s, [s], 1 << s)
    return out


def two_regular_subgraphs(n, edges, cap=None):
    """All vertex sets spanned by a vertex-disjoint union of cycles, including the empty one."""
    cyc = all_cycles(n, edges)
    masks = []
    for c in cyc:
        m = 0
        for v in c:
            m |= 1 << v
        masks.append(m)
    out = []

    def rec(i, used):
        out.append(used)
        if cap is not None and len(out) > cap:
            raise RuntimeError("too many 2-regular subgraphs")
        for j in range(i, len(masks)):
            if not (masks[j] & used):
                rec(j + 1, used | masks[j])

    rec(0, 0)
    return masks, out


def restrict(n, edges, removed):
    keep = [v for v in range(n) if not (removed >> v & 1)]
    idx = {v: i for i, v in enumerate(keep)}
    e = [(idx[a], idx[b]) for a, b in edges
         if not (removed >> a & 1) and not (removed >> b & 1)]
    return len(keep), e


def certificate(n, edges, d, label, cap=200000):
    """Is sqrt d an eigenvalue of T_G? Returns (verdict, number of Gamma, witness or None)."""
    masks, subs = two_regular_subgraphs(n, edges, cap=cap)
    witness = None
    for used in subs:
        nn, ee = restrict(n, edges, used)
        m = matching_poly(nn, ee)
        a, b = eval_sqrt(m, nn, d)
        if a != 0 or b != 0:
            witness = (used, a, b)
            break
    print(f"  {label}: n={n} cycles={len(masks)} 2-regular subgraphs={len(subs)}")
    if witness is None:
        print(f"    every Gamma leaves sqrt{d} a root of mu_(G-Gamma).")
        print(f"    VERDICT: sqrt{d} IS an eigenvalue of T_G. Exact, no floating point.")
        return True, len(subs), None
    used, a, b = witness
    vs = [v for v in range(n) if used >> v & 1]
    print(f"    witness Gamma on vertices {vs}: mu_(G-Gamma)(sqrt{d}) = {a} + {b} sqrt{d} != 0")
    print(f"    VERDICT: sqrt{d} is NOT an eigenvalue of T_G. Exact, no floating point.")
    return False, len(subs), witness
