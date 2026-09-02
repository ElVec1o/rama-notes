"""Free trees by level sequence, with exact matching polynomials.

Prufer enumeration is hopeless here: it produces n^(n-2) labelled trees, 10^10 at n = 12, to
reach the 551 free trees that actually exist. The Beyer-Hedetniemi successor walks rooted-tree
level sequences directly, and AHU canonical forms at the centroid cut rooted trees down to free
ones. Counts are checked against the known free-tree numbers as a self-test.
"""


def level_sequences(n):
    """All rooted trees on n vertices as level sequences, Beyer-Hedetniemi order."""
    if n == 1:
        yield [0]
        return
    L = list(range(n))
    while True:
        yield list(L)
        p = max((i for i in range(n) if L[i] > 1), default=None)
        if p is None:
            return
        q = max(i for i in range(p) if L[i] == L[p] - 1)
        new = L[:p]
        for i in range(p, n):
            new.append(new[i - (p - q)])
        L = new


def tree_of(L):
    """Adjacency lists from a level sequence."""
    n = len(L)
    adj = [[] for _ in range(n)]
    stack = {}
    for i, d in enumerate(L):
        stack[d] = i
        if d > 0:
            par = stack[d - 1]
            adj[i].append(par)
            adj[par].append(i)
    return adj


def centroids(n, adj):
    if n == 1:
        return [0]
    size = [1] * n
    order, seen, st = [], [False] * n, [0]
    par = [-1] * n
    seen[0] = True
    while st:
        v = st.pop()
        order.append(v)
        for u in adj[v]:
            if not seen[u]:
                seen[u] = True
                par[u] = v
                st.append(u)
    for v in reversed(order):
        if par[v] >= 0:
            size[par[v]] += size[v]
    best, out = n + 1, []
    for v in range(n):
        m = max([size[u] if par[u] == v else n - size[v] for u in adj[v]] or [0])
        if m < best:
            best, out = m, [v]
        elif m == best:
            out.append(v)
    return out


def ahu(v, p, adj):
    sub = sorted(ahu(u, v, adj) for u in adj[v] if u != p)
    return "(" + "".join(sub) + ")"


def canon(n, adj):
    return min(ahu(c, -1, adj) for c in centroids(n, adj))


def free_trees(n):
    seen = set()
    for L in level_sequences(n):
        adj = tree_of(L)
        c = canon(n, adj)
        if c not in seen:
            seen.add(c)
            yield adj


def _mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def _add(a, b):
    if len(a) < len(b):
        a, b = b, a
    out = list(a)
    for i, y in enumerate(b):
        out[i] += y
    return out


def matching_counts(n, adj):
    """m_0, m_1, ..., m_nu as exact integers, by tree DP."""
    order, par, seen, st = [], [-1] * n, [False] * n, [0]
    seen[0] = True
    while st:
        v = st.pop()
        order.append(v)
        for u in adj[v]:
            if not seen[u]:
                seen[u] = True
                par[u] = v
                st.append(u)
    f0 = [None] * n   # v unmatched
    f1 = [None] * n   # v matched to one of its children
    for v in reversed(order):
        kids = [u for u in adj[v] if par[u] == v]
        g = [1]
        for c in kids:
            g = _mul(g, _add(f0[c], f1[c]))
        f0[v] = g
        tot = [0]
        for c in kids:
            h = [0, 1]                       # the edge v-c
            h = _mul(h, f0[c])
            for d in kids:
                if d != c:
                    h = _mul(h, _add(f0[d], f1[d]))
            tot = _add(tot, h)
        f1[v] = tot
    m = _add(f0[order[0]], f1[order[0]])
    while len(m) > 1 and m[-1] == 0:
        m.pop()
    return m


KNOWN = {1: 1, 2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106,
         11: 235, 12: 551, 13: 1301, 14: 3159, 15: 7741, 16: 19320, 17: 48629,
         18: 123867}

if __name__ == '__main__':
    for n in range(1, 13):
        c = sum(1 for _ in free_trees(n))
        print(f"n={n:>2} free trees={c:>6} expected={KNOWN[n]:>6} "
              f"{'OK' if c == KNOWN[n] else 'MISMATCH'}")
