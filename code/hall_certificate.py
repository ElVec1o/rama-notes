"""Hall's 41-vertex counterexample, certified exactly by the 2-regular-subgraph criterion.

The graph is a centre c joined to p blocks. A block is K_{2,q} on {v,w} and u_1..u_q, with a pendant
leaf on w, and c is joined to v. Every cycle lies inside a block and is a 4-cycle v-u_a-w-u_b-v,
because K_{2,q} is bipartite with parts of size 2; and any two of them share v and w, so a 2-regular
subgraph uses at most one cycle per block. Hence Gamma is determined by a set of t blocks together
with a choice of two u's in each.

Deleting such a Gamma removes v and w from each chosen block, which isolates that block's remaining
q-2 vertices u and its leaf, and severs the edge c-v. So

    G - Gamma  =  H_{p-t}  disjoint union  (q-1)t isolated vertices,

where H_s is c joined to s intact blocks, and the cut-vertex recursion at c gives

    mu_{H_s} = x mu_B^s - s mu_{B-v} mu_B^{s-1}.

Only mu_B and mu_{B-v}, on 8 and 7 vertices, need the subset DP. The formula is validated against
brute force at p = 1 and p = 2.
"""

import sys
sys.path.insert(0, '.')
from exact_cover_certificate import matching_poly, eval_sqrt, certificate


def hall(p, q):
    """Returns (n, edges). Vertex 0 is the centre."""
    edges = []
    nxt = 1
    for _ in range(p):
        v, w = nxt, nxt + 1
        nxt += 2
        us = []
        for _ in range(q):
            u = nxt; nxt += 1
            us.append(u)
            edges += [(v, u), (w, u)]
        leaf = nxt; nxt += 1
        edges.append((w, leaf))
        edges.append((0, v))
    return nxt, edges


def block(q):
    """B on 8 vertices for q=5: v=0, w=1, u's 2..q+1, leaf q+2."""
    e = []
    for i in range(q):
        e += [(0, 2 + i), (1, 2 + i)]
    e.append((1, 2 + q))
    return q + 3, e


def polymul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def to_coeffs(m, n):
    """m_k list -> full coefficient list of mu(x), index = power of x."""
    c = [0] * (n + 1)
    for k, mk in enumerate(m):
        c[n - 2 * k] += (-1) ** k * mk
    return c


def ev(c, d):
    """c is a coefficient list indexed by power of x; evaluate at sqrt d exactly."""
    a = b = 0
    for e, co in enumerate(c):
        if not co:
            continue
        if e % 2 == 0:
            a += co * d ** (e // 2)
        else:
            b += co * d ** ((e - 1) // 2)
    return a, b


def mu_H(s, muB, muBv, n_B):
    """mu of c joined to s identical blocks, as a coefficient list."""
    if s == 0:
        return [0, 1]                       # the single vertex c
    powB = [1]
    for _ in range(s):
        powB = polymul(powB, muB)
    term1 = polymul([0, 1], powB)           # x * muB^s
    powBm1 = [1]
    for _ in range(s - 1):
        powBm1 = polymul(powBm1, muB)
    term2 = polymul(muBv, powBm1)
    out = list(term1)
    for i, y in enumerate(term2):
        while len(out) <= i:
            out.append(0)
        out[i] -= s * y
    return out


def main():
    q = 5
    nB, eB = block(q)
    muB = to_coeffs(matching_poly(nB, eB), nB)
    nBv, eBv = nB - 1, [(a - 1, b - 1) for a, b in eB if a != 0 and b != 0]
    muBv = to_coeffs(matching_poly(nBv, eBv), nBv)
    print(f"block B: {nB} vertices, mu_B coefficients (low to high) = {muB}")
    print(f"B - v:   {nBv} vertices, mu coefficients = {muBv}\n")

    print("validating the cut formula against brute force:")
    for p in (1, 2):
        n, e = hall(p, q)
        brute = to_coeffs(matching_poly(n, e), n)
        form = mu_H(p, muB, muBv, nB)
        form = form + [0] * (len(brute) - len(form))
        print(f"  p={p} n={n}: {'MATCH' if brute == form[:len(brute)] else 'MISMATCH'}")

    print("\nHall's graph: p=5, q=5, n=41, theta=sqrt5")
    d = 5
    print(f"  mu_B(sqrt5)     = {ev(muB, d)}")
    print(f"  mu_(B-v)(sqrt5) = {ev(muBv, d)}")
    print(f"\n  {'t':>2} {'blocks hit':>11} {'s=p-t':>6} {'mu_(G-Gamma)(sqrt5)':>28} {'zero?':>7}")
    witness = None
    for t in range(0, 6):
        s = 5 - t
        a, b = ev(mu_H(s, muB, muBv, nB), d)
        # times sqrt5^((q-1)t) = 5^(2t), never zero
        f = d ** (2 * t)
        a, b = a * f, b * f
        z = (a == 0 and b == 0)
        if not z and witness is None:
            witness = (t, a, b)
        print(f"  {t:>2} {t:>11} {s:>6} {f'{a} + {b} sqrt5':>28} {str(z):>7}")

    print()
    if witness is None:
        print("  every Gamma leaves sqrt5 a root: sqrt5 IS an eigenvalue and Hall's example fails.")
        return 1
    t, a, b = witness
    print(f"  WITNESS at t={t}: a Gamma consisting of one 4-cycle in each of {t} blocks gives")
    print(f"  mu_(G-Gamma)(sqrt5) = {a} + {b} sqrt5 != 0.")
    print("  VERDICT: sqrt5 is NOT an eigenvalue of T_G. Hall's counterexample is confirmed by an")
    print("  exact polynomial certificate, with no floating point and no gap estimate in it.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
