"""RETRACTED. The conclusion of this script is wrong.

It concluded that a graph built from p identical branches on a k-vertex separator, with p > k,
gives a root of mu_G outside spec(T_G), and hence refutes Conjecture D3 or C2. It does not. In
every such graph the branch union is a theta-Aomoto subset: its components are the p branches, its
boundary lies in the separator so has at most k vertices, and p > k is exactly the Aomoto
inequality |boundary| < components. By the criterion of Banks, Garza-Vargas and Mukherjee the root
is therefore an EIGENVALUE of the universal cover, hence lies IN spec(T_G).

The spectral certificates below are the source of the error. The Angel-Friedman-Hoory ratio system
degenerates at the root with g(hub -> leaf) = infinity; that pole is the localized eigenstate
announcing itself, and it was misread as a removable coordinate singularity. The resolvent then
reported a vertex Green's function of exactly zero at the leaf, which is the same divergence sitting
in a denominator, and that was misread as the absence of an atom.

The correct analysis is in code/aomoto_obstruction.py. Conjectures D3 and C2 are OPEN. This file is
kept for the record and because the two-cut identity and the gap scans in it are still correct; only
the spectral verdict is retracted.
"""

"""Conjecture D3 is false: a 14-vertex graph of minimum degree three with a root in a gap.

Conjecture D3 of paper 2a reads: every finite graph of minimum degree at least three satisfies
Zeros(mu_G) contained in spec(T_G). This exhibits a counterexample on 14 vertices, which is a third
the size of Hall's 41-vertex counterexample to the unrestricted conjecture.

HOW IT WAS FOUND, and why the earlier sweep missed it. The two-cut identity is

    mu_G = A^{p-2} * (x^2 A^2 - p x (Bu + Bv) A + p D A + p(p-1) Bu Bv),

with A the matching polynomial of the branch. code/mindeg3.py swept 102 graphs of minimum degree
three and reported no violation, but it iterated over the roots of the BRACKET only and never over
the roots of A. Since A^{p-2} divides mu_G for every p >= 3, the roots of A are roots of mu_G, and
they are exactly the localized subgraph divisibility mu_H | mu_G that produced Hall's counterexample.
The hypothesis was never tested against the mechanism it was invented to defeat.

Once the roots of A are tested the counterexample is immediate, because Hall's divisor is a STAR: his
violating root sqrt5 is the top matching root of K_{1,5}, whose matching polynomial is x^4(x^2-5).
A star's leaves have degree one IN the divisor however large their degree is IN G, so minimum degree
three does not forbid a star divisor. It only forces the leaves to pick up extra edges elsewhere.

THE GRAPH. Two hubs u, v. Three copies of K_{1,3}, with centre c_i and leaves l_{i,1..3}. Every leaf
is joined to both hubs. Then

    deg(c_i) = 3,   deg(l_{i,j}) = 1 + 2 = 3,   deg(u) = deg(v) = 9,

so the minimum degree is three, and n = 2 + 3*4 = 14, with 27 edges. The branch is the star K_{1,3},
whose matching polynomial is A = x^2(x^2 - 3), so sqrt3 is a root of mu_G of multiplicity p - 2 = 1.

WHY THE OBVIOUS CERTIFICATE DOES NOT WORK HERE, which is the trap this file exists to document.
The Angel-Friedman-Hoory ratio system lambda = 1/r_e + sum_{e -> f} r_f, solved at lambda and
declared outside spec(T) when its decay matrix R_{e,f} = r_f^2 has spectral radius below one, is the
certificate used for Hall's counterexample in code/hall_certificate.py. Under Aut(G) the 54 directed
edges here fall into four orbits, centre-to-leaf, leaf-to-centre, leaf-to-hub and hub-to-leaf, so the
system is four equations. Eliminating gives a QUADRATIC, whose two real branches both have decay
above one; that reads as "sqrt3 lies in spec(T_G)" and it is wrong. At lambda a hair either side of
sqrt3 there are THREE real branches and the third has decay about 0.87. That third branch has
r(leaf->hub) passing through 0 and r(hub->leaf) through infinity exactly at sqrt3, so eliminating
multiplies by r(leaf->hub) and silently drops it. The ratio parametrisation has a coordinate
singularity at sqrt3, not a spectral point, and a pointwise solver returns nothing there for the same
reason. That is precisely how a counterexample can hide behind a "clean" verdict.

THE CERTIFICATE ACTUALLY USED is the resolvent, which has no such coordinate. The cavity recursion
g_e = 1/(z - sum_{e->f} g_f) at z = lambda + i*eta converges on any tree for eta > 0, and the density
of states is (1/pi) Im sum_w G_w. Its three signatures as eta -> 0 are distinct and unambiguous:

    outside spec(T)      Im G -> 0 linearly in eta
    inside a band        Im G -> a positive constant
    an ATOM of spec(T)   Im G ~ c/eta, diverging

The distinction matters exactly here, because spec(T) is closed: showing every point NEAR sqrt3 is
outside does not show sqrt3 is, since sqrt3 could be an isolated point of the spectrum. The paper
records such a point already, the isolated {0} of the biregular cover, so this is a live possibility
and not a formality. The resolvent settles it, and it carries its own internal control: run on THIS
graph at lambda = 0 it reports the atom, and at sqrt3 it reports decay to zero.

FROZEN BEFORE THE DATA:
  P63. (a) mu_G(sqrt3) = 0 exactly, computed from the graph.
       (b) On the same graph the probe reports an atom at lambda = 0 and a band just below sqrt3,
           so it is not merely reporting "outside" everywhere.
       (c) At sqrt3 the probe decays linearly in eta, so sqrt3 is neither in a band nor an atom,
           hence sqrt3 is not in spec(T_G) and D3 is false.
       (d) The same construction with p = 2 is NOT a counterexample, since A^0 = 1 carries no root,
           which is why the violation needs three branches and not two.

FALSIFICATION. If (a) fails the graph is irrelevant. If Im G at sqrt3 tends to a positive constant
the point is in a band, and if it diverges the point is an atom; either way sqrt3 lies in spec(T_G)
and D3 survives.

Both probes are validated against covers whose spectrum is known in closed form: for K_{a,b} the
cover is the (a,b)-biregular tree with spectrum {0} u +-[|s-t|, s+t], s = sqrt(a-1), t = sqrt(b-1),
giving an atom at 0, a gap above it and a band beyond, and for a 3-regular graph the cover is the
3-regular tree with no gap at all. All are reproduced below before the counterexample is asserted.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from twocut import mu_of, x
from gapscale import setup, gap_profile, connectivity

M_STAR = 3
P_COPIES = 3


def build(m=M_STAR, p=P_COPIES):
    """Two hubs, p copies of K_{1,m}, every leaf joined to both hubs."""
    u, v = 0, 1
    edges = []
    nxt = 2
    for _ in range(p):
        c = nxt; nxt += 1
        for _ in range(m):
            l = nxt; nxt += 1
            edges.append((c, l))
            edges.append((l, u))
            edges.append((l, v))
    return nxt, sorted(edges)


def adj_of(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    return adj


def directed(edges):
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    return de


def orbit_of(a, b, n, adj, hubs, centres):
    """Which of the four directed-edge orbits (a -> b) belongs to."""
    ta = 'h' if a in hubs else ('c' if a in centres else 'l')
    tb = 'h' if b in hubs else ('c' if b in centres else 'l')
    return {('c', 'l'): 0, ('l', 'c'): 1, ('l', 'h'): 2, ('h', 'l'): 3}[(ta, tb)]


def im_green(n, edges, lam, eta, iters=400000, tol=1e-14):
    """|Im sum_w G_w(lambda + i eta)| from the cavity recursion on the universal cover.

    Damped because near a band edge the undamped iteration oscillates; the damping changes the
    fixed point not at all, only the path to it."""
    adj = adj_of(n, edges)
    B, M = setup(n, edges)
    de = directed(edges)
    z = complex(lam, eta)
    g = np.full(M, 0.1 + 0.1j)
    for _ in range(iters):
        new = 1.0 / (z - B @ g)
        d = np.max(np.abs(new - g))
        g = 0.5 * g + 0.5 * new
        if d < tol:
            break
    idx = {e: k for k, e in enumerate(de)}
    tot = 0.0
    for w in range(n):
        tot += (1.0 / (z - sum(g[idx[(u, w)]] for u in adj[w]))).imag
    return abs(tot)


def classify(n, edges, lam, etas=(1e-2, 1e-3, 1e-4, 1e-5)):
    """outside / band / atom, from how Im G scales in eta."""
    v = [im_green(n, edges, lam, e) for e in etas]
    ratio = v[-1] / v[-2] if v[-2] > 0 else float('inf')
    if ratio > 3.0:
        kind = 'ATOM'
    elif ratio < 0.3:
        kind = 'outside spec'
    else:
        kind = 'in a band'
    return kind, v


def main():
    lam = sp.sqrt(3)
    print("P63 (frozen): Conjecture D3 is false, on 14 vertices.\n")

    print("(0) the gap detector, against covers whose spectrum is known in closed form.")
    ok0 = True
    for (a, b) in [(3, 4), (2, 3), (3, 5)]:
        e = [(i, a + j) for i in range(a) for j in range(b)]
        s, t = math.sqrt(a - 1), math.sqrt(b - 1)
        g = gap_profile(a + b, e)
        good = len(g) == 1 and abs(g[0][1] - abs(s - t)) < 0.05
        ok0 = ok0 and good
        print(f"    K_{{{a},{b}}}: exact gap (0,{abs(s-t):.4f})  measured "
              f"{[(round(q, 3), round(w, 3)) for q, w in g]}  {'OK' if good else 'MISMATCH'}")
    for nm, nn, e in [("K_4", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
                      ("prism", 6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                                    (0, 3), (1, 4), (2, 5)])]:
        g = gap_profile(nn, e)
        good = len(g) == 0
        ok0 = ok0 and good
        print(f"    {nm} 3-regular: exact answer no gap  measured "
              f"{[(round(q, 3), round(w, 3)) for q, w in g]}  {'OK' if good else 'MISMATCH'}")
    if not ok0:
        print("  the detector fails a known case; nothing below is meaningful.")
        return 1
    print()

    print("(0b) the same probe on the biregular cover, whose three signatures are known exactly.")
    e34 = [(i, 3 + j) for i in range(3) for j in range(4)]
    for lamv, expect in [(0.0, 'ATOM'), (0.15, 'outside spec'), (1.5, 'in a band')]:
        kind, v = classify(7, e34, lamv)
        good = kind == expect
        ok0 = ok0 and good
        print(f"    K_{{3,4}} at {lamv:<5}: expected {expect:<13} got {kind:<13} "
              f"|Im G| = {'  '.join(f'{q:.3e}' for q in v)}  {'OK' if good else 'MISMATCH'}")
    if not ok0:
        print("  the resolvent probe fails a known case; nothing below is meaningful.")
        return 1
    print()

    n, edges = build()
    adj = adj_of(n, edges)
    deg = [len(adj[i]) for i in range(n)]
    hubs = {0, 1}
    centres = {i for i in range(n) if i not in hubs and not (adj[i] & hubs)}
    col = {}

    def bip():
        for s in range(n):
            if s in col:
                continue
            col[s] = 0; st = [s]
            while st:
                w = st.pop()
                for y in adj[w]:
                    if y not in col:
                        col[y] = 1 - col[w]; st.append(y)
                    elif col[y] == col[w]:
                        return False
        return True

    print(f"(1) the graph: n={n}, {len(edges)} edges, degrees min {min(deg)} max {max(deg)}, "
          f"connectivity {connectivity(n, edges)}, "
          f"{'bipartite' if bip() else 'non-bipartite'}")
    print(f"    hubs {sorted(hubs)}, centres {sorted(centres)}, "
          f"{n - len(hubs) - len(centres)} leaves")

    mu = sp.Poly(sp.expand(mu_of(adj, set(range(n)))), x)
    q, rem = sp.div(mu, sp.Poly(x ** 2 - 3, x))
    val = sp.simplify(mu.eval(lam))
    print(f"    mu_G(sqrt3) = {val};  (x^2-3) | mu_G : {rem.is_zero}")
    print(f"    mu_G = {sp.factor(mu.as_expr())}")
    if val != 0:
        print("  P63(a) FAILS: sqrt3 is not a root and there is no counterexample here.")
        return 1

    print("\n(2) why the ratio certificate is not used: it degenerates exactly at sqrt3.")
    t = sp.symbols('t', real=True)
    for tag, lv in (("sqrt3 - 0.005", float(lam) - 0.005), ("sqrt3 exactly", float(lam)),
                    ("sqrt3 + 0.005", float(lam) + 0.005)):
        lz = sp.Float(lv, 30)
        e1 = 1 / (lz - 2 * t)
        e2 = 1 / (lz - 2 * e1)
        e4 = (lz * t - 1) / ((P_COPIES * M_STAR - 1) * t)
        num, _ = sp.fraction(sp.cancel(sp.together(e4 * (lz - e2 - t) - 1)))
        rs = [sp.re(z) for z in sp.Poly(sp.expand(num), t).nroots(n=30, maxsteps=5000)
              if abs(sp.im(z)) < 1e-20]
        print(f"    lambda = {tag:<14}: {len(rs)} real branches, "
              f"r(leaf->hub) = {', '.join(f'{float(z):+.5f}' for z in rs)}")
    print("    The branch that certifies sqrt3 has r(leaf->hub) crossing zero there, so the")
    print("    elimination drops it and the certificate reports the opposite of the truth.")

    print("\n(3) the resolvent, on this graph, at four values of lambda.")
    ok = True
    for lamv, tag, expect in [(0.0, "the origin", 'ATOM'),
                              (1.68, "below the root", 'in a band'),
                              (float(lam), "sqrt3, the root", 'outside spec'),
                              (2.40, "well above", 'in a band')]:
        kind, v = classify(n, edges, lamv)
        good = kind == expect
        ok = ok and good
        print(f"    lambda = {lamv:<9.6f} ({tag:<15}) {kind:<13} "
              f"|Im G| = {'  '.join(f'{q:.3e}' for q in v)}  {'OK' if good else 'UNEXPECTED'}")
    if not ok:
        print("  P63(b)/(c) FAIL: sqrt3 is not cleanly outside spec(T_G).")
        return 1
    print("    The atom at the origin is the control: the same probe, the same graph, and it")
    print("    reports an atom there and linear decay at sqrt3. So sqrt3 is in neither a band")
    print("    nor an atom, and spec(T_G) does not contain it.")

    g = gap_profile(n, edges)
    inside = [(lo, hi) for lo, hi in g if lo < float(lam) < hi]
    print(f"\n(4) gaps of spec(T_G) from the independent scan: "
          f"{[(round(a, 3), round(b, 3)) for a, b in g]}")
    print(f"    sqrt3 = {float(lam):.6f} lies in {inside}")

    print("\n  P63 (a)(b)(c) ALL HOLD.  CONJECTURE D3 IS FALSE.")
    print(f"  G has {n} vertices, minimum degree {min(deg)}, and mu_G(sqrt3) = 0, while sqrt3 is")
    print("  outside spec(T_G) by a decay certificate. The divisor is the star K_{1,3}, which is")
    print("  Hall's mechanism verbatim; minimum degree three constrains G and not the divisor, so")
    print("  it never touched the engine. Conjecture 10 does not have a minimum-degree repair.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
