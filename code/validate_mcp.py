"""Validation of mixed_char_poly against (i) matching counts on biregular
bipartite graphs, and (ii) brute-force sympy differentiation on random
NON-diagonal families."""
import numpy as np
from itertools import combinations
from fractions import Fraction
from mixed_char_poly import (mixed_char_poly, mixed_char_poly_exact,
                             mixed_char_poly_sympy, nu_from_graph,
                             projections_from_graph, matching_counts,
                             band, roots_of)


def complete_bipartite(p, q):
    return [(1 << q) - 1 for _ in range(p)]


def subdivision(edges, n):
    """S(H) for simple graph H with n vertices and given edge list.
    P = vertices of H (degree = deg_H), Q = edges of H (degree 2)."""
    adj = [0] * n
    for k, (u, v) in enumerate(edges):
        adj[u] |= 1 << k
        adj[v] |= 1 << k
    return adj


K4_edges = list(combinations(range(4), 2))
K33_edges = [(i, 3 + j) for i in range(3) for j in range(3)]
CUBE_edges = []
for u in range(8):
    for bit in range(3):
        v = u ^ (1 << bit)
        if u < v:
            CUBE_edges.append((u, v))

TESTS = [
    ("K_{3,4}",   complete_bipartite(3, 4), 3, 4, 4, 3),
    ("K_{3,5}",   complete_bipartite(3, 5), 3, 5, 5, 3),
    ("K_{4,5}",   complete_bipartite(4, 5), 4, 5, 5, 4),
    ("S(K_4)",    subdivision(K4_edges, 4), 4, 6, 3, 2),
    ("S(K_{3,3})", subdivision(K33_edges, 6), 6, 9, 3, 2),
    ("S(Q_3)",    subdivision(CUBE_edges, 8), 8, 12, 3, 2),
]

print("=" * 78)
print("VALIDATION 1: mu[P_1..P_q] == nu_G  (diagonal / graph case)")
print("=" * 78)
allok = True
for name, adj, p, q, a, b in TESTS:
    # sanity on biregularity
    degP = [bin(adj[i]).count('1') for i in range(p)]
    degQ = [sum(1 for i in range(p) if (adj[i] >> k) & 1) for k in range(q)]
    assert set(degP) == {a}, (name, degP)
    assert set(degQ) == {b}, (name, degQ)
    nu = nu_from_graph(adj, p, q)
    Ps = projections_from_graph(adj, p, q)
    if q <= 9:
        mu_ex = mixed_char_poly_exact(Ps)
        ok_ex = all(Fraction(nu[i]) == mu_ex[i] for i in range(p + 1))
    else:
        mu_ex, ok_ex = None, None
    Pf = [np.array(P, dtype=float) for P in Ps]
    mu_f = mixed_char_poly(Pf)
    err = np.max(np.abs(mu_f - np.array(nu, dtype=float)))
    scale = max(1.0, np.max(np.abs(np.array(nu, dtype=float))))
    ok_f = err / scale < 1e-9
    allok &= bool(ok_f) and (ok_ex is not False)
    print(f"{name:12s} p={p} q={q} (a,b)=({a},{b})  exact_match={ok_ex}  "
          f"float_relerr={err/scale:.2e}")
    print(f"    nu_G  = {nu}")
    r, im = roots_of(nu)
    lo, hi = band(a, b)
    print(f"    roots = {np.array2string(r, precision=6)}   "
          f"band=[{lo:.6f},{hi:.6f}]  min_root={r.min():.6f}  "
          f"margin_lo={r.min()-lo:+.6f}  margin_hi={hi-r.max():+.6f}")
print("GRAPH VALIDATION PASSED:", allok)

print()
print("=" * 78)
print("VALIDATION 2: subset formula vs brute-force sympy on NON-diagonal A")
print("=" * 78)
rng = np.random.default_rng(11)
ok2 = True
for trial, (p, q) in enumerate([(2, 3), (3, 3), (3, 4), (4, 3)]):
    # random small-integer symmetric matrices (not PSD, not projections --
    # the identity is algebraic so this is a stronger test)
    As = []
    for k in range(q):
        X = rng.integers(-2, 3, size=(p, p))
        S = X + X.T
        As.append([[int(S[i][j]) for j in range(p)] for i in range(p)])
    c_sub = mixed_char_poly_exact(As)
    c_sym = mixed_char_poly_sympy(As)
    same = all(Fraction(c_sub[i]) == Fraction(c_sym[i]) for i in range(p + 1))
    ok2 &= same
    print(f"  p={p} q={q}: subset={[str(x) for x in c_sub]}  match={same}")
print("SYMBOLIC VALIDATION PASSED:", ok2)
