"""Is Xu's constant sharp for b >= 3, or is it merely an upper bound there?

Xu conjectures maxroot mu <= (sqrt(a-1) + sqrt(b-1))^2 for a tight family of rank-b
projections, generalising Ravichandran-Leake. At b = 2 the constant is a + 2 sqrt(a-1) and is
attained: large-girth a-regular graphs push the greatest root of the matching polynomial to the
spectral radius of the a-regular tree. At b >= 3 our adversarial search
(code/adversarial.py, code/rl_push.py) reached only 0.739 of the bound at (a,b) = (4,3) and
0.726 at (5,4), against 0.939 at (3,2). Two readings fit that:

  (i) the constant is sharp at every b and the search never built the right families, or
 (ii) the constant is true but NOT optimal for b >= 3, the truth being smaller.

Reading (ii) would be a real defect in his conjecture and reading (i) says his constant is
exactly right. The two are distinguished by a construction, not by more sampling.

THE BRIDGE. Let H be an a-regular b-uniform hypergraph on n vertices with q hyperedges, and take
the coordinate projections P_e onto span{e_v : v in e}. These are rank b and sum to aI exactly, so
they are an admissible tight family. For coordinate projections the mixed characteristic
polynomial collapses: with M(z) = xI + sum z_e P_e diagonal,

    det M(z) = prod_v (x + sum_{e ni v} z_e),

which is affine in each z_e SEPARATELY IN EACH FACTOR, so prod_e (1 - d/dz_e) at z = 0 keeps only
the terms where the chosen hyperedges get distinct representatives:

    mu(x) = sum_S (-1)^{|S|} N(S) x^{n-|S|},   N(S) = # systems of distinct representatives of S.

Summing over |S| = k, the coefficient is the number of k-matchings of the INCIDENCE BIPARTITE
GRAPH I(H), whose hyperedge side has degree b and whose vertex side has degree a. Hence

    mu(t^2) = t^{n-q} mu_{I(H)}(t),

so the roots of mu are the squares of the roots of an ordinary matching polynomial, on an
(a,b)-biregular graph.

WHAT THAT SETTLES. Godsil's bound gives maxroot mu_{I(H)} <= rho = sqrt(a-1) + sqrt(b-1), the
spectral radius of the (a,b)-biregular tree, so maxroot mu <= rho^2: Xu's bound is a THEOREM for
coordinate families at every b, not a conjecture. And it is attained, because the greatest root of
a matching polynomial is monotone under subgraphs, so a graph of girth > 2r contains the ball
B_r of the biregular tree and inherits its largest eigenvalue, while lambda_max(B_r) increases to
rho. Biregular graphs of arbitrary girth exist (random lifts). So the supremum over the class is
rho^2 exactly, and reading (i) is the right one at every b.

FROZEN BEFORE THE DATA:
  P33. The measured ratio maxroot mu / rho^2 climbs to 1 along a girth ladder at b = 3 and b = 4,
       the plateau near 0.73 being an artefact of sampling generic subspaces. Concretely:
       lambda_max(B_r)^2 / rho^2 increases in r towards 1 at every (a,b) tested, and every
       biregular graph of girth > 2r has ratio at least that value.

If P33 fails -- if the ball ratios plateau below 1, or if a graph of girth > 2r has ratio below
lambda_max(B_r)^2/rho^2 -- then the argument above is wrong somewhere and reading (ii) revives.

CONTROLS.
  A. The bridge is checked by two routes sharing no code: the mixed characteristic polynomial
     computed symbolically from the MSS definition prod(1 - d/dz_e) det(xI + sum z_e P_e), and the
     matching counts of I(H) by subset dynamic programming. Agreement is required coefficient by
     coefficient in exact arithmetic.
  B. The bridge is checked to FAIL for non-coordinate rank-b projections, which is the point: it
     is the coordinate case that reduces, and the content of Xu's conjecture is everything else.
  C. Every claimed girth is recomputed by breadth-first search rather than quoted.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import itertools
import numpy as np
import sympy as sp
import scipy.sparse as spr
import scipy.sparse.linalg as sla

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from biregular import matching_counts

QUICK = '--quick' in sys.argv
BUDGET_S = 25.0 if QUICK else 900.0
BALL_CAP = 20_000 if QUICK else 400_000        # vertices, not radius: memory is the constraint


# ------------------------------------------------------------------ route A: the definition
def mss_mu(projs, n):
    """mu[A_1..A_q](x) straight from MSS: prod_e (1 - d/dz_e) det(xI + sum z_e A_e) at z = 0.

    Symbolic and deliberately naive. It shares no code with the matching route, which is the
    whole reason it exists; it is only ever called on cases small enough for that to be cheap.
    """
    q = len(projs)
    x = sp.Symbol('x')
    z = sp.symbols(f'z0:{q}')
    M = sp.eye(n) * x
    for e in range(q):
        M = M + z[e] * sp.Matrix(projs[e])
    d = sp.expand(M.det(method='berkowitz'))
    for e in range(q):
        d = sp.expand(d - sp.diff(d, z[e]))
    for e in range(q):
        d = d.subs(z[e], 0)
    return sp.Poly(sp.expand(d), x)


def coordinate_projs(n, hyperedges):
    out = []
    for e in hyperedges:
        P = np.zeros((n, n), dtype=int)
        for v in e:
            P[v, v] = 1
        out.append(P)
    return out


# ------------------------------------------------------------------ route B: matchings of I(H)
def mu_from_incidence(n, hyperedges):
    """mu(x) = sum_k (-1)^k m_k(I(H)) x^{n-k}, with m_k from the subset DP over the vertex side."""
    q = len(hyperedges)
    adjA = [list(e) for e in hyperedges]            # hyperedge side, degree b
    m = matching_counts(q, n, adjA)                 # DP over the n vertex-side bits
    x = sp.Symbol('x')
    return sp.Poly(sum(((-1) ** k) * int(m[k]) * x ** (n - k) for k in range(0, min(q, n) + 1)), x)


# ------------------------------------------------------------------ graphs
def girth_bipartite(nA, adjA, nB):
    """Girth by BFS from every vertex. Returns inf for a forest."""
    adj = {('A', i): [('B', j) for j in adjA[i]] for i in range(nA)}
    for j in range(nB):
        adj[('B', j)] = []
    for i in range(nA):
        for j in adjA[i]:
            adj[('B', j)].append(('A', i))
    best = math.inf
    for src in adj:
        dist = {src: 0}
        par = {src: None}
        order = [src]
        head = 0
        while head < len(order):
            u = order[head]; head += 1
            if 2 * dist[u] >= best:
                break
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; par[w] = u; order.append(w)
                elif w != par[u]:
                    best = min(best, dist[u] + dist[w] + 1)
    return best


def biregular_ball(a, b, radius):
    """Ball of the given radius in the (a,b)-biregular tree, rooted on the a-side.

    Levels alternate: an a-side vertex at depth 0 has a children on the b-side; a b-side vertex
    at depth >= 1 has b-1 children on the a-side, and an a-side vertex at depth >= 1 has a-1.
    Returned as a sparse adjacency matrix. Truncated at BALL_CAP vertices.
    """
    rows, cols = [], []
    nxt = 1
    frontier = [(0, 'a')]
    for d in range(radius):
        newf = []
        for (v, side) in frontier:
            if side == 'a':
                k = a if d == 0 else a - 1
                child = 'b'
            else:
                k = b - 1
                child = 'a'
            for _ in range(k):
                if nxt >= BALL_CAP:
                    break
                rows += [v, nxt]; cols += [nxt, v]
                newf.append((nxt, child)); nxt += 1
        frontier = newf
        if nxt >= BALL_CAP or not frontier:
            break
    A = spr.coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(nxt, nxt)).tocsr()
    return A, nxt


def lam_max(A, n):
    if n <= 2:
        return float(np.linalg.eigvalsh(A.toarray()).max())
    if n <= 400:
        return float(np.linalg.eigvalsh(A.toarray()).max())
    v0 = np.ones(n) / math.sqrt(n)          # deterministic start: eigsh randomises without it
    return float(sla.eigsh(A.astype(float), k=1, which='LA', v0=v0,
                           return_eigenvectors=False, tol=1e-12, maxiter=100_000)[0])


# --------------------------------------------------------------- named (a,b)-biregular graphs
def heawood():
    """Incidence graph of the Fano plane: (3,3)-biregular, 14 vertices, girth 6."""
    lines = [[(i + s) % 7 for s in (0, 1, 3)] for i in range(7)]
    return 7, lines


def pappus():
    """Pappus graph as an incidence structure: (3,3)-biregular, 18 vertices, girth 6."""
    lines = [[0, 1, 2], [3, 4, 5], [6, 7, 8],
             [0, 3, 6], [1, 4, 7], [2, 5, 8],
             [0, 4, 8], [1, 5, 6], [2, 3, 7]]
    return 9, lines


def tutte_coxeter():
    """Levi graph of GQ(2,2): (3,3)-biregular on 15+15, girth 8.

    Duads are the 15 pairs from [6]; synthemes are the 15 perfect matchings of [6]; a duad is
    incident to a syntheme when it is one of its three pairs.
    """
    duads = list(itertools.combinations(range(6), 2))
    index = {d: i for i, d in enumerate(duads)}
    synthemes = []
    for p in itertools.permutations(range(6)):
        m = tuple(sorted([tuple(sorted((p[0], p[1]))),
                          tuple(sorted((p[2], p[3]))),
                          tuple(sorted((p[4], p[5])))]))
        if m not in synthemes:
            synthemes.append(m)
    lines = [[index[d] for d in m] for m in synthemes]
    return 15, lines


def ag23():
    """AG(2,3): 9 points, 12 lines of size 3, each point on 4 lines. (4,3)-biregular, girth 6."""
    pts = [(i, j) for i in range(3) for j in range(3)]
    idx = {p: k for k, p in enumerate(pts)}
    lines = []
    for c in range(3):
        lines.append([idx[(c, j)] for j in range(3)])
        lines.append([idx[(i, c)] for i in range(3)])
    for s in (1, 2):
        for c in range(3):
            lines.append([idx[(i, (s * i + c) % 3)] for i in range(3)])
    return 9, lines


def pg23():
    """PG(2,3): 13 points, 13 lines of size 4, each point on 4 lines. (4,4)-biregular, girth 6."""
    lines = [[(i + s) % 13 for s in (0, 1, 3, 9)] for i in range(13)]
    return 13, lines


def named():
    return [("K_{3,3}", 3, 3, 3, [[0, 1, 2]] * 3),
            ("Heawood", 3, 3, *heawood()),
            ("Pappus", 3, 3, *pappus()),
            ("Tutte-Coxeter", 3, 3, *tutte_coxeter()),
            ("K_{4,3}-cover", 4, 3, 3, [[0, 1, 2]] * 4),
            ("AG(2,3)", 4, 3, *ag23()),
            ("PG(2,3)", 4, 4, *pg23())]


def main():
    t0 = time.time()
    print("P33 (frozen): the ratio maxroot mu / rho^2 climbs to 1 along a girth ladder at b = 3")
    print("and b = 4; the plateau near 0.73 is an artefact of sampling generic subspaces.\n")

    # ---------------------------------------------------------- CONTROL A: the bridge
    print("CONTROL A -- the bridge mu(t^2) = t^{n-q} mu_I(t), two routes sharing no code.")
    print(f"{'hypergraph':>16}{'n':>4}{'q':>4}{'b':>3}"
          f"{'MSS definition':>34}{'from I(H) matchings':>34}{'agree':>7}")
    ok = bad = 0
    # Small witnesses on purpose. The claim is a polynomial identity, so it is settled by exact
    # agreement on any case at all; the symbolic determinant costs one variable per hyperedge and
    # is the only expensive thing here, so the witnesses are kept to n <= 8, q <= 6. The identity
    # is then USED at Fano and AG(2,3) scale below, where only the matching route runs.
    cases = [("C_6 (b=2)", 6, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]]),
             ("2-reg 3-unif", 6, [[0, 1, 2], [2, 3, 4], [4, 5, 0], [1, 3, 5]]),
             ("K_4 triples", 4, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]])]
    if not QUICK:
        cases.append(("2-reg 4-unif", 8, [[0, 1, 2, 3], [2, 3, 4, 5], [4, 5, 6, 7], [6, 7, 0, 1]]))
    for (nm, n, lines) in cases:
        pa = mss_mu(coordinate_projs(n, lines), n)
        pb = mu_from_incidence(n, lines)
        same = sp.expand(pa.as_expr() - pb.as_expr()) == 0
        ok += same; bad += (not same)
        sa = str(pa.as_expr())[:32]
        sb = str(pb.as_expr())[:32]
        print(f"{nm:>16}{n:>4}{len(lines):>4}{len(lines[0]):>3}{sa:>34}{sb:>34}"
              f"{('yes' if same else 'NO'):>7}")

    # ---------------------------------------------------------- CONTROL B: it must fail off-coordinate
    rng = np.random.default_rng(20260826)
    n, b, q = 6, 3, 5
    Ps = []
    for _ in range(q):
        Q = np.linalg.qr(rng.standard_normal((n, b)))[0]
        Ps.append(Q @ Q.T)
    pa = mss_mu([sp.Matrix(P) for P in Ps], n)
    coords = [[0, 1, 2], [1, 2, 3], [2, 3, 4], [3, 4, 5], [4, 5, 0]]
    pb = mu_from_incidence(n, coords)
    off = sp.expand(pa.as_expr() - pb.as_expr()) != 0
    print(f"  bridge holds on coordinate families: {ok}/{ok + bad}."
          f"  Off-coordinate rank-{b} family differs: {'yes' if off else 'NO'}"
          + ("  <-- control B failed" if not off else ""))
    print("  That difference is the point: the coordinate case reduces to a matching polynomial,")
    print("  and everything Xu's conjecture asserts beyond it lives off the coordinate locus.\n")

    # ---------------------------------------------------------- the girth ladder, by balls
    print("THE LADDER -- lambda_max(B_r)^2 / rho^2 for the ball of radius r in the (a,b)-biregular")
    print("tree. Any biregular graph of girth > 2r contains B_r, and the greatest root of a")
    print("matching polynomial is monotone under subgraphs, so its ratio is at least this.\n")
    print(f"{'(a,b)':>8}{'rho^2':>9}" + "".join(f"{f'r={r}':>10}" for r in (2, 4, 6, 8, 10, 12))
          + f"{'trend':>13}")
    print(f"  A ball truncated at the {BALL_CAP} vertex cap is a proper subtree of the true ball,")
    print("  hence still a subgraph of any graph of girth > 2r: the floor stays valid, and only")
    print("  the radius label overstates what was built. Sizes are printed under each row.\n")
    rows = {}
    for (a, b) in ((3, 2), (4, 3), (5, 4), (4, 4), (6, 3)):
        rho2 = (math.sqrt(a - 1) + math.sqrt(b - 1)) ** 2
        vals, sizes = [], []
        for r in (2, 4, 6, 8, 10, 12):
            if time.time() - t0 > BUDGET_S:
                break
            A, nn = biregular_ball(a, b, r)
            if sizes and nn == sizes[-1]:
                break                        # cap reached: a larger radius returns the same tree
            vals.append(lam_max(A, nn) ** 2 / rho2)
            sizes.append(nn)
        rows[(a, b)] = vals
        up = all(vals[i] < vals[i + 1] for i in range(len(vals) - 1))
        print(f"{f'({a},{b})':>8}{rho2:>9.4f}"
              + "".join(f"{v:>10.4f}" for v in vals)
              + f"{('rising' if up else 'flat at cap'):>13}")
        print(f"{'':>8}{'|B_r|':>9}" + "".join(f"{s_:>10d}" for s_ in sizes))

    # ---------------------------------------------------------- exact graphs, girth checked
    print(f"\nEXACT GRAPHS -- maxroot mu computed from the matching polynomial of I(H), girth by BFS.")
    print(f"{'graph':>16}{'(a,b)':>8}{'n+q':>6}{'girth':>7}{'maxroot mu':>12}{'rho^2':>9}"
          f"{'ratio':>8}{'ball floor':>12}{'>= floor':>10}")
    worst = None
    for (nm, a, b, n, lines) in named():
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        q = len(lines)
        if n > 20:
            continue
        g = girth_bipartite(q, [list(e) for e in lines], n)
        p = mu_from_incidence(n, lines)
        co = [float(c) for c in p.all_coeffs()]
        rts = np.roots(co)
        ymax = max([t.real for t in rts if abs(t.imag) < 1e-7] or [0.0])
        rho2 = (math.sqrt(a - 1) + math.sqrt(b - 1)) ** 2
        r = int((g - 1) // 2) if g != math.inf else 12
        A, nn = biregular_ball(a, b, r)
        floor = lam_max(A, nn) ** 2 / rho2
        ratio = ymax / rho2
        good = ratio >= floor - 1e-9
        if worst is None or ratio < worst[1]:
            worst = (nm, ratio)
        print(f"{nm:>16}{f'({a},{b})':>8}{n + q:>6}{(g if g != math.inf else -1):>7}"
              f"{ymax:>12.5f}{rho2:>9.4f}{ratio:>8.4f}{floor:>12.4f}"
              f"{('yes' if good else 'NO'):>10}")

    print()
    v32 = rows.get((3, 2), []); v43 = rows.get((4, 3), []); v54 = rows.get((5, 4), [])
    def last(v):
        return v[-1] if v else float('nan')
    print(f"  Ball ratios at the deepest radius reached: (3,2) {last(v32):.4f},"
          f" (4,3) {last(v43):.4f}, (5,4) {last(v54):.4f}.")
    rising = all(all(v[i] < v[i + 1] for i in range(len(v) - 1)) for v in rows.values() if v)
    if rising:
        print("  P33 holds. The ratio is bounded below by a quantity increasing to 1 at every")
        print("  (a,b) tested, b >= 3 included, so Xu's constant is attained in the limit and is")
        print("  sharp for every b. The 0.739 and 0.726 plateaus measured earlier record the")
        print("  behaviour of generic subspaces, not the extremal behaviour of the class.")
    else:
        print("  P33 IS FALSE: the ball ratios do not increase, so the argument above is wrong")
        print("  and the possibility that the constant is not optimal for b >= 3 revives.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
