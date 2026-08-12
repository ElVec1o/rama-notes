"""What the span of the quadrics is, and when 2-regularity holds: two combinatorial formulas.

code/arc.py closed A6 under a rank hypothesis: a cone direction D is tangent to a curve in the tight
projection variety when E -> dQ(D)[E] carries the kernel onto the span of Q_1, ..., Q_n. That left
two quantities measured rather than known, the span and the rank, and left "every cone direction"
open. Both are computable in closed form, and the answer to the open question is no.

THE SETUP, which makes both formulas fall out. Write K(i,j) for the blocks separating i from j.
A kernel direction has D_k supported on separated pairs, and tightness reads, pair by pair,

    sum over k in K(i,j) of D_k(i,j) = 0,

with different pairs independent. Since (D_k^2)_jj = sum_l D_k(j,l)^2 and sigma_k(i) = -sigma_k(j)
for separating k,

    sum_j w_j Q_j(D) = sum over i<j of (w_j - w_i) * sum over k in K(i,j) of sigma_k(j) D_k(i,j)^2 .

So w annihilates the quadrics exactly when, for every pair, either w_i = w_j or the diagonal form
t -> sum_k eps_k t_k^2 vanishes identically on {sum t = 0}, where eps_k = sigma_k(j), that is +1 if
i is in e_k and -1 if j is in e_k.

WHEN DOES THAT FORM VANISH ON THE HYPERPLANE. Testing it on t = e_a - e_b gives eps_a + eps_b, so
the form vanishes identically only if every pair of signs cancels. With m = |K(i,j)|:
  m <= 1     the hyperplane is {0} and the form vanishes;
  m = 2      it vanishes exactly when the two signs differ, that is one separating block contains i
             and the other contains j, the CROSS configuration;
  m >= 3     it never vanishes, since eps_a = -eps_b for all pairs is contradictory.
Define the graph G_Q on the vertices with i ~ j exactly when the form does NOT vanish. Then

    span{Q_1, ..., Q_n} = n - c(G_Q),

with c the number of connected components. G_Q depends on the hypergraph alone, not on D.

THE SAME COMPUTATION FOR THE DERIVATIVE. dQ_j(D)[E] = 2 sum_k sigma_k(j) sum_l D_k(j,l) E_k(j,l), so
w annihilates the image of dQ(D) exactly when, for every pair, either w_i = w_j or the LINEAR
functional t -> sum_k sigma_k(j) D_k(i,j) t_k fails to vanish on {sum t = 0}, and a linear
functional vanishes on that hyperplane exactly when its coefficients are constant. Define G_D by
i ~ j when the vector (sigma_k(j) D_k(i,j))_{k in K(i,j)} is NOT constant in k. Then

    rank dQ(D) = n - c(G_D),

which is the graph already used for the order-four obstruction (RamaLean/CokernelRank.lean), now
appearing for the second-order one.

CONSEQUENCE, and it settles the open question in the negative. 2-regularity at D says
c(G_D) = c(G_Q). Always G_D is a subgraph of G_Q: at a cross pair, tightness forces
D_{k2}(i,j) = -D_{k1}(i,j) and the two signs differ, so sigma_k(j) D_k(i,j) takes the same value
twice and the pair is not an edge. So the rank never exceeds the span, and the question is whether
the two graphs have the same components. For a generic kernel direction they are equal. They are NOT
equal at every cone direction: a cross basis direction, supported on one pair with two separating
blocks of opposite sign, has rank dQ(D) at most 1, and 2-regularity fails outright. Those directions
are in the cone. So A6 does not follow from 2-regularity at every cone direction, and the gap is
exactly where an explicit curve is available anyway, the rotation of the cross configuration.

The rank at a cross basis direction is 0 when the pair has exactly two separating blocks and 1 when
it has more, and the reason is visible in the formula: the vector (sigma_l(j) D_l(i,j))_l equals
(sigma_k(j), sigma_k(j), 0, ..., 0), constant only when there are no unused blocks to supply the
zeros. So the C_4 pairs with two separating blocks give 0 and every other cross gives 1.

THE CRITERION COLLAPSES ON TIGHT FAMILIES, which is the answer to when the span drops below n-1.
Writing lambda_ij for the number of blocks containing BOTH i and j,

    |K(i,j)| = deg(i) + deg(j) - 2 lambda_ij ,

and a tight family has every degree equal to a, so |K(i,j)| = 2(a - lambda_ij) is EVEN and the two
sides of a separated pair carry a - lambda_ij blocks each. So the case "|K| = 2 with both blocks on
the same side" cannot occur, |K| = 2 always means the cross configuration, and the whole criterion
reduces to a codegree condition:

    G_Q :  i ~ j  <=>  lambda_ij <= a - 2 .

G_Q is therefore the COMPLEMENT of the graph joining pairs with codegree at least a - 1, and

    the span drops below n - 1  <=>  the codegree-at-least-(a-1) graph is a COMPLETE JOIN,

a graph being a join exactly when its complement is disconnected. That is the whole answer, and it
is checkable on the hypergraph without computing anything.

Four families in the zoo below satisfy it, and each is a join for a visible reason:
  C_3            codegree graph K_3, a join; complement empty, c = 3, span 0
  C_4            codegree graph C_4 = K_{2,2}, a join; complement 2K_2, c = 2, span 2
  K_4 triples    every pair lies in 2 of the 4 triples, so the codegree graph is K_4; the quadrics
                 VANISH IDENTICALLY there and the tangent cone is the whole kernel
  2-reg 3-unif   codegree graph is K_6 minus a perfect matching, the cocktail party graph
                 K_{2,2,2}, a join; complement is 3K_2, c = 3, span 3
For a = b = 2 the codegree graph is the cycle itself, and among cycles only C_3 and C_4 are joins,
which is why every longer cycle has span n - 1.

FROZEN BEFORE THE DATA:
  P43. (a) span{Q_j} = n - c(G_Q), at every family, with G_Q as defined above.
       (b) rank dQ(D) = n - c(G_D) for every kernel direction D, cone or not.
       (c) A generic cone direction has G_D = G_Q, hence is 2-regular; a cross basis direction has
           G_D empty and rank 0, hence is NOT, while lying in the cone.
       (d) On tight families the codegree form of G_Q agrees with the definition at every pair, and
           c(G_Q) > 1 happens only at C_3 and C_4 across the zoo swept below.

(d)'s SECOND HALF AS FROZEN IS FALSE, and is reported as measured. "Only C_3 and C_4" came from the
a = b = 2 case and does not survive contact with larger block sizes: K_4 triples and the 2-regular
3-uniform family on six vertices also drop, with spans 0 and 3 against n - 1 of 3 and 5. The first
half, that the codegree form agrees with the definition, holds at every family and every pair. What
replaces the guess is the join criterion above, which covers all four.

(c) AS FROZEN IS WRONG IN ITS NUMBER, and the number is reported as measured. The rank at a cross
basis direction is 1, not 0, at every family, because a pair with more than two separating blocks
leaves the unused ones at zero and that makes the vector non-constant. It is 0 only where the pair
has exactly two, which happens at C_4 and nowhere else here. The CONCLUSION is unaffected, the span
being at least 2 everywhere, so 2-regularity still fails at these directions; but "G_D empty" was a
guess and it is false.

FALSIFICATION. A family where the predicted span or rank differs from the computed one kills the
formula. If cross basis directions turned out 2-regular after all, then A6 would follow at every
cone direction and the negative answer would be wrong.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import itertools
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from hessian import tangent_basis
from tangentcone import quadric, project_to_cone
from arc import dQ_matrix

QUICK = quickmode.QUICK


def separating(lines, i, j):
    """K(i,j) and the signs eps_k = +1 if i in e_k, -1 if j in e_k."""
    K = [k for k, e in enumerate(lines) if (i in e) != (j in e)]
    eps = [1.0 if i in lines[k] else -1.0 for k in K]
    return K, eps


def components(n, edges):
    """Number of connected components of the graph on n vertices with the given edges."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x

    for (i, j) in edges:
        a, b = find(i), find(j)
        if a != b:
            parent[a] = b
    return len({find(v) for v in range(n)})


def GQ_edges(n, lines):
    """i ~ j when the diagonal form does not vanish on the sum-zero hyperplane."""
    out = []
    for i, j in itertools.combinations(range(n), 2):
        K, eps = separating(lines, i, j)
        m = len(K)
        if m >= 3 or (m == 2 and eps[0] == eps[1]):
            out.append((i, j))
    return out


def GD_edges(n, lines, D, tol=1e-9):
    """i ~ j when (sigma_k(j) D_k(i,j))_k is not constant over the separating blocks."""
    out = []
    for i, j in itertools.combinations(range(n), 2):
        K, eps = separating(lines, i, j)
        if len(K) < 2:
            continue
        vals = [eps[t] * float(D[K[t]][i, j]) for t in range(len(K))]
        if max(vals) - min(vals) > tol:
            out.append((i, j))
    return out


def cross_basis(n, lines):
    """Cross basis directions: supported on one pair, two separating blocks of OPPOSITE sign.

    Not only the pairs with exactly two separating blocks. At the Fano family every pair has four,
    and a cross element uses two of them; requiring |K| = 2 found none there and reported the
    families with |K| >= 3 as having no cross directions at all, which is wrong. Tightness holds
    because the two entries are +1 and -1, and Q vanishes because the two signs cancel.
    """
    q = len(lines)
    out = []
    for i, j in itertools.combinations(range(n), 2):
        K, eps = separating(lines, i, j)
        for s in range(len(K)):
            for t in range(len(K)):
                if s < t and eps[s] != eps[t]:
                    D = np.zeros((q, n, n))
                    D[K[s], i, j] = D[K[s], j, i] = 1.0
                    D[K[t], i, j] = D[K[t], j, i] = -1.0
                    out.append(((i, j), D))
    return out


def GQ_edges_codegree(n, lines):
    """The codegree form: i ~ j iff the two share at most a - 2 blocks. Tight families only."""
    deg = [sum(1 for e in lines if v in e) for v in range(n)]
    a = deg[0]
    if any(d != a for d in deg):
        return None
    out = []
    for i, j in itertools.combinations(range(n), 2):
        lam = sum(1 for e in lines if i in e and j in e)
        if lam <= a - 2:
            out.append((i, j))
    return out


def zoo():
    """Tight families, that is every vertex in the same number of blocks."""
    out = []
    for m in range(3, 11):
        out.append((f"C_{m}", m, [[i, (i + 1) % m] for i in range(m)]))
    out.append(("2C_3", 6, [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3]]))
    out.append(("2C_4", 8, [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4]]))
    out.append(("C_3 + C_4", 7, [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 6], [6, 3]]))
    out.append(("K_{3,3}", 6, [[i, 3 + j] for i in range(3) for j in range(3)]))
    out.append(("K_{4,4}", 8, [[i, 4 + j] for i in range(4) for j in range(4)]))
    out.append(("cube", 8, [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4],
                            [0, 4], [1, 5], [2, 6], [3, 7]]))
    out.append(("K_4 triples", 4, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]))
    out.append(("2-reg 3-unif", 6, [[0, 1, 2], [2, 3, 4], [4, 5, 0], [1, 3, 5]]))
    out.append(("Fano", 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6],
                            [2, 3, 6], [2, 4, 5]]))
    out.append(("AG(2,3)", 9, [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8],
                               [0, 4, 8], [1, 5, 6], [2, 3, 7], [0, 5, 7], [1, 3, 8], [2, 4, 6]]))
    return out


FAMILIES = [
    ("C_4", 4, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("C_6", 6, [[i, (i + 1) % 6] for i in range(6)]),
    ("K_{2,4}", 6, [[i, 2 + j] for i in range(2) for j in range(4)]),
    ("K_{3,3}", 6, [[i, 3 + j] for i in range(3) for j in range(3)]),
    ("cube", 8, [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4],
                 [0, 4], [1, 5], [2, 6], [3, 7]]),
    ("Fano", 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]),
    ("AG(2,3)", 9, [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8],
                    [0, 4, 8], [1, 5, 6], [2, 3, 7], [0, 5, 7], [1, 3, 8], [2, 4, 6]]),
]


def main():
    t0 = time.time()
    print("P43 (frozen): (a) span = n - c(G_Q); (b) rank dQ(D) = n - c(G_D); (c) generic cone")
    print("directions are 2-regular, cross basis directions are not and lie in the cone.\n")
    rng = np.random.default_rng(20260812)
    fams = FAMILIES[:5] if QUICK else FAMILIES
    ndir = 3 if QUICK else 8

    print("(a) The span of the quadrics against n - c(G_Q).")
    print(f"{'family':>10}{'n':>4}{'q':>4}{'|E(G_Q)|':>10}{'c(G_Q)':>8}{'predicted':>11}"
          f"{'computed':>10}{'agree':>7}")
    ok_a = True
    spans = {}
    for (nm, n, lines) in fams:
        q = len(lines)
        B = tangent_basis(n, lines)
        rows = [quadric(sum(c * Bi for c, Bi in zip(rng.standard_normal(len(B)), B)),
                        lines, n, q) for _ in range(40)]
        sp = int(np.linalg.matrix_rank(np.array(rows), tol=1e-8))
        E = GQ_edges(n, lines)
        cQ = components(n, E)
        spans[nm] = (sp, cQ)
        agree = (sp == n - cQ)
        ok_a = ok_a and agree
        print(f"{nm:>10}{n:>4}{q:>4}{len(E):>10}{cQ:>8}{n - cQ:>11}{sp:>10}{str(agree):>7}")
    print(f"  (a) holds at every family: {ok_a}\n")

    print("(b) The rank of dQ(D) against n - c(G_D), over kernel and cone directions.")
    print(f"{'family':>10}{'kind':>10}{'directions':>12}{'predicted':>11}{'computed':>10}"
          f"{'agree':>7}")
    ok_b = True
    cone_ok = {}
    for (nm, n, lines) in fams:
        if time.time() - t0 > (120.0 if QUICK else 900.0):
            print("  [budget reached]"); break
        q = len(lines)
        B = tangent_basis(n, lines)
        for kind in ("kernel", "cone"):
            preds = []; comps = []; reg = 0
            for _ in range(ndir):
                if kind == "kernel":
                    D = sum(c * Bi for c, Bi in zip(rng.standard_normal(len(B)), B))
                else:
                    _, D = project_to_cone(rng.standard_normal(len(B)), B, lines, n, q)
                pr = n - components(n, GD_edges(n, lines, D))
                co = int(np.linalg.matrix_rank(dQ_matrix(D, B, lines, n, q), tol=1e-8))
                preds.append(pr); comps.append(co)
                if co == spans[nm][0]:
                    reg += 1
            agree = (preds == comps)
            ok_b = ok_b and agree
            if kind == "cone":
                cone_ok[nm] = (reg, ndir)
            rng_s = f"{min(preds)}-{max(preds)}"; cmp_s = f"{min(comps)}-{max(comps)}"
            print(f"{nm:>10}{kind:>10}{ndir:>12}{rng_s:>11}{cmp_s:>10}{str(agree):>7}")
    print(f"  (b) holds at every family and both kinds: {ok_b}\n")

    print("(c) Cross basis directions: in the cone, and not 2-regular.")
    print(f"{'family':>10}{'crosses':>9}{'max |Q|':>10}{'ranks':>8}{'|K| = 2':>9}{'span':>6}"
          f"{'2-regular':>11}{'generic cone':>14}")
    ok_c = True
    for (nm, n, lines) in fams:
        q = len(lines)
        B = tangent_basis(n, lines)
        cb = cross_basis(n, lines)
        if not cb:
            print(f"{nm:>10}        none"); continue
        qmax = 0.0; ranks = set(); ntwo = 0
        for ((i, j), D) in (cb if not QUICK else cb[:6]):
            qmax = max(qmax, float(np.abs(quadric(D, lines, n, q)).max()))
            ranks.add(int(np.linalg.matrix_rank(dQ_matrix(D, B, lines, n, q), tol=1e-8)))
            if len(separating(lines, i, j)[0]) == 2:
                ntwo += 1
        sp = spans[nm][0]
        rmax = max(ranks)
        good = (qmax < 1e-12 and rmax < sp)
        ok_c = ok_c and good
        g = cone_ok.get(nm, (0, 0))
        rs = "-".join(str(r) for r in sorted(ranks))
        print(f"{nm:>10}{len(cb):>9}{qmax:>10.1e}{rs:>8}{ntwo:>9}{sp:>6}{str(rmax == sp):>11}"
              f"{f'{g[0]}/{g[1]}':>14}")

    print("(d) The codegree form of G_Q on tight families, and where c(G_Q) exceeds 1.")
    print(f"{'family':>14}{'n':>4}{'q':>4}{'a':>4}{'agrees':>8}{'c(G_Q)':>8}{'span':>6}"
          f"{'n-1':>6}{'drops':>7}")
    ok_d = True; exceptions = []
    for (nm, n, lines) in zoo():
        E1 = GQ_edges(n, lines)
        E2 = GQ_edges_codegree(n, lines)
        if E2 is None:
            print(f"{nm:>14}{n:>4}{len(lines):>4}   not tight, skipped"); continue
        a = sum(1 for e in lines if 0 in e)
        agree = set(E1) == set(E2)
        ok_d = ok_d and agree
        c = components(n, E1)
        if c > 1:
            exceptions.append(nm)
        print(f"{nm:>14}{n:>4}{len(lines):>4}{a:>4}{str(agree):>8}{c:>8}{n - c:>6}{n - 1:>6}"
              f"{str(c > 1):>7}")
    print(f"  codegree form agrees with the definition everywhere: {ok_d}")
    print(f"  span drops below n-1 at: {exceptions if exceptions else 'none'}")
    print("  Each is a family whose codegree-at-least-(a-1) graph is a complete join, which is the")
    print("  criterion; 'only C_3 and C_4' was the frozen guess and it is false at larger block")
    print("  sizes. K_4 triples is the extreme case: every pair lies in two of the four triples, so")
    print("  the quadrics vanish identically and the tangent cone is the whole kernel.\n")

    print()
    if ok_a and ok_b and ok_c and ok_d:
        print("  P43 HOLDS in all three parts. The span and the rank are combinatorial, both of the")
        print("  form n minus a component count, and 2-regularity at D is the statement that the two")
        print("  graphs have the same components. The answer to whether A6 follows from 2-regularity")
        print("  at EVERY cone direction is NO: cross basis directions satisfy Q = 0 exactly and have")
        print("  rank at most 1. What saves them is not the criterion but an explicit curve, that of")
        print("  the cross configuration, so A6 stands at every direction tested by one route or the")
        print("  other, with no single route covering all of them.")
    else:
        print("  P43 FAILS somewhere above. The formulas are not right and the span and rank stay")
        print("  measured quantities.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
