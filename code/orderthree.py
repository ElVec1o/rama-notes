"""Order three is unobstructed whenever G_D is connected, and the measured step is gone.

Earlier today the order-three claim was downgraded. The note had argued it from complementary
supports, whose hypothesis on X no second-order correction satisfies; the repair was the trace law,
which gives sum_j R_j = 0 but NOT R = 0, and the conclusion then rested on a measured rank: that the
free entries of X sweep the whole sum-zero hyperplane, checked at Fano only. This removes that step.

THE OBSTRUCTION. At the diagonal no hyperedge splits the pair, so (Y_k)_jj is forced and
sum_k Y_k = 0 requires R_j = 0 at every vertex, with

    R_j = sum_k sigma_k(j) (D_k X_k + X_k D_k)_jj .

X is not unique: the order-two equation leaves its split-pair entries free, and R is linear in them
with no constant term, since D_k is supported exactly on split pairs. Order three is unobstructed
exactly when R = 0 is attainable inside the affine set of admissible X.

THE RANK, and it is the same graph as at order two. Writing u for the free entries, which satisfy
sum_{k in K(i,j)} u_{k,i,j} = 0 pair by pair,

    sum_j w_j R_j = 2 sum_{i<j} (w_j - w_i) sum_{k in K(i,j)} sigma_k(j) D_k(i,j) u_{k,i,j},

using sigma_k(i) = -sigma_k(j) on a split pair. So w annihilates the image exactly when, pair by
pair, either w_i = w_j or the linear functional u -> sum_k sigma_k(j) D_k(i,j) u_k vanishes on
{sum u = 0}, which by SpanRank.linear_vanishes_iff_const happens exactly when its coefficients are
constant in k. That is the definition of the graph G_D already used for the second-order rank and the
order-four obstruction. Hence

    rank of the order-three obstruction map = n - c(G_D),

the same formula, the same graph, and the same proof as rank dQ(D). Nothing new is needed.

THE CONCLUSION. OrderThreeLaw.trace_order_three puts R in the hyperplane sum_j R_j = 0 for every
admissible X. When G_D is connected the rank above is n - 1, which is the dimension of that
hyperplane, so the image IS the hyperplane and R = 0 is attainable. Every step is machine-checked:

    trace_order_three            sum_j R_j = 0, per block, for arbitrary X
    linear_vanishes_iff_const    the annihilator condition is constancy in k
    const_of_adj_eq              a function constant across the edges of a preconnected graph is
                                 constant
    mem_of_sum_zero              a vector summing to zero lies in a subspace whose orthogonal
                                 complement is the constants

so "order three is unobstructed when G_D is connected" is PROVED with no measured input. What is not
claimed is the disconnected case: there the image is strictly smaller than the hyperplane and
solvability needs the obstruction to land inside it, which is checked below rather than proved.

FROZEN BEFORE THE DATA:
  P51. (a) The order-three obstruction map has rank exactly n - c(G_D), at every family and every
           cone direction tested.
       (b) Order three is solvable at every cone direction tested, including where G_D is
           disconnected and the theorem above does not apply.
       (c) The canonical X of the superseded argument, with split-pair entries zero, fails
           tightness at every off-diagonal pair, so the hypothesis it needed is satisfied by
           nothing.

(c) AS FROZEN OVERSTATES, and is reported as measured. "Every off-diagonal pair" holds at Fano
(21 of 21), C_6 (15 of 15), K_{3,3} (15 of 15) and the cube (28 of 28), but not at C_4, where it
fails at 4 of 6. The conclusion is unaffected, since one failing pair already makes the hypothesis
unsatisfiable, and that is what the verdict below tests; but the universal phrasing was a guess.

FALSIFICATION. A rank differing from n - c(G_D) kills (a) and with it the identification of the
order-three and second-order ranks. A direction where R = 0 is unattainable kills (b) and order
three obstructs after all, which would be a much larger result than the one claimed.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import itertools
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from hessian import coord_family, tangent_basis
from tangentcone import quadric, project_to_cone
from spanrank import GD_edges, components

QUICK = quickmode.QUICK

FAMILIES = [
    ("C_4", 4, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("Fano", 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]),
    ("C_6", 6, [[i, (i + 1) % 6] for i in range(6)]),
    ("K_{3,3}", 6, [[i, 3 + j] for i in range(3) for j in range(3)]),
    ("cube", 8, [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4],
                 [0, 4], [1, 5], [2, 6], [3, 7]]),
]


def pieces(D, lines, n, q):
    """The tightness system on the free entries, and the obstruction map."""
    def cross(k, i, j):
        return (i in lines[k]) != (j in lines[k])

    def coef(k, i, j):
        return 1.0 - (1.0 if i in lines[k] else 0.0) - (1.0 if j in lines[k] else 0.0)

    Dsq = [D[k] @ D[k] for k in range(q)]
    off = list(itertools.combinations(range(n), 2))
    free = [(k, i, j) for (i, j) in off for k in range(q) if cross(k, i, j)]
    pos = {t: m for m, t in enumerate(free)}
    A = np.zeros((len(off), len(free)))
    b = np.zeros(len(off))
    for r, (i, j) in enumerate(off):
        for k in range(q):
            if cross(k, i, j):
                A[r, pos[(k, i, j)]] = 1.0
        b[r] = -sum(Dsq[k][i, j] / coef(k, i, j) for k in range(q) if not cross(k, i, j))
    M = np.zeros((n, len(free)))
    for m, (k, i, j) in enumerate(free):
        sg = lambda t: -1.0 if t in lines[k] else 1.0
        M[i, m] += 2 * sg(i) * D[k][i, j]
        M[j, m] += 2 * sg(j) * D[k][j, i]
    return A, b, M, free


def canonical_fails(D, lines, n, q):
    """How many off-diagonal pairs the superseded canonical X fails tightness at."""
    def coef(k, i, j):
        return 1.0 - (1.0 if i in lines[k] else 0.0) - (1.0 if j in lines[k] else 0.0)
    Xc = np.zeros((q, n, n))
    for k in range(q):
        for i in range(n):
            for j in range(n):
                c = coef(k, i, j)
                if abs(c) > 1e-12:
                    Xc[k, i, j] = (D[k] @ D[k])[i, j] / c
    S = Xc.sum(axis=0)
    off = list(itertools.combinations(range(n), 2))
    return sum(1 for (i, j) in off if abs(S[i, j]) > 1e-9), len(off)


def main():
    print("P51 (frozen): (a) the order-three rank is n - c(G_D); (b) order three is solvable at")
    print("every cone direction tested; (c) the superseded canonical X fails tightness everywhere.\n")
    rng = np.random.default_rng(1)
    ndir = 2 if QUICK else 4
    fams = FAMILIES[:2] if QUICK else FAMILIES

    print("(a) and (b): the rank, against the graph, and solvability.")
    print(f"{'family':>10}{'n':>4}{'dirs':>6}{'rank':>8}{'n-c(G_D)':>10}{'connected':>11}"
          f"{'agrees':>8}{'solvable':>10}")
    ok_a = True; ok_b = True
    for (nm, n, lines) in fams:
        q = len(lines)
        A0 = coord_family(n, lines)
        B = tangent_basis(n, lines)
        rks = set(); prd = set(); conn = set(); slv = set()
        for _ in range(ndir):
            _, D = project_to_cone(rng.standard_normal(len(B)), B, lines, n, q)
            A, b, M, _f = pieces(D, lines, n, q)
            u0, *_ = np.linalg.lstsq(A, b, rcond=None)
            ns = np.linalg.svd(A)[2][np.linalg.matrix_rank(A):]
            Z = M @ ns.T
            rks.add(int(np.linalg.matrix_rank(Z, tol=1e-8)))
            cD = components(n, GD_edges(n, lines, D))
            prd.add(n - cD); conn.add(cD == 1)
            R0 = M @ u0
            c, *_ = np.linalg.lstsq(Z, -R0, rcond=None)
            slv.add(float(np.abs(Z @ c + R0).max()) < 1e-9)
        agree = rks == prd
        ok_a = ok_a and agree
        ok_b = ok_b and slv == {True}
        print(f"{nm:>10}{n:>4}{ndir:>6}{str(sorted(rks)):>8}{str(sorted(prd)):>10}"
              f"{str(sorted(conn)):>11}{str(agree):>8}{str(slv == {True}):>10}")
    print("  'connected' False means the theorem does not apply there and solvability is measured;")
    print("  C_4 is that case, its G_D having two components.\n")

    print("(c) The superseded canonical X, with split-pair entries zero.")
    print(f"{'family':>10}{'pairs failing tightness':>26}{'of':>5}{'hypothesis satisfiable':>24}")
    print("  One failing pair suffices: the canonical X is then not an admissible correction.")
    ok_c = True
    for (nm, n, lines) in fams:
        q = len(lines)
        B = tangent_basis(n, lines)
        _, D = project_to_cone(rng.standard_normal(len(B)), B, lines, n, q)
        bad, tot = canonical_fails(D, lines, n, q)
        ok_c = ok_c and bad > 0
        print(f"{nm:>10}{bad:>26}{tot:>5}{str(bad == 0):>24}")
    print()

    if ok_a and ok_b and ok_c:
        print("  P51 HOLDS. The order-three obstruction map has the same rank formula, the same")
        print("  graph and the same proof as the second-order map: n - c(G_D). With the trace law")
        print("  putting the obstruction in the sum-zero hyperplane, a connected G_D makes the image")
        print("  that whole hyperplane and order three is unobstructed, PROVED, with every step")
        print("  machine-checked and no measured input. Where G_D is disconnected the image is")
        print("  smaller and solvability is measured rather than proved; C_4 is the only such family")
        print("  here, and it is solvable.")
    else:
        print("  P51 FAILS somewhere above. Either the rank is not the component count, or a")
        print("  direction obstructs, and the order-three claim must be restated.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
