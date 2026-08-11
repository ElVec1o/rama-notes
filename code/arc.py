"""From all finite orders to an actual curve: A6 by 2-regularity.

The tangent cone at a commuting tight family was characterised as ker(dPhi) cut by the n quadrics
Q_j(D) = sum_k sigma_k(j) (D_k^2)_jj. That Q(D) != 0 obstructs is proved. That Q(D) = 0 suffices was
proved only ORDER BY ORDER: orders two, three and four are all solvable, and the passage from every
finite order to a curve was the gap, labelled A6 and HEURISTIC.

This closes it, and the tool is classical rather than new. What was missing was the right frame.

THE FRAME. Work upstairs, on U_k in R^{n x b} with U_k^T U_k = I_b and A_k = U_k U_k^T. Idempotency
is then free and the only equation is

    Psi(U) = sum_k U_k U_k^T - a I = 0.

Two facts about Psi at the coordinate point, both recorded earlier:

  (i) the diagonal of dPsi vanishes identically on the Stiefel tangent space, because the Stiefel
      constraint makes the e_k-block of V_k antisymmetric and a diagonal entry of the differential
      is a diagonal entry of that block;
  (ii) dPsi is onto the zero-diagonal symmetric matrices (rank 21 of 28 at the Fano family).

So split Psi into its off-diagonal and diagonal parts. The off-diagonal part is a submersion, so
W = {Psi_off = 0} is a smooth manifold near the point; and on W the remaining map F = Psi_diag has
F = 0 and dF = 0 at the point, with Hessian exactly Q. The variety near the commuting family is
therefore the zero set of a map with vanishing differential whose Hessian is Q, which is the
situation 2-regularity was invented for.

THE LEMMA, in the fully degenerate case, with a three-line proof. Let F be polynomial with F(0) = 0
and F'(0) = 0, write F = Q + (higher), Q(x) = B(x,x). Let Q(D) = 0 and suppose E -> B(D,E) is onto.
Then F(tD + t^2 w) = t^3 G(t,w) with G polynomial, G(0,w) = 2B(D,w) + C(D,D,D) affine in w with
onto linear part; pick w_0 with G(0,w_0) = 0 and apply the implicit function theorem in w. The
resulting x(t) = tD + t^2 w(t) satisfies F(x(t)) = 0 and x(t)/t -> D. This is Avakov's 2-regularity
condition (Avakov 1985; Arutyunov, Optimality Conditions, 2000, ch. 2); no novelty is claimed for
it, only for the observation that the tight projection variety is in its scope.

THE RANK CONDITION, and what it is measured against. The n quadrics are never independent: summing
Q_j over j gives sum_k [tr((D_k^2)_22) - tr((D_k^2)_11)], and with D_k off-diagonal with corner M_k
those two blocks are M_k^T M_k and M_k M_k^T, of equal trace. So

    sum_j Q_j(D) = 0 identically,

and Q maps into the trace-zero diagonals. Surjectivity must therefore be asked onto the span of the
Q_j and not onto R^n, and the span can be smaller still: at C_4 there are two relations,
Q_0 + Q_2 = Q_1 + Q_3 = 0, one for each side of its bipartition, and the span is 2. A first version
of this script compared the rank against n-1 for every family and reported C_4 as failing when it
is 2-regular against its own image. The condition is

    rank of E -> dQ(D)[E] on ker(dPhi)  =  dim span{Q_1, ..., Q_n},

which is the hypothesis the implicit function theorem actually needs and is checkable on D alone.

FROZEN BEFORE THE DATA:
  P42. (a) sum_j Q_j(D) = 0 for every cross-supported D, kernel or not.
       (b) At a cone direction D the map E -> dQ(D)[E] on ker(dPhi) has rank exactly n-1, so
           2-regularity holds and D is tangent to a curve in the variety.
       (c) The curve exists in fact and not only in principle: continuation upstairs from the
           second-order jet stays on the variety to machine precision, and (A(t) - P)/t approaches
           D with error O(t) rather than O(1).

(b) AS FROZEN IS FALSE, and is reported here as revised rather than as predicted. C_4 gives rank 2
against n-1 = 3 at every direction tested, and the curve exists there all the same. The reason is
the extra pair of relations above, which the frozen form did not anticipate: n-1 counts only the
all-ones relation. Against the span the rank is full at C_4 too, and that is the form the implicit
function theorem needs, so the revision is a correction of the statement and not a rescue of it.
Read (b) below as tested and (a), (c) as predicted.

FALSIFICATION. A rank below the span dimension at generic cone directions would make the criterion
vacuous and leave A6 where it was. A continuation that leaves the variety, or whose tangent error
does not fall linearly, refutes (c). A direction with Q(D) != 0 must fail, and is run as a control;
if it succeeded the whole second-order obstruction would be an artefact.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import itertools
import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from hessian import coord_family, tangent_basis
from tangentcone import quadric, project_to_cone

QUICK = quickmode.QUICK
BUDGET_S = 60.0 if QUICK else 600.0


def frames(n, lines, b):
    """The coordinate frames U_k^0: the b columns of I indexed by the hyperedge."""
    U = np.zeros((len(lines), n, b))
    for k, e in enumerate(lines):
        for s, v in enumerate(sorted(e)):
            U[k, v, s] = 1.0
    return U


def dQ_matrix(D, B, lines, n, q):
    """The n x len(B) matrix of E -> (sum_k sigma_k(j) (D_k E_k + E_k D_k)_jj)_j."""
    M = np.zeros((n, len(B)))
    for m, E in enumerate(B):
        for j in range(n):
            M[j, m] = sum((-1.0 if j in lines[k] else 1.0)
                          * float((D[k] @ E[k] + E[k] @ D[k])[j, j]) for k in range(q))
    return M


def solve_at(t, seed, U0, P, D, lines, n, q, a, b):
    """A point of the variety upstairs whose displacement has component exactly t along D.

    The variety is positive-dimensional, so the equations alone do not select a point: without the
    last row the solver returns whatever it was seeded with and the curve never moves. The pin is
    the parametrisation the lemma uses, x(t) = tD + t^2 w with w orthogonal to D, written as an
    equation on the displacement rather than imposed on the correction.
    """
    iu = np.triu_indices(n)
    ib = np.triu_indices(b)
    nD = float(np.sum(D * D))

    def eqs(x):
        U = x.reshape(q, n, b)
        A = np.einsum('kis,kjs->kij', U, U)
        out = [(U[k].T @ U[k] - np.eye(b))[ib] for k in range(q)]
        out.append((A.sum(axis=0) - a * np.eye(n))[iu])
        out.append(np.array([float(np.sum((A - P) * D)) - t * nD]))
        return np.concatenate(out)

    sol = least_squares(eqs, seed.ravel(), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=800)
    U = sol.x.reshape(q, n, b)
    return U, float(np.abs(eqs(sol.x)).max())


def arc(D, U0, lines, n, q, a, b, ts):
    """Continuation in t from the first-order jet upstairs. Returns (t, residual, tangent error).

    Predictor: the previous solution rescaled toward the base point, which is exact for the linear
    part and so keeps the solver inside its basin as t shrinks.
    """
    V = np.stack([D[k] @ U0[k] for k in range(q)])
    out = []
    P = coord_family(n, lines)
    prev = None; tprev = None
    for t in ts:
        seed = U0 + t * V if prev is None else U0 + (t / tprev) * (prev - U0)
        U, res = solve_at(t, seed, U0, P, D, lines, n, q, a, b)
        A = np.einsum('kis,kjs->kij', U, U)
        err = float(np.linalg.norm((A - P) / t - D))
        out.append((t, res, err))
        prev = U; tprev = t
    return out


def exponent_of(rows):
    """err ~ c t^alpha, read off by least squares on the log-log slope."""
    ts = np.array([r[0] for r in rows]); es = np.array([r[2] for r in rows])
    ok = es > 1e-13
    if ok.sum() < 2:
        return float('nan')
    return float(np.polyfit(np.log(ts[ok]), np.log(es[ok]), 1)[0])


FAMILIES = [
    ("C_4", 4, [[0, 1], [1, 2], [2, 3], [3, 0]], 2, 2),
    ("K_{3,3}", 6, [[i, 3 + j] for i in range(3) for j in range(3)], 3, 2),
    ("Fano", 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5],
                 [1, 4, 6], [2, 3, 6], [2, 4, 5]], 3, 3),
]


def main():
    t0 = time.time()
    print("P42: (a) sum_j Q_j = 0 identically, frozen; (b) dQ(D) onto the span of the quadrics at")
    print("cone directions, REVISED after C_4 falsified the frozen form 'rank n-1'; (c) the curve")
    print("exists, with tangent error O(t), frozen.\n")
    rng = np.random.default_rng(20260812)

    print("(a) The identity sum_j Q_j(D) = 0, and the span of the quadrics.")
    print(f"{'family':>10}{'n':>4}{'q':>4}{'directions':>12}{'max |sum_j Q_j|':>18}"
          f"{'max |Q|':>12}{'span':>7}{'n-1':>6}")
    worst_id = 0.0
    spans = {}
    for (nm, n, lines, a, b) in FAMILIES:
        q = len(lines)
        B = tangent_basis(n, lines)
        m = 20 if QUICK else 60
        wid = 0.0; wq = 0.0; rows = []
        for _ in range(m):
            D = sum(c * Bi for c, Bi in zip(rng.standard_normal(len(B)), B))
            Q = quadric(D, lines, n, q)
            rows.append(Q)
            wid = max(wid, abs(float(Q.sum()))); wq = max(wq, float(np.abs(Q).max()))
        sp = int(np.linalg.matrix_rank(np.array(rows), tol=1e-8))
        spans[nm] = sp
        worst_id = max(worst_id, wid)
        print(f"{nm:>10}{n:>4}{q:>4}{m:>12}{wid:>18.2e}{wq:>12.4f}{sp:>7}{n - 1:>6}")
    print(f"  worst: {worst_id:.2e}. The all-ones relation is universal; C_4 carries a second pair,")
    print("  Q_0 + Q_2 = Q_1 + Q_3 = 0, one per side of its bipartition. Surjectivity is asked")
    print("  against the span, not against n-1.\n")

    print("(b) 2-regularity at cone directions: rank of E -> dQ(D)[E] on ker(dPhi).")
    print(f"{'family':>10}{'n':>4}{'dim ker':>9}{'max |Q(D)|':>12}{'ranks seen':>14}{'span':>7}"
          f"{'2-regular':>12}")
    cone_dirs = {}
    ndir = 4 if QUICK else 10
    allreg = True
    for (nm, n, lines, a, b) in FAMILIES:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]"); break
        q = len(lines)
        B = tangent_basis(n, lines)
        sp = spans[nm]
        ranks = []; qn = 0.0; pick = None
        for _ in range(ndir):
            _, D = project_to_cone(rng.standard_normal(len(B)), B, lines, n, q)
            qn = max(qn, float(np.abs(quadric(D, lines, n, q)).max()))
            r = int(np.linalg.matrix_rank(dQ_matrix(D, B, lines, n, q), tol=1e-8))
            ranks.append(r)
            if r == sp and pick is None:
                pick = D
        nreg = sum(1 for r in ranks if r == sp)
        allreg = allreg and nreg == ndir and qn < 1e-4
        cone_dirs[nm] = pick if pick is not None else D
        print(f"{nm:>10}{n:>4}{len(B):>9}{qn:>12.1e}"
              f"{f'{min(ranks)}-{max(ranks)}':>14}{sp:>7}{f'{nreg}/{ndir}':>12}")
    print(f"  2-regular at every direction tested, every family: {allreg}\n")

    print("(c) The curve, by continuation upstairs. Control: a direction with Q(D) != 0.")
    print(f"{'family':>10}{'direction':>12}{'max residual':>14}{'err at t_min':>14}"
          f"{'exponent':>10}{'verdict':>12}")
    ts = [0.05, 0.04, 0.03, 0.02, 0.01] if QUICK else [0.08, 0.06, 0.05, 0.04, 0.03, 0.02, 0.01]
    ok_all = True
    for (nm, n, lines, a, b) in FAMILIES:
        if time.time() - t0 > BUDGET_S * 2:
            print("  [budget reached]"); break
        q = len(lines)
        U0 = frames(n, lines, b)
        B = tangent_basis(n, lines)
        for label in ("cone", "control"):
            if label == "cone":
                D = cone_dirs.get(nm)
                if D is None:
                    continue
            else:
                D = None
                for _ in range(200):
                    cand = sum(c * Bi for c, Bi in zip(rng.standard_normal(len(B)), B))
                    if np.abs(quadric(cand, lines, n, q)).max() > 0.2:
                        D = cand; break
                if D is None:
                    continue
            D = D / np.linalg.norm(D)
            rows = arc(D, U0, lines, n, q, a, b, ts)
            res = max(r[1] for r in rows)
            e = rows[-1][2]
            al = exponent_of(rows)
            good = res < 1e-9 and al > 0.7
            if label == "cone":
                ok_all = ok_all and good
            else:
                ok_all = ok_all and not good
            print(f"{nm:>10}{label:>12}{res:>14.1e}{e:>14.2e}{al:>10.2f}"
                  f"{('tangent D' if good else 'not tangent'):>12}")

    print()
    if worst_id < 1e-9 and allreg and ok_all:
        print("  P42 HOLDS. The quadrics satisfy the all-ones identity, cone directions are")
        print("  2-regular onto the span, and the curve promised by the lemma is exhibited with the")
        print("  tangent it is supposed to have, while a direction off the cone does not acquire")
        print("  one. A6 is no longer a passage from finite orders to a curve: the curve comes from")
        print("  2-regularity in one step, and the hypothesis is a rank checkable on D alone.")
    else:
        print("  P42 FAILS somewhere above. A6 stands where it was, at HEURISTIC, and the frame")
        print("  reduction is not enough on its own.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
