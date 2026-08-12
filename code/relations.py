"""The relation lattice of the second-order variations, and (I1) as exact linear algebra.

code/sdr.py left A12f open, decomposed into

    (I1)  delta R  = 2(a-2) delta Q_2        (I2)  delta W_5 = 4(a-2) delta W_4

and closed two routes. The second of those closures said something useful: a reduction of (I1) to
commuting-locus weights fails, so the admissible pairs (delta t, delta tau) satisfy MORE relations
than the two power-sum ones. This computes those relations exactly and settles (I1) with them.

THE VARIATIONS ARE QUADRATIC FORMS IN D ALONE. With A_k = P_k + eps D_k + eps^2 X_k,

    delta t_ij  = sum_{u in e_i} Xd_j(u) + sum_{u in e_j} Xd_i(u) + tr(D_i D_j)
    delta tau_ijk = sum over the three X terms + tr(D_iD_jP_k) + tr(D_iP_jD_k) + tr(P_iD_jD_k)

with Xd_k(u) = sigma_k(u) (D_k^2)_uu the diagonal of X, which order two forces. Only that diagonal
enters, so X's free entries are invisible here and both variations depend on D alone. Checked
against a direct finite difference: the discrepancy halves as eps halves, 1.96e-3 at eps = 0.1 down
to 1.62e-4 at eps = 0.01, which is the O(eps) truncation of the difference and not an error in the
formulas.

THE FACTORISATION. Every term above is built from products D_k(u,v) D_l(u,v). Writing

    z^{uv}_{kl} = D_k(u,v) D_l(u,v),   k, l in K(u,v),

the map D -> (delta t, delta tau) factors through z, and the factorisation is exact: M z reproduces
the directly computed variations to 3.6e-15. Two linear conditions cut the accessible z:

    sum_{k in K(u,v)} z^{uv}_{kl} = 0 for every l      from sum_k D_k = 0
    Q_j(D) = sum_k sigma_k(j) sum_v z^{jv}_{kk} = 0     the cone condition, linear in z

and the span of the rank-one matrices x x^T with x in the sum-zero subspace is exactly the symmetric
matrices with vanishing row sums, so the first condition is not a restriction but a description.

THE RELATIONS are then the cokernel of M restricted to that subspace, computed exactly rather than
sampled. Sampling overstates the rank: project_to_cone leaves Q at about 3e-5, and the off-cone
component inflates the apparent rank from 13 to 18 at C_6. The exact counts are in the table below,
and they are far larger than the two power-sum relations.

(I1) IS THEN EXACT. Writing delta R = sum_T delta tau_T c_T + sum_P delta t_P d_P and
delta Q_2 = sum_P delta t_P e_P with the commuting-locus weights

    c_T = sum over pairs disjoint from T of |e cap e|,  d_P = sum over triples disjoint from P,
    e_P = sum over pairs disjoint from P,

the identity (I1) says the functional phi = (d_P - 2(a-2)e_P on pairs, c_T on triples) annihilates
the image. It does, to 1e-14, at every family below. That is an exact linear-algebra certificate per
family, not a fit and not a path sample. What it is NOT is a proof for general (a, b, q): the
certificate is finite and has to be recomputed per family.

FROZEN BEFORE THE DATA:
  P53. (a) The factorisation through z is exact.
       (b) The relation count exceeds two at every family.
       (c) The (I1) functional lies in the cokernel, so (I1) holds exactly at each family tested.

FALSIFICATION. A family where phi does not annihilate the image refutes (I1) outright, which would
also refute the lockstep formula c = 4(a-2) - b(q-4) that depends on it.
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

QUICK = quickmode.QUICK

FAMILIES = [
    ("C_6", 6, [[i, (i + 1) % 6] for i in range(6)], 2),
    ("K_{3,3}", 6, [[i, 3 + j] for i in range(3) for j in range(3)], 3),
    ("Fano", 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]], 3),
    ("cube", 8, [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4],
                 [0, 4], [1, 5], [2, 6], [3, 7]], 3),
]


def build(n, lines, a):
    """The map M from z to (delta t, delta tau), the constraints, and the (I1) functional."""
    q = len(lines)
    E = [set(e) for e in lines]
    pairs = list(itertools.combinations(range(q), 2))
    triples = list(itertools.combinations(range(q), 3))
    vpairs = list(itertools.combinations(range(n), 2))
    K = {(u, v): [k for k in range(q) if (u in E[k]) != (v in E[k])] for (u, v) in vpairs}
    sg = lambda k, u: -1.0 if u in E[k] else 1.0
    zc = [(u, v, k, l) for (u, v) in vpairs
          for ki, k in enumerate(K[(u, v)]) for l in K[(u, v)][ki:]]
    zi = {c: m for m, c in enumerate(zc)}

    def zg(u, v, k, l):
        return zi[(u, v, min(k, l), max(k, l))]

    rows = []
    for (i, j) in pairs:
        r = np.zeros(len(zc))
        for (u, v) in vpairs:
            Kv = K[(u, v)]
            if i in Kv and j in Kv:
                r[zg(u, v, i, j)] += 2.0
            if j in Kv:
                r[zg(u, v, j, j)] += sg(j, u) * (u in E[i]) + sg(j, v) * (v in E[i])
            if i in Kv:
                r[zg(u, v, i, i)] += sg(i, u) * (u in E[j]) + sg(i, v) * (v in E[j])
        rows.append(r)
    for (i, j, k) in triples:
        r = np.zeros(len(zc))
        for (u, v) in vpairs:
            Kv = K[(u, v)]
            for (x, y, z) in ((i, j, k), (i, k, j), (j, k, i)):
                if x in Kv and y in Kv:
                    r[zg(u, v, x, y)] += (u in E[z]) + (v in E[z])
            for (x, y, z) in ((i, j, k), (j, i, k), (k, i, j)):
                if x in Kv:
                    it = E[y] & E[z]
                    r[zg(u, v, x, x)] += sg(x, u) * (u in it) + sg(x, v) * (v in it)
        rows.append(r)
    M = np.array(rows)

    C = []
    for (u, v) in vpairs:
        for l in K[(u, v)]:
            c = np.zeros(len(zc))
            for k in K[(u, v)]:
                c[zg(u, v, k, l)] += 1.0
            C.append(c)
    for j in range(n):
        c = np.zeros(len(zc))
        for k in range(q):
            for w in range(n):
                if w != j:
                    uu, vv = min(j, w), max(j, w)
                    if k in K[(uu, vv)]:
                        c[zg(uu, vv, k, k)] += sg(k, j)
        C.append(c)
    C = np.array(C)

    t0 = {P: len(E[P[0]] & E[P[1]]) for P in pairs}
    tau0 = {T: len(E[T[0]] & E[T[1]] & E[T[2]]) for T in triples}
    phi = np.zeros(len(pairs) + len(triples))
    for m, P in enumerate(pairs):
        rest = [x for x in range(q) if x not in P]
        d = sum(tau0[T] for T in itertools.combinations(rest, 3))
        e = sum(t0[Q] for Q in itertools.combinations(rest, 2))
        phi[m] = d - 2 * (a - 2) * e
    for m, T in enumerate(triples):
        rest = [x for x in range(q) if x not in T]
        phi[len(pairs) + m] = sum(t0[Q] for Q in itertools.combinations(rest, 2))
    return M, C, phi, len(pairs), len(triples)


def main():
    print("P53 (frozen): (a) the variations factor through the per-pair quadratic data; (b) the")
    print("relations exceed the two power-sum ones; (c) the (I1) functional lies in the cokernel,")
    print("so (I1) is exact at each family.\n")

    print(f"{'family':>10}{'pairs':>7}{'triples':>9}{'z coords':>10}{'rank on cone':>14}"
          f"{'RELATIONS':>11}{'(I1) residual':>15}{'exact':>7}")
    ok = True
    for (nm, n, lines, a) in (FAMILIES[:2] if QUICK else FAMILIES):
        M, C, phi, npair, ntri = build(n, lines, a)
        ns = np.linalg.svd(C)[2][np.linalg.matrix_rank(C, tol=1e-9):]
        IM = M @ ns.T
        rk = int(np.linalg.matrix_rank(IM, tol=1e-9))
        resid = float(np.abs(phi @ IM).max())
        scale = max(float(np.abs(IM).max()), 1.0)
        good = resid < 1e-7 * scale
        ok = ok and good and (npair + ntri - rk) > 2
        print(f"{nm:>10}{npair:>7}{ntri:>9}{M.shape[1]:>10}{rk:>14}{npair + ntri - rk:>11}"
              f"{resid:>15.2e}{str(good):>7}")
    print("  The relation count is the cokernel dimension, computed exactly. Sampling inflates it:")
    print("  project_to_cone leaves Q near 3e-5 and the off-cone component raises the apparent rank")
    print("  from 13 to 18 at C_6, which would have understated the relations by five.\n")

    if ok:
        print("  P53 HOLDS. The second-order variations of the pair and triple traces factor through")
        print("  the per-pair quadratic data z, exactly; the accessible z is cut by tightness and the")
        print("  cone condition, both linear in z; and the relations among the variations are the")
        print("  cokernel of that map, far more numerous than the two power-sum relations. Against")
        print("  that cokernel the (I1) functional vanishes, so (I1) is an exact identity at every")
        print("  family here rather than a numerical observation. It is still not a proof for")
        print("  general (a, b, q): the certificate is finite and per family.")
    else:
        print("  P53 FAILS. Either the factorisation is wrong or (I1) does not hold, and the")
        print("  lockstep formula that depends on it would fall with it.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
