"""What the deformed polynomial counts: volume-weighted partial transversals (A12).

On the commuting locus the coefficients of mu are matching numbers of the incidence bipartite graph,
equivalently counts of partial systems of distinct representatives. Off the locus they move
continuously and stay nonnegative in the alternating sense, and code/mixeddisc.py identified them as
mixed discriminants. That is a formula, not an object: it says how to compute them, not what they
count. This says what they count.

THE EXPANSION. Decompose each block into rank ones, A_k = sum_{r=1}^b u_{k,r} u_{k,r}^T with the
u_{k,r} an orthonormal basis of the range. Then

    det(y I + sum_k z_k A_k) = sum over sets T of pairs (k,r) of y^{p-|T|} (prod_{(k,r) in T} z_k)
                                    det Gram({u_{k,r} : (k,r) in T}),

by the Cauchy-Binet expansion of a determinant perturbed by rank ones. Now apply prod_k (1 - d/dz_k)
and set z = 0. The operator (1 - d/dz) applied to z^t and evaluated at 0 gives 1 when t = 0, -1 when
t = 1, and ZERO when t >= 2. So every T that uses two or more vectors from the same block dies, and

    mu(y) = sum over T picking AT MOST ONE vector per block  (-1)^{|T|} y^{p-|T|} det Gram(T),

that is, writing mu(y) = sum_s m_s y^{p-s},

    m_s = (-1)^s sum_{|S| = s} sum_{r : S -> [b]} det Gram( u_{k, r(k)} : k in S ).

The inner object is a PARTIAL TRANSVERSAL of the block system, one representative chosen from each
of s blocks, and its weight is the squared volume of the parallelepiped they span. On the commuting
locus the ranges are coordinate subspaces, the representatives are standard basis vectors, and the
squared volume is 1 when they are distinct and 0 when two coincide: the count of partial systems of
distinct representatives, which is the matching number of the incidence graph. Off the locus the
weight interpolates in [0,1] and measures how independent the chosen representatives are.

So the answer to what the deformed polynomial counts is: partial transversals weighted by squared
volume. Nothing is being counted in the integer sense off the locus, and the object being weighted
is exactly the object being counted on it.

WHY THE FOUR LEADING COEFFICIENTS ARE RIGID, which is the constraint this must respect. Expanding
det Gram of s unit vectors gives 1 at s = 1; 1 - <u,v>^2 at s = 2; and at s = 3
1 - <u,v>^2 - <u,w>^2 - <v,w>^2 + 2<u,v><v,w><w,u>. Summing over the choices r turns each closed
walk of inner products into a trace of a product of the A_k, so

    m_2 involves  sum_{k<l} tr(A_k A_l),
    m_3 involves  sum_{k<l} tr(A_k A_l)  and  sum_{k<l<m} tr(A_k A_l A_m).

Both are DETERMINED by tightness and idempotency alone. From sum_k A_k = a I, tr A_k = b and
A_k^2 = A_k:

    tr((sum A)^2) = a^2 n  gives   sum_{k<l} tr(A_k A_l) = (a^2 n - q b)/2,
    tr((sum A)^3) = a^3 n  gives   sum_{k<l<m} tr(A_k A_l A_m) = (a^3 n - 3 a^2 n + 2 q b)/6,

the second because every ordered triple of distinct indices contributes the same value, the blocks
being symmetric so that tr(A_k A_m A_l) = tr(A_k A_l A_m). At s = 4 the Gram determinant carries the
four-cycle <u1,u2><u2,u3><u3,u4><u4,u1>, whose sum over choices is tr(A_k A_l A_m A_r) with four
distinct indices, and there the single relation from tr((sum A)^4) = a^4 n cannot pin the three
independent cyclic classes. So m_4 is the first coefficient carrying a genuine joint invariant.

That is a STRONGER statement than the rigidity recorded in the note, which says the four leading
coefficients do not move along one rotation. This says they do not move ANYWHERE on the class, and
it says why the cut is at four.

FROZEN BEFORE THE DATA:
  P47. (a) m_0, m_1, m_2, m_3 are the same for every tight rank-b projection family at fixed
           (n, q, a, b), namely 1, -qb, C(q,2)b^2 - (a^2 n - q b)/2, and
           -[C(q,3)b^3 - b(q-2)(a^2 n - q b)/2 + (a^3 n - 3 a^2 n + 2 q b)/3].
           At Fano (7,7,3,3) that is 1, -21, 168, -644; at PG(2,3) (13,13,4,4) it is
           1, -52, 1170, -14976; at C_4 (4,4,2,2) it is 1, -8, 20, -16; at K_{3,3} (6,9,3,2) it is
           1, -18, 126, -432.
       (b) m_4 is NOT constant on the class, and neither are m_5 and m_6.
       (c) The transversal formula above reproduces every coefficient of mu exactly, at every
           family, commuting or not.

FALSIFICATION. A tight family whose four leading coefficients differ from the closed forms kills
(a). m_4 constant across the class would push the rigidity one order further and make the note's
degree bound n-4 the wrong cut. A single coefficient where the transversal sum disagrees with mu
kills (c) and with it the whole reading.

NOVELTY. None is claimed for the expansion. For rank-one families it is the standard multi-affine
Cauchy-Binet picture that Marcus, Spielman and Srivastava work with, and the rank-b version follows
by decomposing each projection into rank ones; the mixed determinant literature of Ravichandran and
Leake is the nearest neighbour. What is recorded here is the reading of the coefficients as weighted
partial transversals, and the class-wide rigidity of the first four, which is sharper than what the
note states and is derived rather than observed.
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
from mixed_char_poly import mixed_char_poly
from hessian import coord_family
from tff import build_tff, commutativity
from xu_sharp import pg23

QUICK = quickmode.QUICK


def leading_predicted(n, q, a, b):
    """m_0 .. m_3 from tightness and idempotency alone."""
    from math import comb
    P2 = (a ** 2 * n - q * b) / 2
    P3 = (a ** 3 * n - 3 * a ** 2 * n + 2 * q * b) / 6
    return [1.0,
            -q * b,
            comb(q, 2) * b ** 2 - P2,
            -(comb(q, 3) * b ** 3 - b * (q - 2) * P2 + 2 * P3)]


def ranges(A, b, tol=1e-7):
    """An orthonormal basis of the range of each block, as a (q, p, b) array."""
    out = []
    for Ak in A:
        w, v = np.linalg.eigh(Ak)
        idx = np.argsort(w)[::-1][:b]
        if abs(w[idx].min() - 1.0) > 1e-5:
            return None
        out.append(v[:, idx])
    return np.stack(out)


def transversal_coeffs(U, p, q, b, smax):
    """m_s by summing squared volumes over partial transversals, for s up to smax."""
    out = []
    for s in range(smax + 1):
        tot = 0.0
        for S in itertools.combinations(range(q), s):
            if s == 0:
                tot += 1.0
                continue
            choices = np.array(list(itertools.product(range(b), repeat=s)))
            V = np.stack([np.stack([U[k][:, c[i]] for i, k in enumerate(S)]) for c in choices])
            G = V @ V.transpose(0, 2, 1)
            tot += float(np.linalg.det(G).sum())
        out.append(((-1) ** s) * tot)
    return out


def fano():
    return 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]


CASES = [
    ("C_4", 4, 4, 2, 2, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("K_{3,3}", 6, 9, 3, 2, [[i, 3 + j] for i in range(3) for j in range(3)]),
    ("Fano", 7, 7, 3, 3, fano()[1]),
]


def main():
    print("P47 (frozen): (a) m_0..m_3 are class-wide constants with closed forms; (b) m_4, m_5, m_6")
    print("are not; (c) mu's coefficients are volume-weighted partial-transversal sums.\n")
    rng = np.random.default_rng(20260812)

    print("(a) The four leading coefficients, over the coordinate family and random tight families.")
    print(f"{'family':>10}{'(n,q,a,b)':>14}{'families':>10}{'commutator range':>20}"
          f"{'m_0..m_3 constant':>19}{'match closed form':>19}")
    ok_a = True
    moved = {}
    for (nm, n, q, a, b, lines) in CASES:
        pred = leading_predicted(n, q, a, b)
        fams = [coord_family(n, lines)]
        cms = [0.0]
        for _ in range(6 if QUICK else 20):
            A, res = build_tff(n, q, a, b, rng)
            if res > 1e-9:
                continue
            fams.append(A); cms.append(commutativity(A))
        rows = [mixed_char_poly(A) for A in fams]
        lead = np.array([r[:4] for r in rows])
        const = float(np.abs(lead - lead[0]).max()) < 1e-7
        match = float(np.abs(lead[0] - np.array(pred)).max()) < 1e-7
        ok_a = ok_a and const and match
        m4 = [float(r[4]) for r in rows]
        moved[nm] = (min(m4), max(m4))
        print(f"{nm:>10}{f'({n},{q},{a},{b})':>14}{len(fams):>10}"
              f"{f'[{min(cms):.2f},{max(cms):.2f}]':>20}{str(const):>19}{str(match):>19}")
    print("  closed forms: " + ", ".join(
        f"{nm} {[int(round(x)) for x in leading_predicted(n, q, a, b)]}"
        for (nm, n, q, a, b, _) in CASES) + "\n")

    print("(b) m_4 over the same families: it has to move, or the cut at four is wrong.")
    print(f"{'family':>10}{'min m_4':>16}{'max m_4':>16}{'spread':>14}{'moves':>8}")
    ok_b = True
    for (nm, n, q, a, b, _) in CASES:
        lo, hi = moved[nm]
        mv = (hi - lo) > 1e-6
        ok_b = ok_b and mv
        print(f"{nm:>10}{lo:>16.6f}{hi:>16.6f}{hi - lo:>14.6f}{str(mv):>8}")
    print()

    print("(c) The transversal formula against mu, coefficient by coefficient.")
    print(f"{'family':>10}{'commutator':>12}{'s up to':>9}{'max abs diff':>14}{'agrees':>8}")
    ok_c = True
    for (nm, n, q, a, b, lines) in CASES:
        for label, A in (("coordinate", coord_family(n, lines)), ("deformed", None)):
            if A is None:
                A, res = build_tff(n, q, a, b, rng)
                if res > 1e-9:
                    continue
            U = ranges(A, b)
            if U is None:
                print(f"{nm:>10}   blocks are not rank-{b} projections"); ok_c = False; continue
            smax = min(q, 4 if QUICK else 6)
            mu = mixed_char_poly(A)
            tv = transversal_coeffs(U, n, q, b, smax)
            d = max(abs(float(mu[s]) - tv[s]) for s in range(smax + 1))
            agree = d < 1e-7 * max(1.0, max(abs(x) for x in tv))
            ok_c = ok_c and agree
            print(f"{nm + ' ' + label:>10}{commutativity(A):>12.3f}{smax:>9}{d:>14.2e}"
                  f"{str(agree):>8}")
    print()

    print("(d) PG(2,3): the four rigid coefficients, and m_4, m_5, m_6 moving.")
    n, lines = 13, pg23()[1]
    q, a, b = len(lines), 4, 4
    pred = leading_predicted(n, q, a, b)
    fams = [coord_family(n, lines)]
    for _ in range(1 if QUICK else 3):
        A, res = build_tff(n, q, a, b, rng)
        if res > 1e-9:
            continue
        fams.append(A)
    rows = [mixed_char_poly(A) for A in fams]
    print(f"{'family':>12}{'commutator':>12}" + "".join(f"{'m_' + str(s):>15}" for s in range(7)))
    for A, r in zip(fams, rows):
        print(f"{'coordinate' if commutativity(A) < 1e-9 else 'deformed':>12}"
              f"{commutativity(A):>12.3f}" + "".join(f"{float(r[s]):>15.4f}" for s in range(7)))
    lead = np.array([r[:4] for r in rows])
    ok_d = (float(np.abs(lead - np.array(pred)).max()) < 1e-6)
    if len(rows) > 1:
        tail = np.array([[float(r[s]) for s in (4, 5, 6)] for r in rows])
        ok_d = ok_d and float(np.abs(tail - tail[0]).max()) > 1e-6
    print(f"  predicted m_0..m_3 = {[int(round(x)) for x in pred]}, matched: "
          f"{float(np.abs(lead - np.array(pred)).max()) < 1e-6}")
    print("(e) Is it a WEIGHTED MATCHING POLYNOMIAL? That needs the transversal weight to factor")
    print("through pairwise data. The s=3 weight is b^3 - b(t_kl+t_km+t_lm) + 2 tr(A_k A_l A_m), so")
    print("the question is whether the triple trace is a function of the three pairwise traces.")
    print("A row has POWER only where two triples share pairwise data; on a generic deformed family")
    print("every triple has its own class, all groups are singletons, and the test can see nothing.")
    print("A first version judged those rows as confirming factorisation, which they cannot do.")
    print(f"{'family':>16}{'triples':>9}{'classes':>9}{'collided':>10}{'worst spread':>14}"
          f"{'verdict':>18}")
    ok_e = False
    for (nm, n, q, a, b, lines) in CASES + [("PG(2,3)", 13, 13, 4, 4, pg23()[1])]:
        for label, A in (("coordinate", coord_family(n, lines)), ("deformed", None)):
            if A is None:
                A, res = build_tff(n, q, a, b, rng)
                if res > 1e-9:
                    continue
            groups = {}
            for (k, l, m) in itertools.combinations(range(q), 3):
                key = tuple(sorted(round(float(np.trace(A[x] @ A[y])), 6)
                                   for (x, y) in ((k, l), (k, m), (l, m))))
                groups.setdefault(key, []).append(float(np.trace(A[k] @ A[l] @ A[m])))
            big = [v for v in groups.values() if len(v) > 1]
            if not big:
                print(f"{nm + ' ' + label:>16}"
                      f"{sum(len(v) for v in groups.values()):>9}{len(groups):>9}{0:>10}"
                      f"{'-':>14}{'no power':>18}")
                continue
            worst = max((max(v) - min(v)) for v in big)
            refutes = worst > 1e-7
            ok_e = ok_e or refutes
            print(f"{nm + ' ' + label:>16}{sum(len(v) for v in groups.values()):>9}{len(groups):>9}"
                  f"{sum(len(v) for v in big):>10}{worst:>14.4f}"
                  f"{('REFUTES' if refutes else 'consistent'):>18}")
    print("  A refuting row is two triples with identical pairwise weights and different transversal")
    print("  weights, which is exactly the failure of pairwise factorisation. One such row is enough;")
    print("  rows marked consistent do not support factorisation, they merely fail to break it.\n")

    if ok_a and ok_b and ok_c and ok_d and ok_e:
        print("  P47 HOLDS in all four parts. The deformed polynomial is the generating function of")
        print("  PARTIAL TRANSVERSALS OF THE BLOCK SYSTEM WEIGHTED BY SQUARED VOLUME: choose at most")
        print("  one representative from each block's range, weight by the squared volume they span,")
        print("  sum with alternating sign. On the commuting locus the weight is the indicator that")
        print("  the representatives are distinct, which is the SDR count and the matching number of")
        print("  the incidence graph; off it the weight is the continuous measure of how independent")
        print("  they are. The first four coefficients are then class-wide constants, because the")
        print("  Gram determinant only produces closed walks of length at most three there and those")
        print("  are fixed by tightness and idempotency; the four-cycle enters at m_4, which is the")
        print("  first genuine joint invariant and the reason the cut is at four.")
        print()
        print("  It is NOT a weighted matching polynomial, and the obstruction is already visible on")
        print("  the commuting locus. In the Fano plane any two lines meet in one point, so every")
        print("  triple of blocks has the same pairwise data; but three lines are either concurrent")
        print("  or form a triangle, and the triple trace is 1 or 0 accordingly. Two triples with")
        print("  identical pairwise weights and different transversal weights is exactly the failure")
        print("  of pairwise factorisation, in integers, with no deformation needed. So the weight")
        print("  is irreducibly higher than pairwise and no edge-weighted graph carries it.")
    else:
        print("  P47 FAILS somewhere above. The transversal reading is wrong, or the four leading")
        print("  coefficients are not class-wide constants, and the structural hypothesis needs")
        print("  restating before anything is built on it.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
