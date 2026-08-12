"""What m_4 is, exactly: the cycle expansion and the two invariants that carry the deformation.

code/transversal.py identified the coefficients as volume-weighted partial transversals and showed
m_0..m_3 are class-wide constants while m_4 is the first to move. It did not say what m_4 IS. This
does, in closed form, and the answer has two terms rather than the one expected.

THE CYCLE EXPANSION. The Gram determinant of the chosen representatives is a sum over permutations,
det Gram = sum_sigma sgn(sigma) prod_i G_{i,sigma(i)}, and a permutation factors into cycles. A fixed
point contributes G_ii = 1 and a free choice, so a factor b = tr(A_k); a cycle (k_1 ... k_m)
contributes <u_{k_1},u_{k_2}> ... <u_{k_m},u_{k_1}>, which summed over the choices is exactly
tr(A_{k_1} ... A_{k_m}). So the two operations commute and

    sum_{r : S -> [b]} det Gram = sum over sigma in Sym(S) of
                                     sgn(sigma) * prod over cycles c of tr(prod_{k in c} A_k),

uniformly, fixed points included since tr(A_k) = b. Combined with the transversal formula,

    m_s = (-1)^s sum_{|S| = s} sum_{sigma in Sym(S)} sgn(sigma) prod_c tr(prod_{k in c} A_k).

On the commuting locus tr(A_{k_1} ... A_{k_m}) is the number of points common to those blocks, so
this is a signed sum over permutations weighted by products of INTERSECTION NUMBERS of the cycles;
off the locus the intersection numbers are replaced by traces of products of projections. That is
the combinatorial content, and it is the same object in both regimes.

M_4 IN CLOSED FORM. Sym(4) has five cycle types: identity, six transpositions, three double
transpositions, eight 3-cycles, six 4-cycles. Every ordering of a cycle gives the same trace, the
blocks being symmetric, so the eight 3-cycles collapse to 2 per triple and the six 4-cycles to 2 per
cyclic class. Writing t_ij = tr(A_i A_j), tau_ijk = tr(A_i A_j A_k), and summing over all 4-subsets,

    m_4 = C(q,4) b^4 - b^2 C(q-2,2) P_2 + Q_2 + 2 b (q-3) P_3 - 2 W_4 ,

    P_2 = sum_{i<j} t_ij          = (a^2 n - q b)/2                    class-wide constant
    P_3 = sum_{i<j<k} tau_ijk     = (a^3 n - 3 a^2 n + 2 q b)/6        class-wide constant
    Q_2 = sum over unordered pairs of DISJOINT pairs of t_ij t_kl      VARIES
    W_4 = sum over 4-subsets of the three cyclic classes of tr(A_i A_j A_k A_l)   VARIES

THE POINT, and it was not what was expected. The deformation of m_4 is carried by TWO independent
invariants, not one. The four-cycle trace W_4 is the new object, but the double-transposition term
Q_2 also moves, because only the SUM of the pairwise traces is fixed by the class, not the individual
t_ij, and Q_2 is quadratic in them. So "m_4 is the four-cycle count" is false; m_4 is the four-cycle
count plus a quadratic correction in the pairwise traces.

FROZEN BEFORE THE DATA:
  P48. (a) The cycle expansion reproduces sum_r det Gram exactly, at every family and every s tested.
       (b) The closed form for m_4 above holds exactly at every tight family.
       (c) m_4 is NOT a function of W_4 alone: two families with equal W_4 and different Q_2 have
           different m_4, so the four-cycle trace does not determine the first moving coefficient.
       (d) m_5 and m_6 are not functions of m_4: over random tight families the map m_4 -> (m_5, m_6)
           is not single valued, so the deformation is not one dimensional.

FALSIFICATION. A family where the cycle expansion or the closed form disagrees kills (a) or (b). If
m_4 turned out to be an exact function of W_4 the deformation would be governed by one invariant and
(c) would be wrong, which would be a better result than the one predicted. If (d) failed, all higher
coefficients would be functions of the first moving one and the class would be effectively one
dimensional.

NOVELTY. The cycle expansion of a Gram determinant is classical, and for mixed discriminants it is
the standard permutation form; no novelty is claimed for it. What is recorded is the resulting closed
form for the first non-rigid coefficient of mu and the identification of the two invariants that
carry it.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import itertools
from math import comb
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from mixed_char_poly import mixed_char_poly
from hessian import coord_family
from tff import build_tff, commutativity
from transversal import ranges, transversal_coeffs, fano
from xu_sharp import pg23

QUICK = quickmode.QUICK


def cycles_of(perm):
    """The cycles of a permutation given as a tuple, as lists of positions."""
    seen = [False] * len(perm)
    out = []
    for i in range(len(perm)):
        if seen[i]:
            continue
        c = []
        j = i
        while not seen[j]:
            seen[j] = True
            c.append(j)
            j = perm[j]
        out.append(c)
    return out


def sgn(perm):
    return (-1) ** (len(perm) - len(cycles_of(perm)))


def cycle_weight(A, S):
    """sum over sigma of sgn(sigma) prod over cycles of tr(prod A), for the blocks in S."""
    s = len(S)
    tot = 0.0
    for perm in itertools.permutations(range(s)):
        term = float(sgn(perm))
        for c in cycles_of(perm):
            M = A[S[c[0]]]
            for j in c[1:]:
                M = M @ A[S[j]]
            term *= float(np.trace(M))
        tot += term
    return tot


def invariants(A, q):
    """P_2, P_3, Q_2 and W_4."""
    t = {(i, j): float(np.trace(A[i] @ A[j])) for i, j in itertools.combinations(range(q), 2)}
    P2 = sum(t.values())
    P3 = sum(float(np.trace(A[i] @ A[j] @ A[k]))
             for i, j, k in itertools.combinations(range(q), 3))
    Q2 = 0.0
    W4 = 0.0
    for S in itertools.combinations(range(q), 4):
        i, j, k, l = S
        Q2 += t[(i, j)] * t[(k, l)] + t[(i, k)] * t[(j, l)] + t[(i, l)] * t[(j, k)]
        W4 += (float(np.trace(A[i] @ A[j] @ A[k] @ A[l]))
               + float(np.trace(A[i] @ A[k] @ A[j] @ A[l]))
               + float(np.trace(A[i] @ A[j] @ A[l] @ A[k])))
    return P2, P3, Q2, W4


def m4_closed(A, n, q, a, b):
    P2, P3, Q2, W4 = invariants(A, q)
    return comb(q, 4) * b ** 4 - b ** 2 * comb(q - 2, 2) * P2 + Q2 + 2 * b * (q - 3) * P3 - 2 * W4


CASES = [
    ("C_4", 4, 4, 2, 2, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("K_{3,3}", 6, 9, 3, 2, [[i, 3 + j] for i in range(3) for j in range(3)]),
    ("Fano", 7, 7, 3, 3, fano()[1]),
]


def main():
    print("P48 (frozen): (a) the cycle expansion is exact; (b) m_4 has the closed form above;")
    print("(c) m_4 is not a function of W_4 alone; (d) m_5, m_6 are not functions of m_4.\n")
    rng = np.random.default_rng(20260813)

    print("(a) The cycle expansion against the transversal sum, subset by subset.")
    print(f"{'family':>16}{'commutator':>12}{'s up to':>9}{'max abs diff':>14}{'agrees':>8}")
    ok_a = True
    for (nm, n, q, a, b, lines) in CASES:
        for label, A in (("coordinate", coord_family(n, lines)), ("deformed", None)):
            if A is None:
                A, res = build_tff(n, q, a, b, rng)
                if res > 1e-9:
                    continue
            U = ranges(A, b)
            smax = min(q, 4 if QUICK else 5)
            tv = transversal_coeffs(U, n, q, b, smax)
            worst = 0.0
            for s in range(smax + 1):
                cy = ((-1) ** s) * sum(cycle_weight(A, S)
                                       for S in itertools.combinations(range(q), s))
                worst = max(worst, abs(cy - tv[s]))
            agree = worst < 1e-6 * max(1.0, max(abs(x) for x in tv))
            ok_a = ok_a and agree
            print(f"{nm + ' ' + label:>16}{commutativity(A):>12.3f}{smax:>9}{worst:>14.2e}"
                  f"{str(agree):>8}")
    print()

    print("(b) The closed form for m_4 against mu, and (c) the two invariants that carry it.")
    print(f"{'family':>10}{'families':>10}{'max |m_4 - closed|':>20}{'W_4 range':>22}"
          f"{'Q_2 range':>22}{'exact':>7}")
    ok_b = True
    data = {}
    for (nm, n, q, a, b, lines) in CASES:
        fams = [coord_family(n, lines)]
        for _ in range(6 if QUICK else 25):
            A, res = build_tff(n, q, a, b, rng)
            if res > 1e-9:
                continue
            fams.append(A)
        worst = 0.0
        rows = []
        for A in fams:
            mu = mixed_char_poly(A)
            P2, P3, Q2, W4 = invariants(A, q)
            cl = m4_closed(A, n, q, a, b)
            worst = max(worst, abs(float(mu[4]) - cl))
            rows.append((float(mu[4]), W4, Q2, [float(mu[s]) for s in range(4, min(7, n + 1))]))
        data[nm] = rows
        ex = worst < 1e-6 * max(1.0, max(abs(r[0]) for r in rows))
        ok_b = ok_b and ex
        print(f"{nm:>10}{len(fams):>10}{worst:>20.2e}"
              f"{f'[{min(r[1] for r in rows):.2f},{max(r[1] for r in rows):.2f}]':>22}"
              f"{f'[{min(r[2] for r in rows):.2f},{max(r[2] for r in rows):.2f}]':>22}{str(ex):>7}")
    print()

    print("(c) Does W_4 alone determine m_4? Fit m_4 on W_4 only, and on (W_4, Q_2).")
    print(f"{'family':>10}{'residual on W_4':>18}{'residual on (W_4,Q_2)':>24}{'needs both':>12}")
    ok_c = True
    for (nm, n, q, a, b, _) in CASES:
        rows = data[nm]
        y = np.array([r[0] for r in rows])
        W = np.array([r[1] for r in rows])
        Q = np.array([r[2] for r in rows])
        def resid(X):
            X = np.column_stack([X, np.ones(len(y))])
            sol, *_ = np.linalg.lstsq(X, y, rcond=None)
            return float(np.abs(X @ sol - y).max())
        r1 = resid(W[:, None])
        r2 = resid(np.column_stack([W, Q]))
        needs = r1 > 100 * max(r2, 1e-12)
        ok_c = ok_c and needs
        print(f"{nm:>10}{r1:>18.3e}{r2:>24.3e}{str(needs):>12}")
    print("  A residual near zero on W_4 alone would mean the four-cycle trace determines m_4.")
    print("  Near zero only on the pair means both invariants are needed.\n")

    print("(d) Are m_5 and m_6 functions of m_4? Fit m_5 as a polynomial in m_4 and compare the")
    print("residual against m_5's own spread. A window test on |dm_4| cannot answer this: with the")
    print("window set to a thousandth of |m_4| it admits the whole range and reports the slope.")
    print(f"{'family':>10}{'families':>10}{'spread m_5':>14}{'best residual':>15}"
          f"{'residual/spread':>17}{'independent':>13}")
    ok_d = True
    for (nm, n, q, a, b, _) in CASES:
        rows = [r for r in data[nm] if len(r[3]) >= 2]
        if len(rows) < 6:
            print(f"{nm:>10}   too few families"); ok_d = False; continue
        x = np.array([r[3][0] for r in rows])
        y = np.array([r[3][1] for r in rows])
        spread = float(y.max() - y.min())
        best = float('inf')
        for deg in (1, 2, 3):
            if len(rows) <= deg + 1:
                break
            X = np.column_stack([x ** d for d in range(deg + 1)])
            sol, *_ = np.linalg.lstsq(X, y, rcond=None)
            best = min(best, float(np.abs(X @ sol - y).max()))
        ratio = best / max(spread, 1e-30)
        indep = ratio > 0.05
        ok_d = ok_d and indep
        print(f"{nm:>10}{len(rows):>10}{spread:>14.4f}{best:>15.4f}{ratio:>17.4f}"
              f"{str(indep):>13}")
    print("  A residual that is a substantial fraction of the spread means no low-degree function of")
    print("  m_4 reproduces m_5, so the deformation is not one dimensional. The closed form says why:")
    print("  m_4 sees Q_2 and the four-cycles, while m_5 also sees the five-cycles.\n")

    if ok_a and ok_b and ok_c and ok_d:
        print("  P48 HOLDS. The coefficients are signed sums over permutations of the chosen blocks,")
        print("  weighted by products of the cycles' intersection numbers on the commuting locus and")
        print("  by traces of products of projections off it. The first non-rigid coefficient has an")
        print("  exact closed form, and it is carried by TWO invariants: the four-cycle trace W_4,")
        print("  which is the new object, and a quadratic correction Q_2 in the pairwise traces,")
        print("  whose individual values the class does not fix even though their sum is fixed. So")
        print("  the deformation is not governed by the four-cycle count alone.")
    else:
        print("  P48 FAILS somewhere above; the closed form or the independence claim is wrong and")
        print("  the reading of m_4 needs restating.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
