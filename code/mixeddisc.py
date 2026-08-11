"""What the coefficients of mu count off the commuting locus: they are mixed discriminants.

On the commuting locus the coefficients of the mixed characteristic polynomial are matching
numbers of an incidence bipartite graph (Proposition 35 of the note). Off it they move
continuously, stay nonnegative and stay log-concave, and the question was what, if anything, they
count there. The answer needs no new object: they are mixed discriminants, which is the classical
name for the multilinear extension of the determinant and is what the mixed characteristic
polynomial is assembled from in the first place.

THE IDENTITY. With D the mixed discriminant, normalised by

    D(B_1, ..., B_p) = (1/p!) sum over permutations s of det[ B_{s(1)}e_1 | ... | B_{s(p)}e_p ],

writing mu(x) = sum_s c_s x^{p-s},

    c_s = (-1)^s s! binom(p, s) sum over |S| = s of D(A_k : k in S, I repeated p-s).

FROZEN BEFORE THE DATA:
  P37. The identity holds for every tight rank-b projection family, commuting or not, at every s.

This is checked here on families built by alternating projection, whose commutator norms are
reported so that the non-commuting cases are visible as such. Failure at any s would mean the
coefficients are not mixed discriminants and the question is open again.

WHAT IT EXPLAINS. Two properties that were measured now follow from classical results rather than
standing as observations:

  Nonnegativity. Alexandrov's inequality gives D(B_1, ..., B_p) >= 0 for positive semidefinite
  B_i, and the A_k and the identity are positive semidefinite, so every c_s has the sign the
  alternation predicts. This is the same circle of results as the van der Waerden conjecture for
  permanents, proved by Egorychev and by Falikman, whose mixed-discriminant analogue is Bapat's.

  Log-concavity. mu is real-rooted, which is the theorem of Marcus, Spielman and Srivastava for
  mixed characteristic polynomials, and a real-rooted polynomial with nonnegative coefficients has
  log-concave coefficients by Newton's inequalities. Both are checked numerically here against the
  computed coefficients, as a consistency test on the identity rather than as evidence for the
  classical statements.

NOVELTY. None is claimed. Mixed discriminants are classical and the mixed characteristic
polynomial is built from them; the point of recording the identity is that it names the object the
coefficients already are, and it retires the question of what they count off the commuting locus.
On the locus the mixed discriminant of coordinate projections is a count, of systems of distinct
representatives; off it it is the continuous extension of that count and is not itself a count.

COST. The mixed discriminant of p matrices is a sum over p! permutations, so this is exponential in
the dimension and is run at p <= 6. That is enough for an identity: it either holds or it does not.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import itertools
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from mixed_char_poly import mixed_char_poly
from tff import build_tff, commutativity

QUICK = quickmode.QUICK
TOL = 1e-7


def mixed_discriminant(Bs):
    """D(B_1, ..., B_p), by the permutation definition. Exponential in p by construction."""
    p = len(Bs)
    tot = 0.0
    for s in itertools.permutations(range(p)):
        tot += np.linalg.det(np.column_stack([Bs[s[j]][:, j] for j in range(p)]))
    return tot / math.factorial(p)


def coeff_from_mixed_disc(A, p, q, s):
    """The predicted c_s."""
    I = np.eye(p)
    tot = sum(mixed_discriminant([A[k] for k in S] + [I] * (p - s))
              for S in itertools.combinations(range(q), s))
    return ((-1) ** s) * math.factorial(s) * math.comb(p, s) * tot


def newton_ratios(c):
    """Newton's inequalities: with e_s = |c_s| / binom(p, s), e_s^2 >= e_{s-1} e_{s+1}."""
    p = len(c) - 1
    e = [abs(c[s]) / math.comb(p, s) for s in range(p + 1)]
    out = []
    for s in range(1, p):
        if e[s - 1] > 0 and e[s + 1] > 0:
            out.append(e[s] ** 2 / (e[s - 1] * e[s + 1]))
    return out


def gurvits_check():
    """A tight family with q = p and a = b, scaled by 1/a, is a doubly stochastic tuple.

    Gurvits' theorem then bounds its mixed discriminant below by p!/p^p, with equality only at
    A_k = I/p. That tuple is exactly the one the note records as exceeding the tree band, so the
    obstruction it names is the van der Waerden extremal rather than an ad hoc example. Both
    halves are checked, in the normalisation where D(I,...,I) = p!, which is Gurvits' and is p!
    times the permutation average used above.
    """
    rng = np.random.default_rng(20260904)
    print("\nGurvits' bound on the tight families with q = p and a = b, and its extremal.")
    print(f"{'p':>3}{'commutator':>12}{'D_std':>12}{'p!/p^p':>12}{'ratio':>9}{'>= bound':>10}")
    for p in (3, 4):
        A, res = build_tff(p, p, 2, 2, rng)
        if res > 1e-9:
            print(f"{p:>3}   no tight family"); continue
        S = [Ak / 2.0 for Ak in A]
        d = math.factorial(p) * mixed_discriminant(S)
        bd = math.factorial(p) / p ** p
        print(f"{p:>3}{commutativity(A):>12.4f}{d:>12.8f}{bd:>12.8f}{d / bd:>9.4f}"
              f"{str(d >= bd - 1e-12):>10}")
    print(f"{'p':>3}{'D_std at I/p':>16}{'p!/p^p':>12}{'equality':>10}{'max root':>11}"
          f"{'band edge':>11}{'exceeds':>9}")
    for p in (3, 4, 5):
        d = math.factorial(p) * mixed_discriminant([np.eye(p) / p] * p)
        bd = math.factorial(p) / p ** p
        A = np.stack([np.eye(p) * (2.0 / p) for _ in range(p)])
        r = np.roots(mixed_char_poly(A))
        ymax = max(z.real for z in r if abs(z.imag) < 1e-9)
        print(f"{p:>3}{d:>16.10f}{bd:>12.10f}{str(abs(d - bd) < 1e-12):>10}{ymax:>11.6f}"
              f"{4.0:>11.1f}{str(ymax > 4.0):>9}")
    print("  The unique minimiser of the mixed discriminant among doubly stochastic tuples is the")
    print("  family that violates the band. The obstruction is classical, not ad hoc.")


def main():
    t0 = time.time()
    print("P37 (frozen): c_s = (-1)^s s! binom(p,s) sum_{|S|=s} D(A_k : k in S, I^{p-s}) for every")
    print("tight rank-b projection family, commuting or not, at every s.\n")

    rng = np.random.default_rng(20260903)
    cases = [(4, 4, 2, 2), (4, 6, 3, 2)]
    if not QUICK:
        cases += [(5, 5, 2, 2), (6, 6, 2, 2), (6, 9, 3, 2)]

    print(f"{'p':>3}{'q':>3}{'a':>3}{'b':>3}{'commutator':>12}{'max rel diff':>14}"
          f"{'all c_s >= 0 in sign':>22}{'Newton min':>12}")
    worst_all = 0.0
    for (p, q, a, b) in cases:
        if time.time() - t0 > (30.0 if QUICK else 600.0):
            print("  [budget reached]")
            break
        A, res = build_tff(p, q, a, b, rng)
        if res > 1e-9:
            print(f"{p:>3}{q:>3}{a:>3}{b:>3}   no tight family (residual {res:.1e})")
            continue
        cm = commutativity(A)
        cd = mixed_char_poly(A)
        worst = 0.0
        for s in range(0, min(p, q) + 1):
            pred = coeff_from_mixed_disc(A, p, q, s)
            worst = max(worst, abs(pred - cd[s]) / max(1e-12, abs(cd[s])))
        worst_all = max(worst_all, worst)
        signs_ok = all(cd[s] * ((-1) ** s) >= -1e-9 for s in range(min(p, q) + 1))
        nr = newton_ratios(list(cd[:p + 1]))
        print(f"{p:>3}{q:>3}{a:>3}{b:>3}{cm:>12.4f}{worst:>14.2e}"
              f"{str(signs_ok):>22}{(min(nr) if nr else float('nan')):>12.4f}")

    print(f"\n  worst relative disagreement over all families and all s: {worst_all:.2e}")
    if worst_all < TOL:
        print("  P37 holds. The coefficients are mixed discriminants, on and off the commuting")
        print("  locus. Nonnegativity of the alternating signs is Alexandrov's inequality for")
        print("  positive semidefinite arguments, and the Newton ratios above one are the")
        print("  consequence of real-rootedness. Neither is new, and neither is claimed as new;")
        print("  what the identity retires is the question of what the coefficients count off the")
        print("  locus. On the locus they count systems of distinct representatives; off it they")
        print("  are the continuous extension of that count and count nothing.")
    else:
        print("  P37 IS FALSE. The coefficients are not mixed discriminants, and the question of")
        print("  what they are stands open again.")
    gurvits_check()
    return 0


if __name__ == '__main__':
    sys.exit(main())
