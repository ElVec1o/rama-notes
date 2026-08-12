"""What the deformed polynomial counts: an SDR count in which intersection becomes cyclic trace.

code/cycle.py gave the expansion

    m_s = (-1)^s sum_{|S| = s} sum_{sigma in Sym(S)} sgn(sigma) prod_{cycles c} tr(prod_{k in c} A_k).

This says what that is, on the commuting locus and off it, and the answer is one substitution.

ON THE LOCUS. There tr(prod_{k in c} A_k) = |cap_{k in c} e_k|, the number of points common to the
blocks of the cycle. And the signed permutation sum is a Moebius inversion: the permutations whose
cycle partition is a given pi contribute, in total,

    sum over sigma with cycle partition pi of sgn(sigma) = prod over blocks B of (-1)^{|B|-1}(|B|-1)!
                                                        = mu(0, pi),

the Moebius function of the partition lattice. Since prod_{B in pi} |cap_{k in B} e_k| counts the
choice functions f with f(k) in e_k that are CONSTANT on every block of pi, Moebius inversion over
the lattice of collisions turns the sum into the count of choice functions with no collision at all:

    sum_{sigma} sgn(sigma) prod_{cycles} |cap e| = # { f : S -> V, f(k) in e_k, f injective }.

So |m_s| counts partial systems of distinct representatives of size s, which by Proposition
prop:bridge is the matching number of the incidence graph. Nothing here is new: this is the classical
inclusion-exclusion count of SDRs, in its partition-lattice form.

OFF THE LOCUS. The formula survives verbatim with one substitution:

    |cap_{k in B} e_k|   becomes   tr(prod_{k in B} A_k).

That is the whole content. The deformed polynomial is the SDR count of a family of SUBSPACES, in
which "how many points do these blocks share" is replaced by the cyclic trace of their projections.
Three consequences, each already recorded separately, now have one source:

  RIGIDITY. Blocks of size at most three have their cyclic traces fixed by tightness and
  idempotency, sum_k A_k = aI giving tr((sum A)^m) = a^m n for m <= 3. So m_0..m_3 cannot move.

  WHY FOUR. At |B| = 4 the cyclic trace tr(A_i A_j A_k A_l) depends on the CYCLIC ORDER, and there
  are three orders on four blocks. A set intersection has no order, so this is exactly where
  non-commutativity first becomes visible: the intersection number splits into three numbers.

  NOT A MATCHING POLYNOMIAL. The weights are multi-way cyclic overlaps, not pairwise ones, and no
  edge-weighted graph carries them. The witness is on the commuting locus: in the Fano plane every
  triple of lines has the same pairwise intersections while concurrent and triangle triples have
  different triple intersections.

FROZEN BEFORE THE DATA:
  P52. (a) On the commuting locus the cycle sum equals the number of injective choice functions, at
           every subset of every family tested.
       (b) Off the locus the same sum with tr(prod A) in place of |cap e| reproduces the
           coefficients of mu exactly.
       (c) At a 4-subset the three cyclic orders give three DIFFERENT traces off the locus and one
           common value on it, which is the precise sense in which m_4 is where non-commutativity
           enters.

FALSIFICATION. A subset where the cycle sum differs from the injective count kills (a) and the
reading with it. If the three cyclic traces at a 4-subset agreed off the locus, m_4 would carry no
more information than an intersection number and the account of why the cut falls at four would be
wrong.
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
from cycle import cycles_of, sgn, cycle_weight

QUICK = quickmode.QUICK


def cyclesum_sets(E, S):
    """The signed permutation sum with intersection numbers as the cycle weights."""
    tot = 0
    for p in itertools.permutations(range(len(S))):
        t = sgn(p)
        for c in cycles_of(p):
            inter = set(E[S[c[0]]])
            for j in c[1:]:
                inter &= set(E[S[j]])
            t *= len(inter)
        tot += t
    return tot


def injective_count(E, S):
    """Choice functions f with f(k) in e_k and all values distinct: partial SDRs on S."""
    n = 0
    for f in itertools.product(*[sorted(E[k]) for k in S]):
        if len(set(f)) == len(f):
            n += 1
    return n


FAMILIES = [
    ("C_4", 4, 4, 2, 2, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("K_4 triples", 4, 4, 3, 3, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]),
    ("K_{3,3}", 6, 9, 3, 2, [[i, 3 + j] for i in range(3) for j in range(3)]),
    ("Fano", 7, 7, 3, 3, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6],
                          [2, 3, 6], [2, 4, 5]]),
]


def main():
    print("P52 (frozen): (a) the cycle sum counts injective choice functions on the locus;")
    print("(b) the same sum with cyclic traces reproduces mu off it; (c) the three cyclic orders")
    print("on four blocks separate off the locus and coincide on it.\n")
    rng = np.random.default_rng(20260812)
    smax = 4 if QUICK else 5

    print("(a) On the commuting locus: signed cycle sum against the SDR count.")
    print(f"{'family':>14}{'subsets':>9}{'up to size':>12}{'agree':>8}")
    ok_a = True
    for (nm, n, q, a, b, lines) in (FAMILIES[:3] if QUICK else FAMILIES):
        E = [set(e) for e in lines]
        tested = 0; good = True
        for s in range(1, min(q, smax) + 1):
            for S in itertools.combinations(range(q), s):
                if cyclesum_sets(E, S) != injective_count(E, S):
                    good = False
                tested += 1
        ok_a = ok_a and good
        print(f"{nm:>14}{tested:>9}{min(q, smax):>12}{str(good):>8}")
    print("  The reason is exact: summing sgn over the permutations with a given cycle partition")
    print("  gives the Moebius function of the partition lattice, and Moebius inversion over the")
    print("  collisions turns choice functions constant on blocks into injective ones.\n")

    print("(b) Off the locus: the same sum with cyclic traces, against mu.")
    print(f"{'family':>14}{'commutator':>12}{'s up to':>9}{'max abs diff':>14}{'agrees':>8}")
    ok_b = True
    for (nm, n, q, a, b, lines) in (FAMILIES[:3] if QUICK else FAMILIES):
        A, res = build_tff(n, q, a, b, rng)
        if res > 1e-9:
            print(f"{nm:>14}   no tight family"); continue
        mu = mixed_char_poly(A)
        worst = 0.0
        for s in range(min(q, smax) + 1):
            cy = ((-1) ** s) * sum(cycle_weight(A, S)
                                   for S in itertools.combinations(range(q), s))
            worst = max(worst, abs(cy - float(mu[s])))
        agree = worst < 1e-7 * max(1.0, abs(float(mu[min(q, smax)])))
        ok_b = ok_b and agree
        print(f"{nm:>14}{commutativity(A):>12.3f}{min(q, smax):>9}{worst:>14.2e}{str(agree):>8}")
    print()

    print("(c) The three cyclic orders on four blocks: one number on the locus, three off it.")
    print(f"{'family':>14}{'4-subsets':>11}{'max spread on locus':>21}{'max spread off':>16}"
          f"{'separates':>11}")
    ok_c = True
    for (nm, n, q, a, b, lines) in (FAMILIES[:3] if QUICK else FAMILIES):
        P = coord_family(n, lines)
        # The sample must actually be off the locus. build_tff returns a COMMUTING family at the
        # K_4 triples, where the quadrics vanish identically, and a commuting sample cannot test a
        # claim about non-commutativity; a first version scored that row as a failure.
        A = None
        for _ in range(40):
            cand, res = build_tff(n, q, a, b, rng)
            if res < 1e-9 and commutativity(cand) > 0.1:
                A = cand
                break
        if A is None:
            print(f"{nm:>14}   no non-commuting family found; row has no power")
            continue

        def spread(M):
            w = 0.0
            for (i, j, k, l) in itertools.combinations(range(q), 4):
                v = [float(np.trace(M[i] @ M[j] @ M[k] @ M[l])),
                     float(np.trace(M[i] @ M[k] @ M[j] @ M[l])),
                     float(np.trace(M[i] @ M[j] @ M[l] @ M[k]))]
                w = max(w, max(v) - min(v))
            return w
        s0 = spread(P); s1 = spread(A)
        sep = s0 < 1e-12 < s1
        ok_c = ok_c and sep
        print(f"{nm:>14}{len(list(itertools.combinations(range(q), 4))):>11}{s0:>21.2e}"
              f"{s1:>16.4f}{str(sep):>11}")
    print("  On the locus the three orders give one value, the intersection number; off it they")
    print("  give three. That split is what m_4 sees and no set system can express.\n")

    if ok_a and ok_b and ok_c:
        print("  P52 HOLDS. The deformed polynomial is the SDR count of a family of SUBSPACES: the")
        print("  same signed permutation sum, with the intersection number |cap e| replaced by the")
        print("  cyclic trace tr(prod A). On the locus that is the classical inclusion-exclusion")
        print("  count of partial systems of distinct representatives, hence the matching number of")
        print("  the incidence graph; off it the intersection number acquires a cyclic order and")
        print("  splits into three at four blocks, which is where and why the rigidity ends.")
    else:
        print("  P52 FAILS somewhere above and the reading must be restated.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
