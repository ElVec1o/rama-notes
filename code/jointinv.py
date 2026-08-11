"""No bound reading only the block spectra can prove the extremality, and what can.

The obstruction to Conjecture 1.4 has been stated as "any argument must use idempotency". That is
true and too weak. The sharp statement is about what an argument may read.

THE NO-GO. Every A_k in a tight rank-b PROJECTION family has spectrum {1 with multiplicity b, 0
with multiplicity p-b}, whatever the family. So any bound of the form

    maxroot mu <= F(a, b, p, q, spec A_1, ..., spec A_q)

is CONSTANT on the class. The class contains commuting families whose greatest root tends to the
band edge, so such an F is at best the band edge itself, which is the statement to be proved. No
bound of that shape reduces the problem; it restates it. This kills the barrier and interlacing
route as a source of a REDUCTION, not merely as a source of a sharp constant, and it explains why
the exhaustion sweep found nothing: every tool in it produces a bound of exactly that shape.

The same computation shows why the variance route fails. The Poisson-binomial variance
Var_k = b/a - tr(A_k^2)/a^2 is a spectral functional, so it too is constant on the class, at
(b/a)(1 - 1/a). A bound monotone in the variance does hold across RANKS, where projections are the
minimising end, and that is checked in code/mixeddisc.py and section rank of the note; but
restricted to the projection class it says exactly maxroot <= band edge, which is the target. It is
a reformulation, and a strictly stronger one.

WHAT IS LEFT. A proof must read a JOINT invariant of the family, something that distinguishes two
families with identical block spectra. The obvious candidate is the commutator.

FROZEN BEFORE THE DATA:
  P41. Within the projection class at fixed (p, q, a, b), maxroot mu decreases with the total
       commutator norm sum over i < j of ||[A_i, A_j]||_F^2, and is maximised at zero, the
       commuting locus.

P41 is a phenomenon and not a theorem. If it holds, it names the functional a proof would have to
control; if it fails, the commutator is the wrong invariant and the search for one continues.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from mixed_char_poly import mixed_char_poly
from tff import build_tff
from hessian import coord_family

QUICK = quickmode.QUICK


def ymax(A):
    r = np.roots(mixed_char_poly(A))
    re = [z.real for z in r if abs(z.imag) < 1e-7]
    return max(re) if re else float('nan')


def comm_norm(A):
    q = len(A)
    return sum(float(np.linalg.norm(A[i] @ A[j] - A[j] @ A[i], 'fro') ** 2)
               for i in range(q) for j in range(i + 1, q))


def cyc(m):
    return m, [[i, (i + 1) % m] for i in range(m)]


def main():
    t0 = time.time()
    rng = np.random.default_rng(20260910)
    print("The no-go first: are the block spectra identical across the projection class?\n")
    p, lines = cyc(6)
    q, a, b = len(lines), 2, 2
    Ac = coord_family(p, lines)
    A1, res = build_tff(p, q, a, b, rng)
    sc = np.round(np.linalg.eigvalsh(Ac[0]), 9) + 0.0
    sr = np.round(np.linalg.eigvalsh(A1[0]), 9) + 0.0
    print(f"  commuting block spectrum {sc}")
    print(f"  random    block spectrum {sr}")
    print(f"  identical: {np.allclose(sc, sr)}")
    print("  So any bound reading only spectra is constant on the class, and cannot separate the")
    print("  commuting family from any other. The variance is such a functional and is likewise")
    print("  constant here, at (b/a)(1 - 1/a) = "
          f"{(b / a) * (1 - 1.0 / a):.4f}.\n")

    print("P41 (frozen): maxroot decreases with the total commutator norm and is maximised at")
    print("zero, the commuting locus.\n")
    print(f"{'family':>8}{'families':>10}{'commutator range':>22}{'maxroot range':>22}"
          f"{'correlation':>13}{'max at 0':>10}")
    fams = [("C_4", cyc(4)), ("C_6", cyc(6))]
    if not QUICK:
        fams.append(("C_8", cyc(8)))
    ok = True
    for nm, (p, lines) in fams:
        if time.time() - t0 > (25.0 if QUICK else 600.0):
            print("  [budget reached]"); break
        q = len(lines)
        rows = [(0.0, ymax(coord_family(p, lines)))]
        for _ in range(12 if QUICK else 40):
            A, res = build_tff(p, q, 2, 2, rng)
            if res > 1e-9:
                continue
            y = ymax(A)
            if np.isfinite(y):
                rows.append((comm_norm(A), y))
        x = np.array([r[0] for r in rows]); y = np.array([r[1] for r in rows])
        corr = float(np.corrcoef(x, y)[0, 1]) if len(rows) > 2 else float('nan')
        at0 = bool(y.argmax() == 0)
        if not (corr < 0 and at0):
            ok = False
        print(f"{nm:>8}{len(rows):>10}{f'[{x.min():.2f},{x.max():.2f}]':>22}"
              f"{f'[{y.min():.4f},{y.max():.4f}]':>22}{corr:>13.4f}{str(at0):>10}")
    print()
    if ok:
        print("  P41 holds where tested. The commutator is a joint invariant, so it is not blocked")
        print("  by the no-go, and it is maximised exactly where the conjecture says the maximum")
        print("  is. That makes it the shape a proof would need. It is a correlation on random")
        print("  families, not a theorem, and the search is not adversarial.")
    else:
        print("  P41 fails somewhere above: the commutator is not the invariant, and what is")
        print("  remains open.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
