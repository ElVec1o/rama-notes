"""Why long cycles carry no second-order information: a counting bound, and where it stops.

code/relations.py found that blocks beyond four add nothing to the second-order deformation, at four
families, by exact linear algebra. That was a measurement. This gives the reason, proves half of it,
and says exactly which half is left.

THE ROW OF A CYCLIC WORD. Expanding tr(A_{k_1} ... A_{k_m}) to second order with
A_k = P_k + eps D_k + eps^2 X_k, the terms with two D's at positions p < p' are

    tr(D_x B D_y C) = sum_{u,v} B(v) C(u) D_x(u,v) D_y(u,v),

where x, y are the blocks at those positions and B, C are the products of the P's along the two arcs
between them, hence the indicator functions of the intersections of the blocks on those arcs. In the
coordinates z^{uv}_{kl} = D_k(u,v) D_l(u,v) the coefficient at z^{uv}_{xy} is therefore

    1_{u in I_1} 1_{v in I_2} + 1_{v in I_1} 1_{u in I_2},

with I_1, I_2 the two arc intersections. The term with one X contributes only on the diagonal
z^{uv}_{kk}, with the intersection of all the other blocks.

THE BOUND. Suppose the coefficient at z^{uv}_{xy} is nonzero, say u in I_1 and v in I_2. Every block
on arc 1 contains u, and x and y both split the pair (u,v), so whichever of them contains u is a
further block containing u. A point of a tight family lies in exactly a blocks, so

    |arc 1| + 1 <= a       and likewise      |arc 2| + 1 <= a,

whence m = 2 + |arc 1| + |arc 2| <= 2a. If instead x and y both contain u, then arc 1 has at most
a - 2 blocks and arc 2 at most a, giving the same bound. Hence

    the second-order row of a cyclic word of length m > 2a vanishes IDENTICALLY.

That is a theorem, not a measurement, and the table below shows it is tight: at K_{3,3} and the cube,
both with a = 3, rows of length exactly 6 = 2a are nonzero.

WHAT IT SETTLES AND WHAT IT DOES NOT. At a = 2 the bound is 2a = 4, so every cycle of length five or
more has a vanishing row and the four-block ceiling is PROVED. At a = 3 the bound is 6, and rows of
length five and six are genuinely nonzero, yet the rank still does not increase beyond size four; so
for a >= 3 those rows are nonzero and LINEARLY DEPENDENT on the shorter ones, which this does not
explain. That dependence is the remaining half of the ceiling.

FROZEN BEFORE THE DATA:
  P54. (a) Every row of length greater than 2a vanishes identically, at every family.
       (b) The bound is tight: some family has a nonzero row of length exactly 2a.
       (c) At a = 2 this closes the four-block ceiling outright, the bound being 4.

FALSIFICATION. A nonzero row of length greater than 2a refutes the counting argument. A family where
rows of length 2a are all zero would leave the bound unproved as stated, though the ceiling would
still hold.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from relations import block_rows

QUICK = quickmode.QUICK

FAMILIES = [
    ("C_4", 4, [[0, 1], [1, 2], [2, 3], [3, 0]], 2),
    ("C_6", 6, [[i, (i + 1) % 6] for i in range(6)], 2),
    ("C_8", 8, [[i, (i + 1) % 8] for i in range(8)], 2),
    ("K_4 triples", 4, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]], 3),
    ("Fano", 7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]], 3),
    ("K_{3,3}", 6, [[i, 3 + j] for i in range(3) for j in range(3)], 3),
    ("cube", 8, [[0, 1], [1, 2], [2, 3], [3, 0], [4, 5], [5, 6], [6, 7], [7, 4],
                 [0, 4], [1, 5], [2, 6], [3, 7]], 3),
]


def main():
    print("P54 (frozen): (a) rows of length above 2a vanish identically; (b) the bound is tight;")
    print("(c) at a = 2 that closes the four-block ceiling.\n")

    print(f"{'family':>14}{'a':>3}{'2a':>4}{'nonzero sizes':>20}{'first zero':>12}"
          f"{'bound holds':>13}{'tight':>7}")
    ok_a = True; tight = False
    fams = FAMILIES[:4] if QUICK else FAMILIES
    for (nm, n, lines, a) in fams:
        rows, _ns = block_rows(n, lines)
        nz = [m for m in sorted(rows)
              if rows[m].shape[0] > 0 and np.abs(rows[m]).max() > 1e-12]
        zr = [m for m in sorted(rows)
              if rows[m].shape[0] > 0 and np.abs(rows[m]).max() <= 1e-12]
        good = all(m <= 2 * a for m in nz)
        ok_a = ok_a and good
        istight = (2 * a) in nz
        tight = tight or istight
        print(f"{nm:>14}{a:>3}{2 * a:>4}{str(nz):>20}{(zr[0] if zr else '-'):>12}"
              f"{str(good):>13}{str(istight):>7}")
    print("  'first zero' is the smallest length whose rows all vanish; a dash means the family is")
    print("  too small to reach one. Tightness at a = 3 is what makes the bound the right one.\n")

    print("What the bound closes, by regime.")
    print(f"{'a':>4}{'bound 2a':>10}{'four-block ceiling':>22}{'status':>34}")
    print(f"{2:>4}{4:>10}{'follows outright':>22}{'PROVED by the counting bound':>34}")
    print(f"{3:>4}{6:>10}{'needs more':>22}{'rows of length 5,6 nonzero but dependent':>34}")
    print()

    if ok_a and tight:
        print("  P54 HOLDS. The second-order row of a cyclic word of length above 2a vanishes")
        print("  identically, because a point of a tight family lies in exactly a blocks and the")
        print("  blocks along an arc all contain the same point. The bound is tight at a = 3. At")
        print("  a = 2 it is exactly four, so the four-block ceiling is proved there and needs no")
        print("  linear algebra. At a >= 3 the ceiling still holds numerically but by a different")
        print("  mechanism: the rows of length five and six are nonzero and lie in the span of the")
        print("  shorter ones, and that dependence is not explained here.")
    else:
        print("  P54 FAILS. Either a long row is nonzero, refuting the counting argument, or the")
        print("  bound is not tight and is the wrong statement.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
