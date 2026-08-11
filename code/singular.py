"""The same-group direction is obstructed at second order, and the obstruction is two blocks wide.

code/hessian.py measures that at a commuting tight family some directions in the kernel of the
linearised constraints are not tangent to the variety: the nearest point of the variety to
A0 + eps D sits at distance O(eps) rather than O(eps^2), at Fano and again at AG(2,3). A
measurement cannot distinguish an obstruction from a solver that fails, and the solver used there
had already been replaced once for stalling. This settles it algebraically.

THE SETUP. Write A_k = P_k + eps D_k + eps^2 X_k + O(eps^3) with every A_k a rank-b orthogonal
projection and sum_k A_k = aI. Expanding,

  order 0   P_k^2 = P_k                and  sum_k P_k = aI,
  order 1   P_k D_k + D_k P_k = D_k    and  sum_k D_k = 0,
  order 2   X_k - P_k X_k - X_k P_k = D_k^2  and  sum_k X_k = 0.

The order-two equation is the whole story. Splitting into blocks for ran(P_k) + ker(P_k), where
P_k = [[I,0],[0,0]], the left side is [[-X_11, 0], [0, X_22]]: the off-diagonal blocks of X drop
out entirely and the diagonal blocks are DETERMINED,

  X_11 = -(D^2)_11,      X_22 = +(D^2)_22.

So for a coordinate projection with support e_k, every diagonal entry of X_k is forced, with the
sign fixed by membership:

  (X_k)_{jj} = -(D_k^2)_{jj}  if j is in e_k,     (X_k)_{jj} = +(D_k^2)_{jj}  if j is not.

Nothing is free on the diagonal. The freedom in X lives entirely in the off-diagonal blocks, which
are the next order's tangent directions and cannot help.

THE CONTRADICTION. Take e, f with w in both and v in neither -- the same-group configuration --
and the direction D_e = E_vw + E_wv, D_f = -(E_vw + E_wv), all other blocks zero. Then
D_e^2 = D_f^2 = E_vv + E_ww, the sign squaring away, so at the vertex v, which lies in neither
hyperedge, both blocks are forced the same way:

  (X_e)_vv = +1,   (X_f)_vv = +1,   (X_k)_vv = 0 for every other k,

and the tightness condition sum_k (X_k)_vv = 0 reads 2 = 0. The same happens at w with -2 = 0.

For the cross configuration, v in e but not f and w in f but not e, the identical computation
gives (X_e)_vv = -1 and (X_f)_vv = +1, which cancel. That is the entire difference between the
two kinds, and it is a difference of sign and nothing else.

WHAT IT PROVES. A curve on the variety with velocity D would have X = A''(0)/2 solving that
system, so no such curve exists and D is not in the tangent cone, although it is in the kernel of
the linearisation. The cross directions are in the cone, by the explicit rotations of
code/curvature.py, so the cone contains directions the kernel does and omits D: the commuting point
is a SINGULAR point of the tight projection variety, and it is singular for any commuting tight
family containing the configuration, which is any with a >= 2 and a vertex outside two hyperedges
through a common vertex. The cone is moreover not a linear subspace, since Q is quadratic and does
not vanish on sums (code/tangentcone.py).

This script checks all of that symbolically, and then checks the full linear system for X on the
actual families, so the local argument and the global system are compared rather than one being
trusted.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import itertools
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from xu_sharp import heawood, ag23

QUICK = quickmode.QUICK


def E(n, i, j):
    M = sp.zeros(n, n); M[i, j] = 1; return M


def proj(n, e):
    M = sp.zeros(n, n)
    for x in e:
        M[x, x] = 1
    return M


def check_order2_solved_form(n):
    """Verify X - PX - XP = D^2 forces the diagonal, with the sign given by membership.

    Done on a symbolic X and a symbolic diagonal P with entries 0/1, so the conclusion is about
    the equation and not about any particular D.
    """
    P = sp.diag(*[sp.Symbol(f'p{i}') for i in range(n)])
    X = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'x{min(i, j)}_{max(i, j)}'))
    G = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'g{min(i, j)}_{max(i, j)}'))   # stands for D^2
    L = sp.expand(X - P * X - X * P - G)
    out = []
    for j in range(n):
        ent = L[j, j]
        for val, inside in ((1, True), (0, False)):
            sol = sp.solve(ent.subs(sp.Symbol(f'p{j}'), val), sp.Symbol(f'x{j}_{j}'))
            out.append((j, inside, sp.simplify(sol[0])))
    return out


def local_theorem(n, e, f, v, w, label):
    """The forced diagonal entries at v and w, for the given two hyperedges, exactly."""
    De = E(n, v, w) + E(n, w, v)
    Df = -De
    rows = []
    for (nm, Pset, D) in (('e', e, De), ('f', f, Df)):
        D2 = sp.expand(D * D)
        for j, jn in ((v, 'v'), (w, 'w')):
            sgn = -1 if j in Pset else 1
            rows.append((label, nm, jn, j in Pset, sp.nsimplify(sgn * D2[j, j])))
    return rows


def full_system(n, lines, e, f, v, w):
    """The whole linear system for X on a real family: is it consistent?

    Unknowns are the symmetric entries of every X_k; equations are the order-two idempotency
    relation for each block and the tightness sum. Consistency is decided by comparing the rank of
    the coefficient matrix with that of the augmented matrix, which is a fact about the system and
    not about any solver's behaviour on it.
    """
    q = len(lines)
    iu = [(i, j) for i in range(n) for j in range(i, n)]
    idx = {(k, ij): t for t, (k, ij) in enumerate(itertools.product(range(q), iu))}
    nvar = len(idx)
    De = E(n, v, w) + E(n, w, v)
    D = [sp.zeros(n, n) for _ in range(q)]
    D[e] = De
    D[f] = -De
    rows, rhs = [], []

    def Xsym(k, i, j):
        row = [0] * nvar
        row[idx[(k, (min(i, j), max(i, j)))]] = 1
        return row

    for k in range(q):
        P = proj(n, lines[k])
        D2 = sp.expand(D[k] * D[k])
        for (i, j) in iu:
            # (X - PX - XP)_{ij} = X_ij (1 - P_ii - P_jj)
            c = 1 - P[i, i] - P[j, j]
            r = [c * z for z in Xsym(k, i, j)]
            rows.append(r); rhs.append(D2[i, j])
    for (i, j) in iu:
        r = [0] * nvar
        for k in range(q):
            r[idx[(k, (i, j))]] += 1
        rows.append(r); rhs.append(0)
    A = sp.Matrix(rows)
    b = sp.Matrix(rhs)
    rA = A.rank()
    rAb = A.row_join(b).rank()
    return nvar, rA, rAb, rA == rAb


def main():
    n = 4
    print("The second-order equation, solved symbolically for a general symmetric X.\n")
    print("  X - P X - X P = D^2 has (X - PX - XP)_{ij} = X_ij (1 - P_ii - P_jj), so a diagonal")
    print("  entry has coefficient 1 - 2 P_jj, which is -1 inside the support and +1 outside.")
    print(f"{'vertex':>8}{'in support':>13}{'forced X_jj':>28}")
    for (j, inside, val) in check_order2_solved_form(n)[:4]:
        print(f"{j:>8}{str(inside):>13}{str(val):>28}")
    print("\n  So the diagonal of X is determined by D^2 with a sign, and the off-diagonal blocks,")
    print("  which are the only freedom, never touch a diagonal entry.\n")

    print("The two configurations, with the forced entries at v and w.\n")
    print(f"{'config':>12}{'block':>7}{'vertex':>8}{'in edge':>9}{'forced X_jj':>14}")
    same = local_theorem(6, {0, 1}, {0, 2}, 3, 0, 'same-group')      # w = 0 in both, v = 3 in neither
    cross = local_theorem(6, {3, 1}, {0, 2}, 3, 0, 'cross')          # v = 3 in e only, w = 0 in f only
    tot = {}
    for rows in (same, cross):
        for (lab, blk, jn, inside, val) in rows:
            print(f"{lab:>12}{blk:>7}{jn:>8}{str(inside):>9}{str(val):>14}")
            tot.setdefault((lab, jn), 0)
            tot[(lab, jn)] += int(val)
        print()
    print(f"{'config':>12}{'vertex':>8}{'sum over blocks':>18}{'tightness needs 0':>20}")
    for (lab, jn), sv in sorted(tot.items()):
        print(f"{lab:>12}{jn:>8}{sv:>18}{('CONTRADICTION' if sv else 'consistent'):>20}")

    print("\nThe same conclusion from the full system on real families, by rank.\n")
    print(f"{'family':>12}{'config':>12}{'unknowns':>10}{'rank A':>8}{'rank [A|b]':>12}{'solvable':>10}")
    fams = [("Fano", *heawood())] + ([] if QUICK else [("AG(2,3)", *ag23())])
    for (nm, nn, lines) in fams:
        q = len(lines)
        for label, want in (('same-group', 0), ('cross', 1)):
            found = None
            for (ee, ff) in itertools.permutations(range(q), 2):
                Ee, Ff = set(lines[ee]), set(lines[ff])
                if want == 0:
                    cand = [(vv, ww) for ww in Ee & Ff
                            for vv in range(nn) if vv not in Ee and vv not in Ff]
                else:
                    cand = [(vv, ww) for vv in Ee - Ff for ww in Ff - Ee]
                if cand:
                    found = (ee, ff) + cand[0]
                    break
            if found is None:
                print(f"{nm:>12}{label:>12}   no such configuration"); continue
            ee, ff, vv, ww = found
            nvar, rA, rAb, ok = full_system(nn, lines, ee, ff, vv, ww)
            print(f"{nm:>12}{label:>12}{nvar:>10}{rA:>8}{rAb:>12}"
                  f"{('yes' if ok else 'NO'):>10}")

    print("\n  A system whose augmented rank exceeds its coefficient rank has no solution, so no")
    print("  curve on the variety has that velocity: the direction is in the kernel of the")
    print("  linearisation and not in the tangent cone. The cross directions are in the cone, by")
    print("  the explicit rotations of code/curvature.py, so the cone omits D while the kernel")
    print("  contains it, and Q being quadratic it is not closed under addition either. The")
    print("  commuting point is")
    print("  a singular point of the tight projection variety, for every commuting tight family")
    print("  containing two hyperedges through a common vertex and a vertex outside both.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
