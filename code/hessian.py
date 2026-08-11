"""Does the variety fill the linearised tangent space at the commuting point?

code/curvature.py computes exactly that the top root falls as C theta^2, with the single value
C = 0.0371785140129474... along all 168 rotations of the shape "rotate one plane, apply it to two
blocks". The obvious next step is the full Hessian on the tangent space, since a quadratic form
can have every diagonal entry negative and still be indefinite. This script was written to do
that, and the first thing it found is that the step is not available, for a reason worth more than
the Hessian would have been.

THE LINEARISATION. Writing A_k = P_k + eps D_k + O(eps^2):

  idempotency  (P + eps D)^2 = P + eps D  gives  P D + D P = D, so D is off-diagonal for the
    splitting range(P_k) + ker(P_k); with P_k the coordinate projection on the hyperedge e_k that
    means D_k is supported on pairs (i,j) with EXACTLY ONE of i, j in e_k;
  tightness  sum_k A_k = aI  gives  sum_k D_k = 0.

So the linearised space decomposes over unordered vertex pairs: writing D_k as a sum of
m^k_{ij}(E_ij + E_ji), the only constraint is sum over K_ij of m^k_{ij} = 0, with K_ij the
hyperedges containing exactly one of i and j. For the Fano family that is 63.

WHAT IS ACTUALLY TESTED. Whether each basis direction is tangent TO THE VARIETY, by locating the
nearest point of the variety to A0 + eps D and reading the exponent: distance O(eps^2) means
tangent, distance O(eps) means not. The alternating projection of tff.restore cannot answer this,
because it stalls -- it fails on the same 21 directions at every step size and still fails at
100000 iterations, with the residual pinned at 2.6e-3 -- so the nearest point is found by weighted
least squares instead.

The directions split by whether the two blocks lie on opposite sides of the vertex pair. The
CROSS ones, which are exactly the tangents of the curves in code/curvature.py, are tangent. The
SAME-group ones are not. Since cross differences span the linearised space, the tangent directions
are then not closed under subtraction, so the tangent cone is not a linear subspace and the
commuting point is a singular point of the variety. A Hessian on the linearised space is therefore
the wrong object, which is why the second-order coefficient is computed along explicit curves.

THIS IS NUMERICAL, and it is a statement about exponents rather than about a value: the ratios
distance/eps and distance/eps^2 are printed at several step sizes so that which of them is
constant can be read off rather than asserted.
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
from tff import restore, tff_residual
from xu_sharp import heawood, pappus, ag23

QUICK = quickmode.QUICK
BUDGET_S = 60.0 if QUICK else 1800.0
TOL = 1e-9
C_EXACT_FANO = 0.0371785140129474      # code/curvature.py, exact rational arithmetic


def coord_family(n, lines):
    A = np.zeros((len(lines), n, n))
    for k, e in enumerate(lines):
        for v in e:
            A[k, v, v] = 1.0
    return A


def tangent_basis(n, lines):
    """A basis of {D : D_k off-diagonal for P_k, sum_k D_k = 0}, one block per vertex pair."""
    q = len(lines)
    basis = []
    for i, j in itertools.combinations(range(n), 2):
        K = [k for k, e in enumerate(lines) if (i in e) != (j in e)]
        for t in range(len(K) - 1):                 # differences span the sum-zero subspace
            D = np.zeros((q, n, n))
            D[K[t], i, j] = D[K[t], j, i] = 1.0
            D[K[t + 1], i, j] = D[K[t + 1], j, i] = -1.0
            basis.append(D)
    return basis


def lam_max(A):
    r = np.roots(mixed_char_poly(A))
    return max(z.real for z in r if abs(z.imag) < 1e-8)


def step(A0, U, eps, a, b, n, q):
    """Move eps along U and return to the variety; None if the retraction does not converge."""
    A, res = restore(A0 + eps * U, q, n, a, b)
    return None if res > TOL else A


def nearest_on_variety(A0, T, a, n, q):
    """Nearest point of the variety to T, by weighted least squares. The alternating projection of
    tff.restore stalls here: it fails on the same 21 directions at every step size and at 100000
    iterations, with the residual pinned at 2.6e-3, which is a stall and not slow convergence."""
    from scipy.optimize import least_squares
    iu = np.triu_indices(n)
    L = len(iu[0])

    def unpack(x):
        A = np.zeros((q, n, n))
        for k in range(q):
            M = np.zeros((n, n)); M[iu] = x[k * L:(k + 1) * L]
            A[k] = M + M.T - np.diag(np.diag(M))
        return A

    def F(x):
        A = unpack(x)
        return np.concatenate([(A[k] @ A[k] - A[k])[iu] for k in range(q)]
                              + [(A.sum(axis=0) - a * np.eye(n))[iu]])

    tx = np.concatenate([T[k][iu] for k in range(q)])
    r = lambda x: np.concatenate([1e5 * F(x), x - tx])
    sol = least_squares(r, tx, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
    return unpack(sol.x), float(np.abs(F(sol.x)).max()), float(np.linalg.norm(sol.x - tx))


def kind_of(B, i, lines, n, q):
    """cross: the two blocks lie on opposite sides of the vertex pair. same: the same side."""
    D = B[i]
    ks = [k for k in range(q) if np.abs(D[k]).max() > 0]
    u, v = [(x, y) for x in range(n) for y in range(x + 1, n) if abs(D[ks[0], x, y]) > 0][0]
    return 'cross' if len([k for k in ks if u in lines[k]]) == 1 else 'same'


def main():
    t0 = time.time()
    print("Which linearised tangent directions are actually tangent to the variety?\n")
    print("The idempotency and tightness constraints linearise to a space of dimension")
    print("sum over vertex pairs of (|K_ij| - 1). Whether the variety fills it is a different")
    print("question, and the answer decides what a second-order test even means.\n")

    for (nm, a, b, n, lines) in ([("Fano/Heawood", 3, 3, *heawood())]
                                 + ([] if QUICK else [("AG(2,3)", 4, 3, *ag23())])):
        q = len(lines)
        A0 = coord_family(n, lines)
        B = tangent_basis(n, lines)
        d = len(B)
        M = np.stack([D.reshape(-1) for D in B])
        rank = int(np.linalg.matrix_rank(M, tol=1e-9))
        so_n = n * (n - 1) // 2
        print(f"{nm}: n = {n}, q = {q}, (a,b) = ({a},{b})")
        print(f"  linearised tangent dimension {d} (rank {rank}), conjugation orbit dim {so_n}")
        print(f"{'kind':>8}{'count':>7}{'eps':>8}{'max dist':>11}{'dist/eps':>10}{'dist/eps^2':>12}"
              f"{'verdict':>12}")
        for kind in ('cross', 'same'):
            idx = [i for i in range(d) if kind_of(B, i, lines, n, q) == kind]
            take = idx[:2] if QUICK else idx[:8]
            for eps in ((0.08,) if QUICK else (0.08, 0.04, 0.02)):
                if time.time() - t0 > BUDGET_S:
                    print("  [budget reached]"); break
                ds = []
                for i in take:
                    _, res, dist = nearest_on_variety(A0, A0 + eps * B[i], a, n, q)
                    if res < 1e-9:
                        ds.append(dist)
                if not ds:
                    continue
                md = max(ds)
                verdict = 'TANGENT' if md / eps < 0.2 else 'not tangent'
                print(f"{kind:>8}{len(idx):>7}{eps:>8.3f}{md:>11.6f}{md / eps:>10.4f}"
                      f"{md / eps ** 2:>12.3f}{verdict:>12}")
        print()

    print("  A direction is tangent when the nearest point of the variety to A0 + eps D sits at")
    print("  distance O(eps^2); at distance O(eps) it is not. If the cross directions are tangent")
    print("  and the same-group ones are not, the variety does not fill the linearised space and")
    print("  the commuting point is a SINGULAR point of it. Since cross differences span the")
    print("  linearised space, the set of tangent directions is then not closed under")
    print("  subtraction: the tangent cone is not a linear subspace, and a Hessian on the")
    print("  linearised space is the wrong object. That is why code/curvature.py computes the")
    print("  second-order coefficient along explicit curves instead.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
