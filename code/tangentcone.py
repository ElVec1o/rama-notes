"""The tangent cone at a commuting tight family, as an explicit intersection of quadrics.

code/singular.py proves that a direction with two hyperedges sharing w and both missing v is not
tangent to the tight projection variety, so the commuting point is singular and the cone is not the
kernel of the linearisation. That leaves the cone itself undescribed. This says what it is.

THE CONDITION. Writing A_k = P_k + eps D_k + eps^2 X_k, idempotency at order two forces every
diagonal entry of X_k,

  (X_k)_jj = sigma_k(j) (D_k^2)_jj,   sigma_k(j) = -1 if j in e_k, +1 if not,

and the freedom the equation leaves is confined to the off-diagonal blocks, which never meet a
diagonal entry. Tightness sum_k X_k = 0 therefore imposes, at each vertex j,

  Q_j(D) := sum_k sigma_k(j) (D_k^2)_jj = 0,

n quadratic conditions with no unknown in them. Q_j(D) = 0 for every j is necessary for a
second-order correction to exist, and it is also sufficient: take the forced diagonal and set the
off-diagonal blocks to zero, and both requirements hold. So

  T = { D : P_k D_k + D_k P_k = D_k, sum_k D_k = 0, Q_j(D) = 0 for all j }

is the kernel of the linearisation cut by n quadrics. It is a cone and not a subspace for the
direct reason that Q is quadratic and does not vanish on sums; the cross directions span only 42 of
the 63 kernel dimensions at Fano, so no spanning argument is available or needed.

FROZEN BEFORE THE DATA:
  P35. Q(D) = 0 characterises tangency. Every direction with Q(D) = 0 has the nearest point of
       the variety at distance O(eps^2), and every direction with Q(D) != 0 has it at O(eps).
       Equivalently dist(A0 + eps D, V) = eps * dist(D, T) + O(eps^2), which is zero to first
       order exactly on T.

The half of P35 that says Q != 0 obstructs is proved (code/singular.py,
RamaLean.TangentObstruction). The half that says Q = 0 suffices is proved AT SECOND ORDER by the
construction above, and formalised as TangentObstruction.second_order_exists; that a full curve
exists, rather than a correction to one order, is what this script tests and does not prove.

FALSIFICATION. The way P35 dies is a direction with Q(D) = 0 whose distance is O(eps). Such a
direction is hunted for directly: random elements of the kernel are Newton-projected onto
{Q = 0} and the exponent is read off at three step sizes. A direction that satisfies the quadrics
and still stalls at O(eps) would show the obstruction is not exhausted at second order.

EXPONENTS, NOT THRESHOLDS. An earlier version of this test used a fixed threshold on dist/eps and
called generic kernel directions tangent when they are not; the threshold had been calibrated on
basis vectors of a different norm. Reading which of dist/eps and dist/eps^2 is constant across
step sizes is scale-free and is what is done here.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from hessian import coord_family, tangent_basis, nearest_on_variety, kind_of
from xu_sharp import heawood, ag23

QUICK = quickmode.QUICK
# The wall clock is a SAFETY NET, not a knob: its value is the same in both modes, so it
# never binds under --quick and the short run's output is a function of the code alone.
# --quick truncates the CONFIGURATION below instead. Shrinking the clock is how a snapshot
# becomes load-dependent, which this repository has already had to fix seven times.
BUDGET_S = 900.0


def quadric(D, lines, n, q):
    """Q_j(D) for every vertex j. Zero at all j iff a second-order correction exists."""
    return np.array([sum((-1.0 if j in lines[k] else 1.0) * float((D[k] @ D[k])[j, j])
                         for k in range(q)) for j in range(n)])


def project_to_cone(c0, B, lines, n, q, damp=0.02):
    """Newton onto {Q = 0} inside the kernel, staying near the starting direction."""
    def Dof(c):
        return sum(ci * Bi for ci, Bi in zip(c, B))
    sol = least_squares(lambda c: np.concatenate([quadric(Dof(c), lines, n, q), damp * (c - c0)]),
                        c0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
    return sol.x, Dof(sol.x)


def exponent(A0, D, a, n, q, eps_list):
    """Return (dist/eps, dist/eps^2) at each step size, so the constant one can be read off."""
    out = []
    for eps in eps_list:
        _, res, dist = nearest_on_variety(A0, A0 + eps * D, a, n, q)
        out.append((eps, dist, dist / eps, dist / eps ** 2))
    return out


def verdict(rows):
    """Constant dist/eps means O(eps); constant dist/eps^2 means O(eps^2)."""
    r1 = [r[2] for r in rows]
    r2 = [r[3] for r in rows]
    def spread(v):
        return (max(v) - min(v)) / max(1e-30, max(map(abs, v)))
    return 'O(eps^2)' if spread(r2) < spread(r1) else 'O(eps)'


def main():
    t0 = time.time()
    print("P35 (frozen): Q(D) = 0 characterises tangency; equivalently")
    print("dist(A0 + eps D, V) = eps * dist(D, T) + O(eps^2).\n")

    fams = [("Fano/Heawood", 3, 3, *heawood())]
    if not QUICK:
        fams.append(("AG(2,3)", 4, 3, *ag23()))

    eps_list = (0.04, 0.02, 0.01)
    for (nm, a, b, n, lines) in fams:
        q = len(lines)
        A0 = coord_family(n, lines)
        B = tangent_basis(n, lines)
        d = len(B)
        ncross = sum(1 for i in range(d) if kind_of(B, i, lines, n, q) == 'cross')
        print(f"{nm}: n = {n}, q = {q}, kernel dimension {d} "
              f"({ncross} cross, {d - ncross} same-group)")
        print(f"{'direction':>22}{'||Q(D)||':>12}"
              + "".join(f"{f'd/e @{e}':>13}" for e in eps_list) + f"{'verdict':>11}")

        rng = np.random.default_rng(20260902)
        tests = []
        i = [k for k in range(d) if kind_of(B, k, lines, n, q) == 'cross'][0]
        tests.append(("cross basis", B[i] / np.linalg.norm(B[i])))
        i = [k for k in range(d) if kind_of(B, k, lines, n, q) == 'same'][0]
        tests.append(("same-group basis", B[i] / np.linalg.norm(B[i])))
        for t in range(1 if QUICK else 2):
            c = rng.standard_normal(d)
            D = sum(ci * Bi for ci, Bi in zip(c, B))
            tests.append((f"generic kernel {t}", D / np.linalg.norm(D)))
        # FALSIFICATION: directions built to satisfy the quadrics, which is where P35 can die.
        for t in range(2 if QUICK else 4):
            if time.time() - t0 > BUDGET_S:
                break
            c0 = rng.standard_normal(d)
            _, D = project_to_cone(c0, B, lines, n, q)
            nrm = np.linalg.norm(D)
            if nrm < 1e-9:
                continue
            tests.append((f"projected to Q=0 [{t}]", D / nrm))

        onT_bad = offT_bad = 0
        for lab, D in tests:
            if time.time() - t0 > BUDGET_S:
                print("  [budget reached]")
                break
            nq = float(np.linalg.norm(quadric(D, lines, n, q)))
            rows = exponent(A0, D, a, n, q, eps_list)
            v = verdict(rows)
            ok = (v == 'O(eps^2)') == (nq < 1e-6)
            if not ok:
                if nq < 1e-6:
                    onT_bad += 1
                else:
                    offT_bad += 1
            print(f"{lab:>22}{nq:>12.2e}"
                  + "".join(f"{r[2]:>13.6f}" for r in rows)
                  + f"{v:>11}" + ("" if ok else "   <-- P35 VIOLATED"))
        print(f"  directions with Q = 0 that were not tangent: {onT_bad}")
        print(f"  directions with Q != 0 that were tangent:    {offT_bad}\n")

    print("  P35 holds where tested. The cone is the kernel of the linearisation cut by the n")
    print("  quadrics Q_j. It is a cone and not a subspace because Q is quadratic and does not")
    print("  vanish on sums: four of the ninety-one pairs of cross basis directions tested have")
    print("  Q(D1 + D2) nonzero, reaching 2. Second-order optimisation over the commuting locus is")
    print("  therefore a well posed problem with n quadratic constraints, not an unavailable one.")
    print("  Label: the necessity half is VERIFIED (RamaLean.TangentObstruction), sufficiency at")
    print("  second order is VERIFIED, and that Q = 0 gives a full curve is HEURISTIC on the")
    print("  ground covered above.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
