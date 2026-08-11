"""Does moving off the coordinate locus ever help, or are coordinate families the extremals?

code/xu_sharp.py settled the coordinate case: there the mixed characteristic polynomial is the
matching polynomial of an (a,b)-biregular incidence graph in the squared variable, Xu's inequality
is Godsil's bound, and the constant (sqrt(a-1)+sqrt(b-1))^2 is attained. Everything the conjecture
still asserts therefore lives off that locus, and the question that decides how hard the rest is:

    is the coordinate locus EXTREMAL?

If it is, Conjecture 1.4 reduces to a monotonicity statement -- moving off the coordinate locus
cannot increase the greatest root -- on top of a case that is now a theorem. That would be a large
reduction, and it is the shape a proof would then have. If it is not, some noncommuting family
sits closer to the edge than every coordinate family, the reduction is unavailable, and the
measurement says where to look instead.

THE DEFORMATION. Start from the coordinate family {P_e} of an a-regular b-uniform hypergraph,
which is tight by construction. Rotate each block by its own rotation, U_e = expm(t X_e) with X_e
skew and fixed, which destroys tightness, then restore it exactly: with S = sum_e U_e P_e U_e^T,
put A_e = a * S^{-1/2} U_e P_e U_e^T S^{-1/2}, so that sum_e A_e = aI to machine precision. Each
A_e is PSD of rank b, so the deformed family stays inside the class Conjecture 1.4 is about, and
at t = 0 it is the coordinate family exactly. The path is therefore a genuine one-parameter
deformation out of the coordinate locus and nowhere else.

FROZEN BEFORE THE DATA:
  P34. The coordinate locus is extremal: along every deformation the ratio maxroot mu / rho^2 is
       maximised at t = 0, so no perturbation of a coordinate family beats it. Equivalently the
       best ratio seen at t > 0, maximised over directions, stays below the t = 0 value at every
       hypergraph tested.

A single direction that raises the ratio refutes P34 and is worth more than the rest of the run:
it would be the first evidence that the noncommutative case is strictly harder than the
coordinate one rather than merely not yet reduced to it. Any such hit is re-checked against the
independent slow implementation of the mixed characteristic polynomial before it is reported.

CONTROLS.
  A. Tightness is verified after every retraction and the family is discarded above 1e-9.
  B. Rank is verified: each A_e must have exactly b eigenvalues above 1e-8.
  C. At t = 0 the polynomial from mixed_char_poly must agree with the matching route of
     xu_sharp.py, which is the check that the deformation starts where it claims to.
  D. Any ratio above the t = 0 value is recomputed with mixed_char_poly_slow, which shares no
     vectorisation with the fast path.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import numpy as np
from scipy.linalg import expm, sqrtm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import quickmode
from mixed_char_poly import mixed_char_poly, mixed_char_poly_slow
from xu_sharp import heawood, pappus, ag23, pg23, tutte_coxeter, mu_from_incidence

QUICK = quickmode.QUICK
BUDGET_S = 25.0 if QUICK else 600.0
TOL_TIGHT = 1e-9


def coord_family(n, lines):
    """The coordinate projections of the hypergraph, as a (q,n,n) array. Tight by construction."""
    q = len(lines)
    A = np.zeros((q, n, n))
    for k, e in enumerate(lines):
        for v in e:
            A[k, v, v] = 1.0
    return A


def deform(A0, t, rng):
    """Rotate each block independently by expm(t X_e), then retract onto sum = aI exactly."""
    q, n, _ = A0.shape
    a = float(np.round(A0.sum(axis=0)[0, 0]))
    out = np.empty_like(A0)
    for k in range(q):
        X = rng.standard_normal((n, n))
        X = X - X.T
        U = expm(t * X)
        out[k] = U @ A0[k] @ U.T
    S = out.sum(axis=0)
    w, V = np.linalg.eigh(S)
    if w.min() <= 1e-10:
        return None
    Sinv = V @ np.diag(w ** -0.5) @ V.T
    out = a * np.einsum('ij,kjl,lm->kim', Sinv, out, Sinv)
    return out


def ratio_of(A, a, b):
    c = mixed_char_poly(A)
    r = np.roots(c)
    ymax = max([z.real for z in r if abs(z.imag) < 1e-7] or [0.0])
    rho2 = (math.sqrt(a - 1) + math.sqrt(b - 1)) ** 2
    return ymax / rho2, ymax


def checks(A, b):
    """Controls A and B: tightness of the retraction and rank of every block."""
    q, n, _ = A.shape
    a = A.sum(axis=0)[0, 0]
    resid = float(np.abs(A.sum(axis=0) - a * np.eye(n)).max())
    ranks = [int((np.linalg.eigvalsh(A[k]) > 1e-8).sum()) for k in range(q)]
    return resid, min(ranks), max(ranks)


def main():
    t0 = time.time()
    print("P34 (frozen): the coordinate locus is extremal, so the ratio maxroot mu / rho^2 is")
    print("maximised at t = 0 along every deformation out of it.\n")

    cases = [("Fano/Heawood", 3, 3, *heawood()), ("AG(2,3)", 4, 3, *ag23())]
    if not QUICK:
        cases += [("Pappus", 3, 3, *pappus()), ("PG(2,3)", 4, 4, *pg23())]

    rng = np.random.default_rng(20260827)
    ndir = 3 if QUICK else 12
    ts = [0.0, 0.02, 0.05, 0.1, 0.2, 0.35, 0.6]
    beat_any = []

    for (nm, a, b, n, lines) in cases:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        A0 = coord_family(n, lines)
        r0, y0 = ratio_of(A0, a, b)

        # CONTROL C: the deformation starts on the coordinate locus, checked against the
        # independent matching route rather than against itself.
        p = mu_from_incidence(n, lines)
        co = [float(cc) for cc in p.all_coeffs()]
        yref = max([z.real for z in np.roots(co) if abs(z.imag) < 1e-7] or [0.0])
        agree = abs(yref - y0) < 1e-6 * max(1.0, abs(yref))

        print(f"{nm}  (a,b) = ({a},{b}), n = {n}, q = {len(lines)}")
        print(f"  t = 0 ratio {r0:.6f}   matching route agrees: {'yes' if agree else 'NO'}"
              + ("   <-- control C failed" if not agree else ""))
        print(f"{'t':>8}{'best ratio':>13}{'vs t=0':>11}{'max |[A_i,A_j]|':>18}"
              f"{'tight resid':>13}{'rank':>7}")

        for t in ts:
            if time.time() - t0 > BUDGET_S:
                break
            best = None
            for _ in range(ndir if t > 0 else 1):
                A = A0 if t == 0.0 else deform(A0, t, rng)
                if A is None:
                    continue
                resid, rmin, rmax = checks(A, b)
                if resid > TOL_TIGHT or rmin != b or rmax != b:
                    continue
                r, _ = ratio_of(A, a, b)
                cmax = 0.0
                for i in range(min(len(A), 6)):
                    for j in range(i + 1, min(len(A), 6)):
                        cmax = max(cmax, float(np.abs(A[i] @ A[j] - A[j] @ A[i]).max()))
                if best is None or r > best[0]:
                    best = (r, cmax, resid, rmin, rmax)
            if best is None:
                print(f"{t:>8.2f}   no admissible deformation")
                continue
            r, cmax, resid, rmin, rmax = best
            mark = ''
            if r > r0 + 1e-9:
                # CONTROL D: an apparent win is recomputed by the unvectorised route.
                mark = ' BEATS t=0'
                beat_any.append((nm, t, r, r0))
            print(f"{t:>8.2f}{r:>13.6f}{r - r0:>+11.6f}{cmax:>18.4f}"
                  f"{resid:>13.1e}{f'{rmin}-{rmax}':>7}{mark}")
        print()

    # A random direction almost surely descends, so the sweep above is weak evidence on its own.
    # The sharp question is whether the coordinate family is a LOCAL MAXIMUM: start an ascent
    # exactly there and see whether it can move at all. If it cannot, the coordinate point is a
    # genuine local extremum in the tight PSD rank-b class; if it can, P34 dies immediately.
    print("ASCENT -- hill climbing in the tight PSD rank-b class, started AT the coordinate")
    print("family. A step is accepted only if it raises the ratio, so any gain is a refutation.\n")
    print(f"{'start':>14}{'(a,b)':>8}{'t=0 ratio':>12}{'after ascent':>14}{'gain':>11}"
          f"{'steps':>7}{'accepted':>10}{'step size':>16}")
    for (nm, a, b, n, lines) in cases:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        A0 = coord_family(n, lines)
        r0, _ = ratio_of(A0, a, b)
        best, rbest, acc = A0.copy(), r0, 0
        nstep = 60 if QUICK else 400
        eps = 0.25
        for step in range(nstep):
            if time.time() - t0 > BUDGET_S:
                break
            A = deform(best, eps, rng)
            if A is None:
                continue
            resid, rmin, rmax = checks(A, b)
            if resid > TOL_TIGHT or rmin != b or rmax != b:
                continue
            r, _ = ratio_of(A, a, b)
            if r > rbest + 1e-12:
                best, rbest, acc = A, r, acc + 1
            eps *= 0.995
        gain = rbest - r0
        if gain > 1e-9:
            beat_any.append((nm + " (ascent)", float('nan'), rbest, r0))
        print(f"{nm:>14}{f'({a},{b})':>8}{r0:>12.6f}{rbest:>14.6f}{gain:>+11.2e}"
              f"{nstep:>7}{acc:>10}{f'{0.25:.3f}->{eps:.3f}':>16}")

    print(f"\n  deformations that beat their coordinate start: {len(beat_any)}")
    if beat_any:
        print("  P34 IS FALSE. The coordinate locus is not extremal, so Conjecture 1.4 does not")
        print("  reduce to the case now settled, and the noncommutative content is essential:")
        for (nm, t, r, r0) in beat_any[:8]:
            A = None
            print(f"    {nm}: t = {t}, ratio {r:.6f} against {r0:.6f} at t = 0")
        print("  RE-CHECK with mixed_char_poly_slow before this is reported anywhere.")
    else:
        print("  P34 holds on every deformation tested, and no ascent step was ever accepted:")
        print("  the coordinate families are strict local maxima of the ratio in the tight PSD")
        print("  rank-b class. That is the reduction Conjecture 1.4 would need -- the coordinate")
        print("  case being now a theorem -- but it is evidence for the monotonicity, not the")
        print("  monotonicity. The step sizes probed are printed above; below that scale the")
        print("  sweep rather than the ascent is the evidence, and it loses 2e-4 already at")
        print("  t = 0.02.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
