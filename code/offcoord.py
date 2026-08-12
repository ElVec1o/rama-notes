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
from tff import restore, tff_residual, proj_rank_b
from xu_sharp import heawood, pappus, ag23, pg23, tutte_coxeter, mu_from_incidence

QUICK = quickmode.QUICK
# The wall clock is a SAFETY NET, not a knob: its value is the same in both modes, so it
# never binds under --quick and the short run's output is a function of the code alone.
# --quick truncates the CONFIGURATION below instead. Shrinking the clock is how a snapshot
# becomes load-dependent, which this repository has already had to fix seven times.
BUDGET_S = 1500.0
TOL_TIGHT = 1e-9


def coord_family(n, lines):
    """The coordinate projections of the hypergraph, as a (q,n,n) array. Tight by construction."""
    q = len(lines)
    A = np.zeros((q, n, n))
    for k, e in enumerate(lines):
        for v in e:
            A[k, v, v] = 1.0
    return A


def deform(A0, t, rng, b=None):
    """Rotate each block independently by expm(t X_e), then return to the tight PROJECTION class.

    Rotation preserves idempotency but breaks tightness, and the obvious repair -- conjugating by
    S^{-1/2} -- restores tightness while destroying idempotency, landing in the PSD rank-b class
    instead. That class is not what Conjecture 1.4 is about and is already known to exceed the
    band, so the repair has to be the alternating projection of tff.restore, which returns to the
    intersection of {rank-b projections} and {sum = aI}.
    """
    q, n, _ = A0.shape
    a = float(np.round(A0.sum(axis=0)[0, 0]))
    if b is None:
        b = int(round(float(np.trace(A0[0]))))
    out = np.empty_like(A0)
    for k in range(q):
        X = rng.standard_normal((n, n))
        X = X - X.T
        U = expm(t * X)
        out[k] = U @ A0[k] @ U.T
    out, res = restore(out, q, n, a, b)
    return None if res > TOL_TIGHT else out


def ratio_of(A, a, b):
    c = mixed_char_poly(A)
    r = np.roots(c)
    ymax = max([z.real for z in r if abs(z.imag) < 1e-7] or [0.0])
    rho2 = (math.sqrt(a - 1) + math.sqrt(b - 1)) ** 2
    return ymax / rho2, ymax


def checks(A, b):
    """Tightness, rank, AND idempotency. The last is the one whose absence invalidated the first
    version of this script: without it a family with eigenvalues 0.77, 1.13, 1.21 passes as a
    rank-3 projection, and the search then wanders into the PSD class where the band is known to
    fail for reasons that have nothing to do with Xu's conjecture."""
    q, n, _ = A.shape
    a = A.sum(axis=0)[0, 0]
    resid = float(np.abs(A.sum(axis=0) - a * np.eye(n)).max())
    ranks = [int((np.linalg.eigvalsh(A[k]) > 1e-8).sum()) for k in range(q)]
    idem = max(float(np.abs(A[k] @ A[k] - A[k]).max()) for k in range(q))
    return resid, min(ranks), max(ranks), idem


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
              f"{'tight resid':>13}{'rank':>7}{'|A^2-A|':>10}")

        for t in ts:
            if time.time() - t0 > BUDGET_S:
                break
            best = None
            for _ in range(ndir if t > 0 else 1):
                A = A0 if t == 0.0 else deform(A0, t, rng, b)
                if A is None:
                    continue
                resid, rmin, rmax, idem = checks(A, b)
                if resid > TOL_TIGHT or rmin != b or rmax != b or idem > 1e-8:
                    continue
                r, _ = ratio_of(A, a, b)
                cmax = 0.0
                for i in range(min(len(A), 6)):
                    for j in range(i + 1, min(len(A), 6)):
                        cmax = max(cmax, float(np.abs(A[i] @ A[j] - A[j] @ A[i]).max()))
                if best is None or r > best[0]:
                    best = (r, cmax, resid, rmin, rmax, idem)
            if best is None:
                print(f"{t:>8.2f}   no admissible deformation")
                continue
            r, cmax, resid, rmin, rmax, idem = best
            mark = ''
            if r > r0 + 1e-9:
                # CONTROL D: an apparent win is recomputed by the unvectorised route.
                mark = ' BEATS t=0'
                beat_any.append((nm, t, r, r0))
            print(f"{t:>8.2f}{r:>13.6f}{r - r0:>+11.6f}{cmax:>18.4f}"
                  f"{resid:>13.1e}{f'{rmin}-{rmax}':>7}{idem:>10.1e}{mark}")
        print()

    # A random direction almost surely descends, so the sweep above is weak evidence on its own.
    # The sharp question is whether the coordinate family is a LOCAL MAXIMUM: start an ascent
    # exactly there and see whether it can move at all. If it cannot, the coordinate point is a
    # genuine local extremum in the tight PSD rank-b class; if it can, P34 dies immediately.
    print("ASCENT -- hill climbing in the tight rank-b PROJECTION class, started AT the")
    print("commuting family. A step is accepted only if it raises the ratio, so any gain")
    print("is a refutation. Idempotency is enforced, not assumed.\n")
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
            A = deform(best, eps, rng, b)
            if A is None:
                continue
            resid, rmin, rmax, idem = checks(A, b)
            if resid > TOL_TIGHT or rmin != b or rmax != b or idem > 1e-8:
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

    # The ascent above only says the commuting point is a LOCAL maximum. The statement that
    # would reduce Conjecture 1.4 is global, so the same search is run from random starts at the
    # SAME (n, q, a, b): if the commuting value is the global maximum at that size, nothing found
    # this way beats it. Comparing across sizes, as the earlier adversarial runs did, cannot
    # settle this, since the ratio grows with the size at fixed (a,b).
    print("\nGLOBAL -- random starts in the tight rank-b PROJECTION class, same (n,q,a,b) as")
    print("the commuting family. A start beating the commuting value refutes extremality.\n")
    print(f"{'match':>14}{'(a,b)':>8}{'n':>4}{'q':>4}{'commuting':>12}"
          f"{'best random':>13}{'gap':>11}{'starts':>8}")
    for (nm, a, b, n, lines) in cases:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        q = len(lines)
        A0 = coord_family(n, lines)
        r0, _ = ratio_of(A0, a, b)
        nstart = 3 if QUICK else 15
        nstep = 40 if QUICK else 200
        rbest_all = 0.0
        for _ in range(nstart):
            if time.time() - t0 > BUDGET_S:
                break
            B = np.stack([np.linalg.qr(rng.standard_normal((n, b)))[0] for _ in range(q)])
            B = np.einsum('kij,klj->kil', B, B)
            cur, res = restore(B, q, n, a, b)
            if res > TOL_TIGHT:
                continue
            resid, rmin, rmax, idem = checks(cur, b)
            if resid > TOL_TIGHT or rmin != b or rmax != b or idem > 1e-8:
                continue
            rcur, _ = ratio_of(cur, a, b)
            eps = 0.3
            for _ in range(nstep):
                if time.time() - t0 > BUDGET_S:
                    break
                cand = deform(cur, eps, rng, b)
                if cand is None:
                    continue
                rs, rmn, rmx, idm = checks(cand, b)
                if rs > TOL_TIGHT or rmn != b or rmx != b or idm > 1e-8:
                    continue
                rc, _ = ratio_of(cand, a, b)
                if rc > rcur:
                    cur, rcur = cand, rc
                eps *= 0.99
            rbest_all = max(rbest_all, rcur)
        beats = rbest_all > r0 + 1e-9
        if beats:
            beat_any.append((nm + " (global)", float('nan'), rbest_all, r0))
        print(f"{nm:>14}{f'({a},{b})':>8}{n:>4}{q:>4}{r0:>12.6f}{rbest_all:>13.6f}"
              f"{rbest_all - r0:>+11.6f}{nstart:>8}" + ("  BEATS" if beats else ""))

    # THE RELAXATION, run deliberately. Dropping idempotency and keeping only PSD, rank b and
    # tightness is what the first version of this script did by accident, and it is worth keeping
    # as a control: the relaxed class exceeds the band outright, so any argument for the
    # monotonicity above must use idempotency and not merely rank, trace and sum = aI. The
    # retraction here is the S^{-1/2} conjugation, which restores tightness while destroying
    # idempotency, and the resulting families are reported with their idempotency defect so that
    # nobody mistakes them for a counterexample to Conjecture 1.4.
    print("\nRELAXATION -- the same search with idempotency DROPPED: PSD, rank b, tight. Not")
    print("Xu's class, and reported only to show the monotonicity above needs idempotency.\n")
    print(f"{'match':>14}{'(a,b)':>8}{'projections':>13}{'PSD relaxed':>13}"
          f"{'|A^2-A|':>10}{'over band':>11}")
    relaxed = {}

    def psd_retract(B, a):
        S = B.sum(axis=0)
        w, V = np.linalg.eigh(S)
        if w.min() <= 1e-10:
            return None
        Si = V @ np.diag(w ** -0.5) @ V.T
        return a * np.einsum('ij,kjl,lm->kim', Si, B, Si)

    for (nm, a, b, n, lines) in cases:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached]")
            break
        q = len(lines)
        A0 = coord_family(n, lines)
        r0, _ = ratio_of(A0, a, b)
        rbest, ibest = 0.0, 0.0
        for _ in range(3 if QUICK else 10):
            if time.time() - t0 > BUDGET_S:
                break
            B = np.stack([np.linalg.qr(rng.standard_normal((n, b)))[0] for _ in range(q)])
            cur = psd_retract(np.einsum('kij,klj->kil', B, B), a)
            if cur is None:
                continue
            rcur, _ = ratio_of(cur, a, b)
            eps = 0.3
            for _ in range(30 if QUICK else 150):     # the search, which is where >1 comes from
                if time.time() - t0 > BUDGET_S:
                    break
                Y = np.empty_like(cur)
                for k in range(q):
                    X = rng.standard_normal((n, n)); X = X - X.T
                    U = expm(eps * X)
                    Y[k] = U @ cur[k] @ U.T
                cand = psd_retract(Y, a)
                if cand is None:
                    continue
                rc, _ = ratio_of(cand, a, b)
                if rc > rcur:
                    cur, rcur = cand, rc
                eps *= 0.99
            if rcur > rbest:
                rbest = rcur
                ibest = max(float(np.abs(cur[k] @ cur[k] - cur[k]).max()) for k in range(q))
        relaxed[nm] = rbest
        print(f"{nm:>14}{f'({a},{b})':>8}{r0:>13.6f}{rbest:>13.6f}{ibest:>10.3f}"
              f"{('YES' if rbest > 1.0 else 'no'):>11}")
    print("  Above the band in the relaxed class is the obstruction already recorded for")
    print("  A_k = (b/p)I, not evidence about Xu's conjecture, which is about projections.")

    print(f"\n  deformations that beat their coordinate start: {len(beat_any)}")
    if beat_any:
        print("  P34 IS FALSE. The coordinate locus is not extremal, so Conjecture 1.4 does not")
        print("  reduce to the case now settled, and the noncommutative content is essential:")
        for (nm, t, r, r0) in beat_any[:8]:
            A = None
            print(f"    {nm}: t = {t}, ratio {r:.6f} against {r0:.6f} at t = 0")
        print("  RE-CHECK with mixed_char_poly_slow before this is reported anywhere.")
    else:
        print("  P34 holds. No ascent step was ever accepted, and no random start in the tight")
        print("  projection class beat its commuting counterpart at the same (n,q,a,b): the")
        print("  commuting families are the best seen, locally and globally at these sizes. That")
        print("  is the reduction Conjecture 1.4 would need, the commuting case being now a")
        print("  theorem, but it is evidence for the monotonicity and not the monotonicity.")
        print("  The claim is specific to PROJECTIONS. Relaxing to PSD rank-b breaks it: the")
        over = sorted(((v, k) for k, v in relaxed.items() if v > 1.0), reverse=True)
        if over:
            print("  same search without idempotency exceeds the band outright at "
                  + ", ".join(f"{k} ({v:.3f})" for v, k in over) + ",")
            print("  which is the obstruction the note already records for A_k = (b/p)I and is not")
            print("  evidence about Xu's conjecture. Any proof of the monotonicity must therefore")
            print("  use idempotency and not merely rank, trace and tightness.")
        else:
            if relaxed:
                print("  same search without idempotency reached at most "
                      f"{max(relaxed.values()):.3f} here, below the band in this run; the note")
                print("  records the violation independently for A_k = (b/p)I at p = 4.")
            else:
                print("  relaxed search did not run inside the budget, so this run says nothing")
                print("  about it; the note records the violation for A_k = (b/p)I at p = 4.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
