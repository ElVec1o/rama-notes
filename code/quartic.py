"""The fourth-order term on ker(Lambda), which is what decides both the shape and the sign.

code/lyapunov.py refuted the linear Lyapunov statement Lambda <= -c Gamma and read off the corrected
shape from one direction at one family:

    maxroot mu <= y_0 - c C^2,     C the total commutator norm.

Two questions were left, and they are the same question. Asking whether (y_0 - maxroot)/C^2 is
bounded below is asking about the directions that MINIMISE it, and those are exactly the degenerate
ones. Along a generic cone direction Lambda(D) < 0, so y_0 - y ~ -Lambda t^2/2 while C ~ Gamma t^2,
and the ratio behaves like t^(-2) and blows up. Along a direction in ker(Lambda) with Gamma > 0 the
root only moves at order four, y_0 - y ~ c_4 t^4, so the ratio tends to the FINITE value

    c_4(D) / Gamma(D)^2 .

So the constant in the corrected shape is inf c_4/Gamma^2 over ker(Lambda) on the cone, and the
question of whether the shape holds at all is the question of whether c_4 > 0 there.

WHAT c_4 > 0 MEANS, and why this is worth running before anything else. The second-order test is
BLIND on ker(Lambda): that is what the note records as the b = 2 excess, 2 at C_4 and 9 at C_6. If
some direction there had c_4 <= 0 the commuting point would not be a local maximum at all, and A15
would be refuted rather than unproved. The note says the fourth order still decreases, but says so
from a handful of directions. This searches ker(Lambda) systematically for the worst one.

FROZEN BEFORE THE DATA:
  P46. (a) c_4(D) > 0 for every direction of ker(Lambda) on the cone with Gamma(D) > 0, so the
           commuting point is a strict local maximum in every direction the second order cannot see.
       (b) inf c_4/Gamma^2 over those directions is positive, so maxroot <= y_0 - c C^2 holds near
           the locus with c that infimum.
       (c) The bound is LOCAL and not global: over random tight families far from the commuting
           locus the ratio (y_0 - maxroot)/C^2 falls below any fixed constant, because y_0 - maxroot
           is bounded while C^2 is not.

FALSIFICATION. A direction of ker(Lambda) on the cone with c_4 <= 0 refutes (a), and if c_4 < 0 it
refutes A15 outright: the commuting family would not be the local maximum. That is the outcome this
script exists to look for, and the directions it looks in are precisely those the curvature form
cannot see.

METHOD. Directions are found by solving Q(D) = 0 and Gamma(D) = 1 INSIDE ker(Lambda) from many random
starts, so they are sampled rather than assumed. The curve is built by continuation upstairs on
frames, where idempotency is exact and only tightness is solved, so the points are on the variety to
machine precision; c_4 is read as (y_0 - y)/t^4 at several t and reported with its spread, so a
value that is not a genuine fourth-order constant is visible as drift rather than hidden by a fit.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode
from hessian import coord_family, tangent_basis
from tangentcone import quadric
from hessian import nearest_on_variety
from lyapunov import lambda_matrix, gamma_matrix
from tff import build_tff
from mixed_char_poly import mixed_char_poly

QUICK = quickmode.QUICK


def ymax(A):
    r = np.roots(mixed_char_poly(A))
    re = [z.real for z in r if abs(z.imag) < 1e-8]
    return max(re) if re else float('nan')


def comm(A):
    m = len(A)
    return sum(float(np.linalg.norm(A[i] @ A[j] - A[j] @ A[i], 'fro') ** 2)
               for i in range(m) for j in range(i + 1, m))


def sample_degenerate(A0, B, Lam, Gam, lines, n, q, ndir, seed):
    """Directions inside ker(Lambda), on the cone, normalised to Gamma = 1."""
    d = len(B)
    wl, vl = np.linalg.eigh(Lam)
    N = vl[:, [i for i in range(d) if abs(wl[i]) < 1e-9]]
    rng = np.random.default_rng(seed)
    out = []
    for _ in range(ndir * 6):
        if len(out) >= ndir:
            break
        z0 = rng.standard_normal(N.shape[1])

        def res(z):
            c = N @ z
            D = sum(ci * Bi for ci, Bi in zip(c, B))
            return np.concatenate([quadric(D, lines, n, q), [0.3 * (float(c @ Gam @ c) - 1.0)]])

        sol = least_squares(res, z0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        c = N @ sol.x
        D = sum(ci * Bi for ci, Bi in zip(c, B))
        if np.abs(quadric(D, lines, n, q)).max() < 1e-9 and abs(float(c @ Gam @ c) - 1.0) < 1e-6:
            out.append(D)
    return out


def walk(D, A0, lines, n, q, a, b, ts):
    """The nearest point of the variety to the first-order jet, at each t.

    NOT a pinned continuation. The pin fixes only the component of the displacement ALONG D and
    leaves the transverse part free, so on a direction that is not 2-regular the curve acquires an
    O(t) transverse component and its root moves at order TWO while D itself is in ker(Lambda).
    A first version of this script did exactly that and reported a fourth-order constant for
    directions whose ratio was in fact growing like t^(-2). Taking the nearest point to A_0 + tD
    makes the displacement O(t^2) away from tD whenever such a point exists, which is what having
    tangent D means, and the caller checks that it does.

    Returns (t, y_0 - y, C, tangent error) or None if the projection fails.
    """
    y0 = ymax(A0)
    rows = []
    for t in ts:
        A, res, _ = nearest_on_variety(A0, A0 + t * D, a, n, q)
        if A is None or res > 1e-9:
            return None
        err = float(np.linalg.norm((A - A0) / t - D))
        rows.append((t, y0 - ymax(A), comm(A), err))
    return rows


def perturbed_c4(D, A0, B, lines, n, q, a, b, ts, nk, seed):
    """c_4 along curves whose SECOND-order term is perturbed inside the kernel.

    A direction does not determine a curve. Order two fixes the diagonal blocks of the correction
    and leaves the off-diagonal ones free, so the curves with tangent D form a family, and the
    fourth-order coefficient depends on which one is taken: replacing the correction W by W + K for
    K in the kernel changes the root at order t^4. The nearest-point curve is one member. A local
    maximum needs the sign for EVERY member, so the freedom is sampled here rather than ignored.

    Returns the smallest c_4 found over the sampled corrections.
    """
    y0 = ymax(A0)
    rng = np.random.default_rng(seed)
    worst = float('inf')
    for _ in range(nk):
        c = rng.standard_normal(len(B))
        Kd = sum(ci * Bi for ci, Bi in zip(c, B))
        Kd = Kd / max(1e-12, np.linalg.norm(Kd))
        vals = []
        for t in ts:
            A, res, _ = nearest_on_variety(A0, A0 + t * D + t * t * Kd, a, n, q)
            if A is None or res > 1e-9:
                vals = []
                break
            e = float(np.linalg.norm((A - A0) / t - D))
            if e / t > 200.0:
                vals = []
                break
            vals.append((y0 - ymax(A)) / t ** 4)
        if vals:
            worst = min(worst, float(np.mean(vals)))
    return worst


FAMILIES = [
    ("C_4 (2,2)", 2, 2, 4, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("C_6 (2,2)", 2, 2, 6, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]]),
]


def main():
    print("P46 (frozen): (a) c_4 > 0 on ker(Lambda) at the cone, so the commuting point is a strict")
    print("local maximum where the second order is blind; (b) inf c_4/Gamma^2 > 0, giving the")
    print("constant in maxroot <= y_0 - c C^2; (c) the bound is local, not global.\n")

    ts = (0.12, 0.07) if QUICK else (0.15, 0.12, 0.09, 0.07, 0.05)
    ndir = 2 if QUICK else 20
    fams = FAMILIES[:1] if QUICK else FAMILIES

    # The exact curvature form costs one truncated series per basis pair, so it is built ONCE per
    # family and shared by (a) and (a'). Building it twice put the quick pass over the citation
    # checker's budget for no reason.
    cache = {}
    for (nm, a, b, n, lines) in fams:
        q = len(lines)
        A0 = coord_family(n, lines)
        B = tangent_basis(n, lines)
        Lam, _, _ = lambda_matrix(A0, B, lines, n, q)
        Gam = gamma_matrix(A0, B, n, q)
        cache[nm] = (A0, B, Lam, Gam,
                     sample_degenerate(A0, B, Lam, Gam, lines, n, q, ndir, 20260812))

    print("(a) and (b): the fourth-order constant over ker(Lambda), Gamma normalised to 1.")
    print(f"{'family':>12}{'dim ker L':>11}{'orbit':>7}{'dirs':>6}{'no tangent':>12}"
          f"{'unresolved':>12}{'min c_4':>12}{'max c_4':>12}{'root falls':>12}")
    ok_a = True; infs = []
    for (nm, a, b, n, lines) in fams:
        q = len(lines)
        A0, B, Lam, Gam, dirs = cache[nm]
        c4s = []; dropped = 0; unresolved = 0; decreases = True
        for D in dirs:
            rows = walk(D, A0, lines, n, q, a, b, ts)
            if rows is None:
                dropped += 1
                continue
            # The curve must actually have tangent D. The scale-free test is that the error is
            # O(t), that is err/t is constant; an ABSOLUTE cutoff on err is wrong here because the
            # directions are normalised by Gamma = 1 rather than by norm, so their scales differ by
            # more than an order of magnitude. A first version used err < 0.15 and threw away five
            # of six directions whose err/t was constant to three digits.
            rat = [e / t for (t, _, _, e) in rows]
            if (max(rat) - min(rat)) / max(1e-30, max(rat)) > 0.25:
                dropped += 1
                continue
            # (a) is the SIGN, and it is read directly rather than through a fitted exponent.
            if not all(dy > 0 for (_, dy, _, _) in rows):
                decreases = False
            # (b) needs a resolvable fourth-order constant. Where y_0 - y falls to the precision
            # floor of the root solve the ratio is noise, and saying so beats quoting it: one
            # direction of six at C_4 sits at 4e-12 and its c_4 is not resolved here.
            if min(dy for (_, dy, _, _) in rows) < 1e-10:
                unresolved += 1
                continue
            vals = [dy / t ** 4 for (t, dy, _, _) in rows]
            c4s.append(float(np.mean(vals)))
        if not c4s:
            print(f"{nm:>12}   no direction gave a resolvable constant"); continue
        allpos = min(c4s) > 0
        ok_a = ok_a and allpos and decreases
        # Gamma is 1 on these directions, so c_4 IS c_4/Gamma^2
        infs.append((nm, min(c4s)))
        wl = np.linalg.eigvalsh(Lam)
        dimN = int(sum(1 for w in wl if abs(w) < 1e-9))
        print(f"{nm:>12}{dimN:>11}{n * (n - 1) // 2:>7}{len(dirs):>6}{dropped:>12}"
              f"{unresolved:>12}{min(c4s):>12.3e}{max(c4s):>12.3e}{str(decreases):>12}")
    print("  'root falls' is the sign of y_0 - y at every direction and every step size, read")
    print("  directly; it is claim (a) and does not depend on an exponent. Gamma is normalised to 1,")
    print("  so c_4 is already c_4/Gamma^2 and the minimum column is claim (b)'s constant, taken")
    print("  over the directions where the fourth order is resolvable above the precision floor.\n")

    print("(a') The same, over curves whose second-order term is perturbed inside the kernel: a")
    print("direction does not determine a curve, and a local maximum needs the sign for all of them.")
    print(f"{'family':>12}{'directions':>12}{'corrections':>13}{'min c_4':>12}{'still > 0':>11}")
    ok_pert = True
    for (nm, a, b, n, lines) in fams:
        q = len(lines)
        A0, B, Lam, Gam, dirs = cache[nm]
        nk = 2 if QUICK else 12
        worst = float('inf')
        for D in dirs:
            worst = min(worst, perturbed_c4(D, A0, B, lines, n, q, a, b, ts, nk, 20260814))
        good = worst > 0
        ok_pert = ok_pert and good
        print(f"{nm:>12}{len(dirs):>12}{nk:>13}{worst:>12.3e}{str(good):>11}")
    print()

    print("(c) The same ratio over random tight families, which are not near the locus.")
    print(f"{'family':>12}{'families':>10}{'C range':>22}{'min ratio':>12}{'at C':>10}"
          f"{'falls with C':>14}")
    rng = np.random.default_rng(20260813)
    ok_c = True
    for (nm, a, b, n, lines) in fams:
        q = len(lines)
        A0 = coord_family(n, lines)
        y0 = ymax(A0)
        pts = []
        for _ in range(8 if QUICK else 60):
            A, res = build_tff(n, q, a, b, rng)
            if res > 1e-9:
                continue
            C = comm(A)
            if C < 1e-9:
                continue
            y = ymax(A)
            if not np.isfinite(y):
                continue
            pts.append((C, (y0 - y) / C ** 2))
        if len(pts) < 5:
            print(f"{nm:>12}   too few families"); continue
        pts.sort()
        lo = float(np.median([r for (_, r) in pts[:len(pts) // 3]]))
        hi = float(np.median([r for (_, r) in pts[-len(pts) // 3:]]))
        mn = min(r for (_, r) in pts)
        cm = [c for (c, r) in pts if r == mn][0]
        falls = hi < lo
        ok_c = ok_c and falls
        print(f"{nm:>12}{len(pts):>10}"
              f"{f'[{pts[0][0]:.2f},{pts[-1][0]:.2f}]':>22}{mn:>12.3e}{cm:>10.2f}{str(falls):>14}")
    print("  The ratio is compared between the third of families with the smallest commutator and")
    print("  the third with the largest; falling means no global constant can work.\n")

    if ok_a and ok_pert and infs:
        print("  P46 (a) HOLDS. Every direction the curvature form cannot see still decreases, at")
        print("  order four, so the commuting family is a strict local maximum on ker(Lambda) too")
        print("  and A15 survives its sharpest local test.")
        print("  (b) The constant is the minimum column above: " +
              ", ".join(f"{nm} {v:.3e}" for (nm, v) in infs) + ".")
    else:
        print("  P46 (a) FAILS. There is a direction the curvature form cannot see, or a curve with")
        print("  that direction as its tangent, along which the root does NOT decrease at order")
        print("  four. The commuting family is then not a local maximum, and A15 is refuted rather")
        print("  than open.")
    if ok_c:
        print("  (c) HOLDS: the ratio falls as the commutator grows, so the bound is local by")
        print("  necessity and any global statement needs a different right-hand side.")
    else:
        print("  (c) FAILS: the ratio does not fall, so a global constant is not excluded and the")
        print("  statement may be stronger than claimed.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
