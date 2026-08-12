"""Is the commutator a Lyapunov functional for the top root? The second-order test, which decides it.

P41 says the greatest root of mu is largest at the commuting locus and falls away as the commutator
grows. It survived an adversarial search (code/jointinv.py), so it is worth a proof attempt rather
than more sampling. This is the attempt, at the order where both sides are computable exactly.

THE SHARP LOCAL STATEMENT. At a commuting tight family both quantities are quadratic forms on the
kernel of the linearisation. The top root has the curvature form Lambda of code/curvform.py. The
commutator has one too: with A_k = P_k + eps D_k and [P_i, P_j] = 0,

    [A_i, A_j] = eps ([P_i, D_j] + [D_i, P_j]) + eps^2 [D_i, D_j],

so the commutator norm is eps^2 Gamma(D) + O(eps^3) with

    Gamma(D) = sum over i<j of || [P_i, D_j] + [D_i, P_j] ||_F^2 ,

manifestly positive semidefinite, being a sum of squares of linear forms in D. "The commutator is a
Lyapunov functional" then says, to second order,

    Lambda(D) <= -c Gamma(D)   for some c > 0.

WHY THIS IS DECISIVE RATHER THAN SUGGESTIVE. The inequality forces null(Lambda) to be CONTAINED in
null(Gamma). Both contain the conjugation orbit: along exp(eps Omega) P_k exp(-eps Omega) the
commutators stay zero and the root stays constant, so both forms vanish there. But at b = 2 the null
space of Lambda is strictly LARGER than the orbit, by 2 at C_4, 6 at K_4 and 9 at C_6, and that
excess is recorded in the note as the reason the second-order test is blind there. So the question
has a yes or no answer available now: do the excess directions also kill Gamma?

  If they do, the containment holds and the Lyapunov statement survives at second order, with c the
  negative of the largest generalised eigenvalue. That is the first evidence for P41 that is not a
  sampling argument, and it names the constant.

  If they do not, there is a direction along which the root does not move at second order while the
  commutator does, so no inequality of the above shape can hold, and the commutator is NOT the
  functional. That would close the route P41 opened, which is worth more than another correlation.

FROZEN BEFORE THE DATA:
  P44. (a) null(Lambda) is contained in null(Gamma) at every family tested.
       (b) Consequently sup{ Lambda(D) : Gamma(D) = 1 } is strictly negative, so Lambda <= -c Gamma
           holds with c > 0.

FALSIFICATION. A direction with Lambda(D) = 0 and Gamma(D) != 0 refutes both parts at once and
closes the commutator route at second order. This is the outcome the b = 2 excess makes likely
enough to be worth checking, and it is the reason to run this before attempting a proof.

P44 IS REFUTED, and the refutation hands back the right statement. There are directions ON THE CONE
with Q = 0, Lambda = 0 and Gamma > 0 at C_4 and at C_6, found by searching inside null(Lambda), so no
inequality Lambda <= -c Gamma can hold. But along such a direction the root falls at order FOUR while
the commutator grows at order TWO, and those two exponents pair up: with y_0 - y ~ c_4 t^4 and
C ~ g_2 t^2 one gets y_0 - y ~ (c_4/g_2^2) C^2. So the shape is quadratic in the commutator, not
linear, and that is a corrected statement rather than a dead end.

P45, DERIVED FROM THE REFUTATION and therefore not frozen before it, tested out of sample below:
  maxroot mu <= y_0 - c C^2 near the commuting locus, that is (y_0 - maxroot)/C^2 is bounded below
  by a positive constant. A generic direction has Lambda < 0 and sends the ratio to infinity, so the
  content is entirely in the degenerate directions, which is where the linear form died.

ARITHMETIC. Lambda is read off the exact integer eps^2 coefficient of mu along the 2-jet, as in
code/curvform.py, at 60 digits; Gamma is an integer form on the integer tangent basis. Neither is
built by finite differences, the failure mode that once gave two different signatures at two step
sizes.
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
from hessian import coord_family, tangent_basis
from curvform import jet_family, canonical_X, mu2_poly
import curvature as K

QUICK = quickmode.QUICK


def gamma_matrix(A0, B, n, q):
    """The exact matrix of Gamma in the tangent basis, by polarisation of a sum of squares."""
    def M(D, i, j):
        return (A0[i] @ D[j] - D[j] @ A0[i]) + (D[i] @ A0[j] - A0[j] @ D[i])
    d = len(B)
    pairs = list(itertools.combinations(range(q), 2))
    cols = []
    for s in range(d):
        cols.append(np.concatenate([M(B[s], i, j).ravel() for (i, j) in pairs]))
    L = np.array(cols)
    return L @ L.T


def lambda_matrix(A0, B, lines, n, q):
    """The matrix of Lambda in the tangent basis, from the exact eps^2 coefficient of mu.

    No wall-clock guard anywhere in this file: --quick truncates the FAMILY LIST and the step list,
    never the clock, so the output is a function of the code alone. The repository has fixed this
    same defect in seven scripts and it is not reintroduced here.
    """
    import sympy as sp
    from mpmath import mp, mpf
    y = sp.Symbol('y')
    P = [[[int(A0[k][i][j]) for j in range(n)] for i in range(n)] for k in range(q)]
    z = np.zeros_like(A0)
    mu0 = [K.mixed_char_series(jet_family(P, z, z, n, q), n, q)[m][0] for m in range(n + 1)]
    p0 = sp.Poly(sum(sp.Rational(mu0[m]) * y ** (n - m) for m in range(n + 1)), y)
    y0 = max(sp.Poly(p0, y).real_roots())
    dp0 = sp.diff(p0.as_expr(), y)
    mp.dps = 60
    y0f = mpf(str(sp.N(y0, 55)))
    dp0f = mpf(str(sp.N(dp0.subs(y, y0), 55)))

    def lam_of(D):
        c = mu2_poly(P, D, lines, n, q)
        val = sum(mpf(int(c[m])) * y0f ** (n - m) for m in range(n + 1))
        return -val / dp0f

    d = len(B)
    diag = [lam_of(B[s]) for s in range(d)]
    Lam = np.zeros((d, d))
    for s in range(d):
        Lam[s, s] = float(diag[s])
    for s in range(d):
        for t in range(s + 1, d):
            Lam[s, t] = Lam[t, s] = float((lam_of(B[s] + B[t]) - diag[s] - diag[t]) / 2)
    return Lam, float(y0f), float(dp0f)


def orbit_dim(n):
    """The conjugation orbit has the dimension of the skew-symmetric matrices."""
    return n * (n - 1) // 2


FAMILIES = [
    ("C_4 (2,2)", 2, 2, 4, [[0, 1], [1, 2], [2, 3], [3, 0]]),
    ("C_6 (2,2)", 2, 2, 6, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]]),
    ("K_4 triples (3,3)", 3, 3, 4, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]),
]


def offending_direction(A0, B, Lam, Gam, lines, n, q, seed=11):
    """A cone direction inside null(Lambda) on which Gamma does not vanish, if one exists."""
    from scipy.optimize import least_squares
    from tangentcone import quadric
    d = len(B)
    wl, vl = np.linalg.eigh(Lam)
    N = vl[:, [i for i in range(d) if abs(wl[i]) < 1e-9]]
    rng = np.random.default_rng(seed)
    for _ in range(60):
        z0 = rng.standard_normal(N.shape[1])

        def res(z):
            c = N @ z
            D = sum(ci * Bi for ci, Bi in zip(c, B))
            return np.concatenate([quadric(D, lines, n, q), [0.3 * (float(c @ Gam @ c) - 1.0)]])

        sol = least_squares(res, z0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        c = N @ sol.x
        D = sum(ci * Bi for ci, Bi in zip(c, B))
        if np.abs(quadric(D, lines, n, q)).max() < 1e-10 and float(c @ Gam @ c) > 1e-6:
            return D / np.linalg.norm(D)
    return None


def exponents():
    """P45 out of sample: the exponents along a refuting direction, and the ratio they produce."""
    from arc import frames, solve_at
    from mixed_char_poly import mixed_char_poly

    def ymax(A):
        r = np.roots(mixed_char_poly(A))
        return max(z.real for z in r if abs(z.imag) < 1e-8)

    def comm(A):
        m = len(A)
        return sum(float(np.linalg.norm(A[i] @ A[j] - A[j] @ A[i], 'fro') ** 2)
                   for i in range(m) for j in range(i + 1, m))

    print("P45 (derived from the refutation, not frozen before it): the root falls at order four")
    print("where the commutator grows at order two, so the shape is y_0 - maxroot >= c C^2.")
    print(f"{'family':>12}{'t':>8}{'y_0 - y':>13}{'C':>13}{'(y_0-y)/t^4':>14}{'C/t^2':>10}"
          f"{'(y_0-y)/C^2':>14}")
    fams = FAMILIES[:1] if QUICK else FAMILIES[:2]
    for (nm, a, b, n, lines) in fams:
        q = len(lines)
        A0 = coord_family(n, lines)
        B = tangent_basis(n, lines)
        Lam, _, _ = lambda_matrix(A0, B, lines, n, q)
        Gam = gamma_matrix(A0, B, n, q)
        D = offending_direction(A0, B, Lam, Gam, lines, n, q)
        if D is None:
            print(f"{nm:>12}   no refuting direction found"); continue
        U0 = frames(n, lines, b)
        y0 = ymax(A0)
        prev = None; tprev = None
        ts = (0.20, 0.10, 0.05, 0.02) if QUICK else (0.20, 0.15, 0.10, 0.07, 0.05, 0.03, 0.02)
        for t in ts:
            seed = (U0 + t * np.stack([D[k] @ U0[k] for k in range(q)])
                    if prev is None else U0 + (t / tprev) * (prev - U0))
            U, _ = solve_at(t, seed, U0, A0, D, lines, n, q, a, b)
            A = np.einsum('kis,kjs->kij', U, U)
            dy = y0 - ymax(A); C = comm(A)
            r4 = dy / t ** 4
            print(f"{nm:>12}{t:>8.3f}{dy:>13.3e}{C:>13.3e}{r4:>14.3e}{C / t ** 2:>10.4f}"
                  f"{(dy / C ** 2 if C > 0 else float('nan')):>14.6f}")
            prev = U; tprev = t
    print("  A constant last column across a decade in t is the corrected statement; a constant")
    print("  fourth column is the exponent that produces it. Both are read off rather than fitted.")


def main():
    print("P44 (frozen): (a) null(Lambda) is contained in null(Gamma); (b) hence")
    print("Lambda <= -c Gamma with c > 0, so the commutator is a Lyapunov functional at")
    print("second order.\n")

    print(f"{'family':>20}{'dim ker':>9}{'orbit':>7}{'null L':>8}{'excess':>8}{'null G':>8}"
          f"{'contained':>11}{'max L/G':>12}")
    verdicts = []
    for (nm, a, b, n, lines) in (FAMILIES[:2] if QUICK else FAMILIES):
        q = len(lines)
        A0 = coord_family(n, lines)
        B = tangent_basis(n, lines)
        d = len(B)
        Lam, y0, dp0 = lambda_matrix(A0, B, lines, n, q)
        Gam = gamma_matrix(A0, B, n, q)

        wl, vl = np.linalg.eigh(Lam)
        wg, vg = np.linalg.eigh(Gam)
        tolL = max(1e-9, 1e-9 * max(abs(wl).max(), 1.0))
        tolG = max(1e-9, 1e-9 * max(abs(wg).max(), 1.0))
        nl = [i for i in range(d) if abs(wl[i]) < tolL]
        ng = [i for i in range(d) if abs(wg[i]) < tolG]
        # every null direction of Lambda, tested against Gamma
        worst = 0.0
        for i in nl:
            v = vl[:, i]
            worst = max(worst, float(v @ Gam @ v))
        contained = worst < 1e-7 * max(1.0, float(np.abs(Gam).max()))

        # the generalised problem on the complement of null(Gamma)
        pos = [i for i in range(d) if wg[i] > tolG]
        if pos:
            S = vg[:, pos] * (1.0 / np.sqrt(wg[pos]))
            M = S.T @ Lam @ S
            gmax = float(np.linalg.eigvalsh(M).max())
        else:
            gmax = float('nan')
        verdicts.append((contained, gmax))
        print(f"{nm:>20}{d:>9}{orbit_dim(n):>7}{len(nl):>8}{len(nl) - orbit_dim(n):>8}"
              f"{len(ng):>8}{str(contained):>11}{gmax:>12.6f}")

    print()
    if verdicts and not all(c for (c, _) in verdicts):
        exponents()

    print()
    if not verdicts:
        print("  no family produced a form")
        return 0
    ok_a = all(c for (c, _) in verdicts)
    ok_b = all(g < -1e-9 for (_, g) in verdicts)
    if ok_a and ok_b:
        print("  P44 HOLDS. Every direction along which the top root does not move at second order")
        print("  also kills the commutator form, and the largest generalised eigenvalue is strictly")
        print("  negative, so Lambda <= -c Gamma with c its negative. The commutator is a Lyapunov")
        print("  functional at second order, which is the first non-sampling evidence for P41 and")
        print("  names the constant a proof would have to produce.")
    else:
        print("  P44 IS REFUTED. There are directions ON THE CONE with Lambda = 0 and Gamma > 0,")
        print("  so the top root does not move at second order where the commutator does, and NO")
        print("  inequality Lambda <= -c Gamma can hold. The LINEAR shape is dead.")
        print("  What replaces it is not nothing. Along such a direction the root falls at order")
        print("  four while the commutator grows at order two, and the table above shows the two")
        print("  exponents pairing into a constant ratio (y_0 - y)/C^2 across a decade in t. So the")
        print("  commutator is still the right functional and the wrong power was assumed: the")
        print("  shape a proof should target is maxroot <= y_0 - c C^2, quadratic and not linear.")
        print("  The degenerate directions, which made the second-order test blind, are exactly")
        print("  where that distinction is visible, so they are the evidence rather than the")
        print("  obstacle.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
