"""The exact curvature of the top root as a commuting family is rotated off the commuting locus.

code/offcoord.py measured that commuting tight rank-b projection families are the best in their
class, locally and globally at the sizes reached. That is sampling. This computes the second-order
coefficient exactly, in rational arithmetic, along explicit curves that stay on the tight
projection variety.

THE CURVE, AND WHY IT SATISFIES THE GUARDRAIL. Rotating each block by its own U_e preserves
idempotency and breaks tightness; restoring tightness by conjugating with S^{-1/2} preserves
tightness and breaks idempotency, which is how an earlier version of the search left the
projection class without noticing. A common rotation preserves both but is a conjugation, so mu
is unchanged and the curvature is zero for trivial reasons. The move that does all three:

  take hyperedges e, f and coordinates v in e\\f, w in f\\e, let R(theta) rotate the plane
  span{e_v, e_w} and apply it to P_e and P_f ONLY.

Then P_v + P_w restricted to that plane is the identity, so

  R (P_e + P_f) R^T = P_{e\\v} + P_{f\\w} + R (P_v + P_w) R^T = P_e + P_f

IDENTICALLY IN THETA, and every other block is untouched: the tightness sum is preserved exactly,
not to leading order. Each rotated block is R P R^T with R orthogonal, hence a rank-b orthogonal
projection exactly. And the family genuinely decommutes, since span{cos(theta) e_v + sin(theta)
e_w} is neither inside nor orthogonal to the range of a block containing v but not w.

WHAT IS COMPUTED. With mu(y, theta) the mixed characteristic polynomial of the rotated family,
expanded in theta over the rationals,

  mu(y, theta) = mu_0(y) + theta mu_1(y) + theta^2 mu_2(y) + ...,

and y(theta) the top root, implicit differentiation at a simple root gives

  y_1 = -mu_1(y_0) / mu_0'(y_0),
  y_2 = -[ mu_0''(y_0) y_1^2 / 2 + mu_1'(y_0) y_1 + mu_2(y_0) ] / mu_0'(y_0),

so lambda_max(theta) = y_0 + y_2 theta^2 + O(theta^3) and the curvature constant is C = -y_2.

The odd orders vanish for a reason rather than by accident: flipping the sign of the coordinate w
is an orthogonal conjugation that fixes every coordinate projection and sends R(theta) to
R(-theta), so the theta and -theta families are orthogonally conjugate and mu is even in theta.
That is checked here rather than assumed, and a nonzero mu_1 would mean the construction is wrong.

NOTE ON THE FORM. The expansion is about y_0, the top root of the commuting family itself, NOT
about (sqrt(a-1)+sqrt(b-1))^2. Those are different numbers: the Fano family reaches 0.8995 of the
band edge, and only in the girth-to-infinity limit does the commuting maximum approach it. An
expansion of the band edge in theta would be an expansion about a point the family never occupies.

ARITHMETIC. Truncated power series over Fraction, with characteristic polynomials by
Leverrier-Faddeev. Nothing is evaluated in floating point except the final report, and the exact
result is cross-checked against the numeric mixed_char_poly at several angles.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'

import sys
import math
import time
import itertools
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode

QUICK = quickmode.QUICK
NORD = 3 if QUICK else 5          # truncation order in theta; 3 suffices for C, 5 shows the tail


# ------------------------------------------------------------------ truncated series over Q
def s_zero():
    return [Fr(0)] * NORD


def s_const(c):
    v = s_zero(); v[0] = Fr(c); return v


def s_add(a, b):
    return [a[i] + b[i] for i in range(NORD)]


def s_sub(a, b):
    return [a[i] - b[i] for i in range(NORD)]


def s_mul(a, b):
    out = [Fr(0)] * NORD
    for i in range(NORD):
        ai = a[i]
        if ai:
            for j in range(NORD - i):
                bj = b[j]
                if bj:
                    out[i + j] += ai * bj
    return out


def s_smul(a, c):
    return [x * c for x in a]


def s_cos():
    """cos(theta) truncated: 1 - t^2/2 + t^4/24 - ..."""
    v = s_zero()
    for k in range(0, NORD, 2):
        v[k] = Fr((-1) ** (k // 2), math.factorial(k))
    return v


def s_sin():
    v = s_zero()
    for k in range(1, NORD, 2):
        v[k] = Fr((-1) ** ((k - 1) // 2), math.factorial(k))
    return v


# ------------------------------------------------------------------ matrices over the series ring
def m_zero(n):
    return [[s_zero() for _ in range(n)] for _ in range(n)]


def m_mul(A, B, n):
    C = m_zero(n)
    for i in range(n):
        Ai = A[i]
        for k in range(n):
            aik = Ai[k]
            if not any(aik):
                continue
            Bk = B[k]
            Ci = C[i]
            for j in range(n):
                bkj = Bk[j]
                if any(bkj):
                    Ci[j] = s_add(Ci[j], s_mul(aik, bkj))
    return C


def m_trace(A, n):
    t = s_zero()
    for i in range(n):
        t = s_add(t, A[i][i])
    return t


def charpoly(A, n):
    """det(xI - A) = x^n + c_1 x^{n-1} + ... + c_n, by Leverrier-Faddeev over the series ring."""
    c = [s_const(1)]
    M = [row[:] for row in A]
    for k in range(1, n + 1):
        if k > 1:
            for i in range(n):
                M[i][i] = s_add(M[i][i], c[k - 1])
            M = m_mul(A, M, n)
        ck = s_smul(m_trace(M, n), Fr(-1, k))
        c.append(ck)
    return c


def esym(A, n):
    """e_m of the eigenvalues: e_m = (-1)^m c_m with c the characteristic coefficients."""
    c = charpoly(A, n)
    return [s_smul(c[m], Fr((-1) ** m)) for m in range(n + 1)]


# ------------------------------------------------------------------ the mixed characteristic poly
def mixed_char_series(fam, n, q):
    """mu(y) = sum_m mu[m] y^{n-m}, exactly, over the truncated series ring.

    Same formula as code/mixed_char_poly.py's reference implementation, which is the definition
    reorganised by subsets; agreement with that implementation is checked numerically below.
    """
    binom = [[Fr(math.comb(a, b_)) for b_ in range(n + 1)] for a in range(q + 1)]
    mu = [s_zero() for _ in range(n + 1)]
    for r in range(q + 1):
        sgn = Fr(-1) if (r & 1) else Fr(1)
        for R in itertools.combinations(range(q), r):
            if r == 0:
                mu[0] = s_add(mu[0], s_const(1))
                continue
            M = m_zero(n)
            for k in R:
                for i in range(n):
                    for j in range(n):
                        if any(fam[k][i][j]):
                            M[i][j] = s_add(M[i][j], fam[k][i][j])
            e = esym(M, n)
            brow = binom[q - r]
            for m in range(r, n + 1):
                mu[m] = s_add(mu[m], s_smul(e[m], sgn * brow[m - r]))
    return mu


def rotated_family(n, lines, e, f, v, w):
    """The coordinate family with R(theta) applied to blocks e and f only, exactly in theta."""
    C, S = s_cos(), s_sin()
    C2, S2, CS = s_mul(C, C), s_mul(S, S), s_mul(C, S)
    fam = []
    for k, L in enumerate(lines):
        A = m_zero(n)
        for x in L:
            A[x][x] = s_const(1)
        if k == e:                                  # v is rotated into span{v, w}
            A[v][v] = C2; A[w][w] = S2
            A[v][w] = CS; A[w][v] = CS
        elif k == f:                                # w is rotated, with the opposite sign
            A[v][v] = S2; A[w][w] = C2
            A[v][w] = s_smul(CS, Fr(-1)); A[w][v] = s_smul(CS, Fr(-1))
        fam.append(A)
    return fam


def fano():
    return 7, [[(i + s) % 7 for s in (0, 1, 3)] for i in range(7)]


def curvature(n, lines, e, f, v, w):
    """Return (mu_0, mu_1, mu_2) as integer-coefficient polynomial coefficient lists in y."""
    fam = rotated_family(n, lines, e, f, v, w)
    mu = mixed_char_series(fam, n, len(lines))
    return [[mu[m][k] for m in range(n + 1)] for k in range(NORD)]


def main():
    import sympy as sp
    t0 = time.time()
    n, lines = fano()
    a = b = 3
    q = len(lines)
    y = sp.Symbol('y')
    print("The curvature of the top root along a rotation that stays on the tight projection")
    print("variety. Exact rational arithmetic; the expansion is about the commuting family's own")
    print("top root, not about the band edge, which the family does not occupy.\n")

    E, F = set(lines[0]), set(lines[1])
    e, f = 0, 1
    v, w = sorted(E - F)[0], sorted(F - E)[0]
    lay = curvature(n, lines, e, f, v, w)
    print(f"curve: e = {sorted(E)}, f = {sorted(F)}, rotating span(e_{v}, e_{w})"
          f"   [{time.time() - t0:.0f}s]")

    def poly(co):
        return sp.Poly(sum(sp.Rational(co[m]) * y ** (n - m) for m in range(n + 1)), y)

    mu0, mu1, mu2 = poly(lay[0]), poly(lay[1]), poly(lay[2])
    print(f"  mu_1 identically zero: {'yes' if mu1.as_expr() == 0 else 'NO -- construction wrong'}")
    print(f"  mu_0(y) = {sp.factor(mu0.as_expr())}")

    roots = [r for r in sp.Poly(mu0, y).real_roots()]
    y0 = max(roots)
    mp = sp.minimal_polynomial(y0, y)
    print(f"  y_0 = {sp.N(y0, 15)},  minimal polynomial {mp}")

    d0 = sp.diff(mu0.as_expr(), y)
    y2 = sp.simplify(-mu2.as_expr().subs(y, y0) / d0.subs(y, y0))
    Cc = sp.radsimp(sp.simplify(-y2))
    Cmp = sp.minimal_polynomial(Cc, y)
    print(f"\n  lambda_max(theta) = y_0 - C theta^2 + O(theta^4)")
    print(f"  C = {sp.N(Cc, 15)}   exact minimal polynomial: {Cmp}")
    print(f"  C > 0: {'yes' if sp.N(Cc) > 0 else 'NO -- not a maximum along this curve'}")

    # CONTROL. The exact quadratic against the numeric top root at small angles, by a route that
    # shares no code: numpy roots of code/mixed_char_poly.py on the float family.
    import numpy as np
    from mixed_char_poly import mixed_char_poly
    Cf, y0f = float(sp.N(Cc, 30)), float(sp.N(y0, 30))
    print(f"\n  CONTROL -- exact quadratic against the numeric top root")
    print(f"{'theta':>9}{'numeric':>18}{'y_0 - C th^2':>18}{'residual/th^4':>16}")
    for th in (0.05, 0.1, 0.2, 0.4):
        A = np.zeros((q, n, n))
        for k, L in enumerate(lines):
            for xx in L:
                A[k, xx, xx] = 1.0
        R = np.eye(n); cc_, ss_ = math.cos(th), math.sin(th)
        R[v, v] = cc_; R[v, w] = -ss_; R[w, v] = ss_; R[w, w] = cc_
        for k in (e, f):
            A[k] = R @ A[k] @ R.T
        num = max(z.real for z in np.roots(mixed_char_poly(A)) if abs(z.imag) < 1e-9)
        quad = y0f - Cf * th ** 2
        print(f"{th:>9.2f}{num:>18.12f}{quad:>18.12f}{(num - quad) / th ** 4:>16.6f}")

    # THE SWEEP. Every curve of this shape, over all (e, f, v, w). The Fano plane's automorphism
    # group is transitive on ordered pairs of distinct lines, so a single value of C across all of
    # them is the expected outcome and a different one would mean the construction is not what it
    # is claimed to be.
    print(f"\n  SWEEP -- C over every (e, f, v, w) with v in e\\f, w in f\\e")
    seen = {}
    for (ee, ff) in itertools.permutations(range(q), 2):
        Ee, Ff = set(lines[ee]), set(lines[ff])
        for vv in sorted(Ee - Ff):
            for ww in sorted(Ff - Ee):
                lay2 = curvature(n, lines, ee, ff, vv, ww)
                m0, m1, m2 = poly(lay2[0]), poly(lay2[1]), poly(lay2[2])
                if m1.as_expr() != 0:
                    print(f"    (e,f,v,w)=({ee},{ff},{vv},{ww}) has mu_1 nonzero"); continue
                yy = max(sp.Poly(m0, y).real_roots())
                cval = float(sp.N(-(-m2.as_expr().subs(y, yy) / sp.diff(m0.as_expr(), y).subs(y, yy)), 20))
                seen.setdefault(round(cval, 12), 0)
                seen[round(cval, 12)] += 1
    print(f"    {sum(seen.values())} curves, {len(seen)} distinct value(s) of C:")
    for kk, vvv in sorted(seen.items()):
        print(f"      C = {kk:.12f}   ({vvv} curves)   {'POSITIVE' if kk > 0 else 'NOT POSITIVE'}")

    print("\n  WHAT THIS PROVES, AND WHAT IT DOES NOT. Each C is one diagonal entry of the")
    print("  Hessian of the top root at the commuting point, in the basis of these curves.")
    print("  All positive means the top root strictly decreases along every one of them. It is")
    print("  NOT negative definiteness: that needs the off-diagonal entries as well, which these")
    print("  curves do not supply. What they do supply is that the point is CRITICAL -- mu_1")
    print("  vanishes on a spanning set of tangent directions and the differential is linear --")
    print("  so the Hessian is well defined and independent of the retraction used to compute it.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
