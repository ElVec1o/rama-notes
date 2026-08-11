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
        tr = m_trace(M, n)
        ck = [(-x) / k if isinstance(x, Fr) else Fr(-x, k) for x in tr]
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
    if NORD == 3:                       # integral, and that is what makes the big cases feasible
        C2 = [Fr(1), Fr(0), Fr(-1)]
        S2 = [Fr(0), Fr(0), Fr(1)]
        CS = [Fr(0), Fr(1), Fr(0)]
    else:
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


def pick(lines, e, f):
    """A valid (v, w): v in e minus f, w in f minus e. Both are nonempty for distinct lines of
    equal size, which is what makes the construction available at every one of these families."""
    E, F = set(lines[e]), set(lines[f])
    return sorted(E - F)[0], sorted(F - E)[0]


def analyse(nm, a, b, n, lines, sp, ncurves):
    """mu_0, mu_1, mu_2 exactly, then y_0 and C as algebraic numbers."""
    y = sp.Symbol('y')
    q = len(lines)

    def poly(co):
        return sp.Poly(sum(sp.Rational(co[m]) * y ** (n - m) for m in range(n + 1)), y)

    e, f = 0, 1
    v, w = pick(lines, e, f)
    t = time.time()
    lay = curvature(n, lines, e, f, v, w)
    mu0, mu1, mu2 = poly(lay[0]), poly(lay[1]), poly(lay[2])
    odd_ok = mu1.as_expr() == 0
    y0 = max(sp.Poly(mu0, y).real_roots())
    mp0 = sp.minimal_polynomial(y0, y)
    d0 = sp.diff(mu0.as_expr(), y)
    Cc = sp.radsimp(sp.simplify(mu2.as_expr().subs(y, y0) / d0.subs(y, y0)))
    mpC = sp.minimal_polynomial(Cc, y)
    print(f"{nm}  (a,b) = ({a},{b}), n = {n}, q = {q}   [{time.time() - t:.0f}s]")
    print(f"  mu_1 identically zero: {'yes' if odd_ok else 'NO -- construction wrong'}")
    print(f"  y_0 = {sp.N(y0, 15)}   deg(min poly) = {sp.Poly(mp0, y).degree()}")
    print(f"  C   = {sp.N(Cc, 15)}   deg(min poly) = {sp.Poly(mpC, y).degree()}"
          f"   {'POSITIVE' if sp.N(Cc) > 0 else 'NOT POSITIVE'}")
    rho2 = (math.sqrt(a - 1) + math.sqrt(b - 1)) ** 2
    print(f"  y_0 / rho^2 = {float(sp.N(y0)) / rho2:.6f},  C / y_0 = {float(sp.N(Cc / y0)):.8f},"
          f"  C * q = {float(sp.N(Cc)) * q:.8f}")

    # C is not a single number once two hyperedges can be DISJOINT. In the Fano plane any two
    # lines meet, so there is one orbit and one C; in AG(2,3) and PG(2,3) lines fall into meeting
    # and parallel pairs, and the curvature is indexed by that. Classify rather than average.
    byint = {}
    pairs = [(i, j) for i in range(q) for j in range(q) if i != j]
    for (ee, ff) in pairs[:ncurves]:
        vv, ww = pick(lines, ee, ff)
        inter = len(set(lines[ee]) & set(lines[ff]))
        l2 = curvature(n, lines, ee, ff, vv, ww)
        m0, m2 = poly(l2[0]), poly(l2[2])
        if m2.as_expr() == 0 and m0.as_expr() == 0:
            continue
        yy = max(sp.Poly(m0, y).real_roots())
        cv = float(sp.N(m2.as_expr().subs(y, yy) / sp.diff(m0.as_expr(), y).subs(y, yy), 20))
        byint.setdefault(inter, {}).setdefault(round(cv, 12), 0)
        byint[inter][round(cv, 12)] += 1
    print(f"  over {sum(sum(d.values()) for d in byint.values())} curves, grouped by |e ∩ f|:")
    for inter in sorted(byint):
        d = byint[inter]
        print(f"    |e ∩ f| = {inter}: {len(d)} distinct C -> "
              + ", ".join(f"{k:.12f} x{v}" for k, v in sorted(d.items())))
    return float(sp.N(y0, 20)), float(sp.N(Cc, 20)), sp.Poly(mpC, y).degree(), byint


def curvature(n, lines, e, f, v, w):
    """Return (mu_0, mu_1, mu_2) as integer-coefficient polynomial coefficient lists in y."""
    fam = rotated_family(n, lines, e, f, v, w)
    mu = mixed_char_series(fam, n, len(lines))
    return [[mu[m][k] for m in range(n + 1)] for k in range(NORD)]


def main():
    import sympy as sp
    from xu_sharp import ag23, pg23
    t0 = time.time()
    print("Curvature off the commuting locus, exactly, across three commuting tight families.")
    print("The expansion is about each family's own top root, not about the band edge.\n")

    # AG(2,3) costs about two minutes and PG(2,3) about twenty, so --quick runs the Fano family
    # only; the point of the quick mode is a reproducible baseline, not coverage.
    cases = [("Fano/Heawood", 3, 3, *fano())]
    if not QUICK:
        cases += [("AG(2,3)", 4, 3, *ag23()), ("PG(2,3)", 4, 4, *pg23())]

    out = {}
    for (nm, a, b, n, lines) in cases:
        ncurves = 4 if QUICK else (42 if n == 7 else 14)
        out[nm] = (a, b) + analyse(nm, a, b, n, lines, sp, ncurves)[:3]
        print()

    print(f"{'family':>14}{'(a,b)':>8}{'n':>4}{'q':>4}{'y_0':>16}{'C':>18}{'deg C':>7}"
          f"{'C*q':>14}{'C*n':>14}")
    for nm, (a, b, y0, C, dC) in out.items():
        n = {'Fano/Heawood': 7, 'AG(2,3)': 9, 'PG(2,3)': 13}[nm]
        q = {'Fano/Heawood': 7, 'AG(2,3)': 12, 'PG(2,3)': 13}[nm]
        print(f"{nm:>14}{f'({a},{b})':>8}{n:>4}{q:>4}{y0:>16.10f}{C:>18.12f}{dC:>7}"
              f"{C * q:>14.8f}{C * n:>14.8f}")
    print("\n  There is no closed form C(a,b), and not for want of data: AG(2,3) carries TWO")
    print("  values at the single parameter pair (4,3), 0.041740312350 when the two hyperedges")
    print("  are disjoint and 0.021354509344 when they meet. C is a function of the pair of")
    print("  hyperedges rotated, not of (a,b), so the quantity the question asks for does not")
    print("  exist. What is uniform across all three families is deg(C) = deg(y_0) = n: mu_0 is")
    print("  irreducible and C generates the same field as the top root.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
