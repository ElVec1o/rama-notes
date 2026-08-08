"""sr_lp.py -- how much room do (i) sum = p  and  (ii) marginals = Bin(b,1/a)
leave, BEFORE stability (iii) is imposed?

The objective  f_law(y) = E prod_k (y - a s_k)  is LINEAR in the law, and both
constraints are linear and S_q-invariant, and the objective is S_q-invariant.
So symmetrising is w.l.o.g.:  the exact optimum over ALL laws satisfying
(i)+(ii) equals the optimum over EXCHANGEABLE laws, i.e. over the simplex whose
vertices are the orbits = partitions of p into at most q parts of size <= b.

Three things are computed for each (p,q,a,b):

  DIM    the dimension of the polytope  {x >= 0 : mass = 1, marginals = Bin}.
         DIM = 0 means (i)+(ii) DETERMINE mu completely -- the conjecture is
         then a closed-form statement with no freedom at all.

  LPMAX  sup over the polytope of a certified real root, via
         max { y0 : min_x f_x(y0) < 0 }.  (f_x is monic of degree q, so
         f_x(y0) < 0 certifies a real root > y0.)  Symmetrically LPMIN for the
         lower edge, using sign (-1)^q f_x(y0) with y0 < lo.

  Compared against the band edges  lo, hi  and the trivial bound ab.
"""
import sys
import numpy as np
from math import comb
from fractions import Fraction
from scipy.optimize import linprog

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def partitions_fixed(p, q, b):
    out = []

    def rec(pos, remaining, cap, cur):
        if pos == q:
            if remaining == 0:
                out.append(tuple(cur))
            return
        lo = max(0, remaining - cap * (q - pos - 1))
        for v in range(min(cap, remaining), lo - 1, -1):
            cur.append(v)
            rec(pos + 1, remaining - v, v, cur)
            cur.pop()
    rec(0, p, b, [])
    return out


def constraints(lams, p, q, a, b, exact=False):
    """rows: mass, then P(s_1 = j) for j = 0..b."""
    N = len(lams)
    if exact:
        A = [[Fraction(1)] * N]
        rhs = [Fraction(1)]
        for j in range(b + 1):
            A.append([Fraction(sum(1 for v in lam if v == j), q) for lam in lams])
            rhs.append(Fraction(comb(b, j) * (a - 1) ** (b - j), a ** b))
        return A, rhs
    A = [np.ones(N)]
    rhs = [1.0]
    for j in range(b + 1):
        A.append(np.array([sum(1 for v in lam if v == j) / q for lam in lams]))
        rhs.append(comb(b, j) * (1.0 / a) ** j * (1 - 1.0 / a) ** (b - j))
    return np.array(A), np.array(rhs)


def poly_of(lam, a, q):
    poly = np.array([1.0])
    for v in lam:
        poly = np.convolve(poly, [1.0, -a * float(v)])
    return poly


def objective(lams, y0, a):
    return np.array([float(np.prod([y0 - a * v for v in lam])) for lam in lams])


def polytope_dim(lams, p, q, a, b):
    """dimension of {x >= 0, Ax = rhs}; -1 if infeasible."""
    A, rhs = constraints(lams, p, q, a, b)
    N = len(lams)
    r = linprog(np.zeros(N), A_eq=A, b_eq=rhs, bounds=(0, 1), method='highs')
    if not r.success:
        return -1, None, None
    # dimension of the affine set intersected with the (relatively open) face
    rk = np.linalg.matrix_rank(A, tol=1e-10)
    # find the support of a relative-interior point (average of many LP vertices)
    rng = np.random.default_rng(0)
    acc = np.zeros(N)
    for _ in range(40):
        c = rng.normal(size=N)
        rr = linprog(c, A_eq=A, b_eq=rhs, bounds=(0, 1), method='highs')
        if rr.success:
            acc += rr.x
    supp = acc > 1e-9
    if supp.sum() == 0:
        return -1, None, None
    rk_s = np.linalg.matrix_rank(A[:, supp], tol=1e-10)
    return int(supp.sum() - rk_s), A, rhs


def certify(lams, A, rhs, a, q, y0, sign):
    c = sign * objective(lams, y0, a)
    r = linprog(c, A_eq=A, b_eq=rhs, bounds=(0, 1), method='highs')
    if not r.success:
        return None, None
    return r.fun, r.x


def edge_search(lams, A, rhs, a, q, lo, hi, p, upper=True, tol=1e-7):
    """largest y0 > hi (resp. smallest y0 < lo) with a certified violation."""
    if upper:
        y_ok, y_bad = hi, float(a * max(max(l) for l in lams)) + 1e-9
        val0, _ = certify(lams, A, rhs, a, q, hi + 1e-9, 1.0)
        if val0 is None or val0 >= -1e-11:
            return None, None
        for _ in range(60):
            mid = 0.5 * (y_ok + y_bad)
            v, x = certify(lams, A, rhs, a, q, mid, 1.0)
            if v is not None and v < -1e-11:
                y_ok = mid
            else:
                y_bad = mid
            if y_bad - y_ok < tol:
                break
        v, x = certify(lams, A, rhs, a, q, y_ok, 1.0)
        return y_ok, x
    else:
        if lo <= 1e-12:
            return None, None
        sgn = (-1.0) ** p   # f = y^(q-p) mu(y): the sign below all
        # roots of mu is (-1)^p, NOT (-1)^q -- the y^(q-p) factor is positive
        y_ok, y_bad = lo, 0.0
        val0, _ = certify(lams, A, rhs, a, q, lo - 1e-9, sgn)
        if val0 is None or val0 >= -1e-11:
            return None, None
        for _ in range(60):
            mid = 0.5 * (y_ok + y_bad)
            v, x = certify(lams, A, rhs, a, q, mid, sgn)
            if v is not None and v < -1e-11:
                y_ok = mid
            else:
                y_bad = mid
            if y_ok - y_bad < tol:
                break
        v, x = certify(lams, A, rhs, a, q, y_ok, sgn)
        return y_ok, x


def unique_law(lams, p, q, a, b):
    """If DIM = 0, return the exact rational law."""
    A, rhs = constraints(lams, p, q, a, b, exact=True)
    import sympy as sp
    M = sp.Matrix([[sp.Rational(x) for x in row] for row in A])
    v = sp.Matrix([sp.Rational(x) for x in rhs])
    sol, params = M.gauss_jordan_solve(M.copy() * 0 + M, v)
    return sol, params


def run(p, q, a, b, show_law=False):
    lo, hi = band(a, b)
    lams = partitions_fixed(p, q, b)
    N = len(lams)
    dim, A, rhs = polytope_dim(lams, p, q, a, b)
    if dim < 0:
        print(f"({p},{q},{a},{b}) : (i)+(ii) INFEASIBLE for exchangeable laws")
        return None
    print(f"({p},{q},{a},{b})  band=[{lo:.5f},{hi:.5f}]  ab={a*b}  "
          f"orbits={N}  DIM={dim}")
    res = dict(p=p, q=q, a=a, b=b, dim=dim, N=N, lo=lo, hi=hi)
    if dim == 0:
        r = linprog(np.zeros(N), A_eq=A, b_eq=rhs, bounds=(0, 1), method='highs')
        x = r.x
        f = np.zeros(q + 1)
        for wi, lam in zip(x, lams):
            if wi > 1e-13:
                f += wi * poly_of(lam, a, q)
        rt = np.roots(f)
        rr = np.sort(rt.real[np.abs(rt.real) > 1e-9])
        print(f"    RIGID: the law -- hence mu -- is FORCED by (i)+(ii).")
        print(f"    roots {np.array2string(rr, precision=5)}  "
              f"max|Im|={np.abs(rt.imag).max():.1e}  "
              f"INSIDE={np.all(rr >= lo-1e-7) and np.all(rr <= hi+1e-7)}")
        if show_law:
            for wi, lam in zip(x, lams):
                if wi > 1e-13:
                    print(f"      {lam}: {wi:.6f}")
        res['rigid_roots'] = rr
        return res
    yU, xU = edge_search(lams, A, rhs, a, q, lo, hi, p, upper=True)
    yL, xL = edge_search(lams, A, rhs, a, q, lo, hi, p, upper=False)
    if yU is None:
        print(f"    UPPER: no violation certifiable -- (i)+(ii) alone give "
              f"lambda_max <= {hi:.5f}  ***band forced***")
    else:
        print(f"    UPPER: certified root up to {yU:.5f}  "
              f"(hi={hi:.5f}, ab={a*b})  excess {yU-hi:+.5f}")
        supp = [(lams[i], float(xU[i])) for i in range(N) if xU[i] > 1e-9]
        print(f"       witness support: {supp}")
    if yL is None:
        print(f"    LOWER: no violation certifiable -- (i)+(ii) alone give "
              f"lambda_min >= {lo:.5f}  ***band forced***")
    else:
        print(f"    LOWER: certified root down to {yL:.5f}  (lo={lo:.5f})  "
              f"deficit {lo-yL:+.5f}")
        supp = [(lams[i], float(xL[i])) for i in range(N) if xL[i] > 1e-9]
        print(f"       witness support: {supp}")
    res['yU'], res['xU'], res['yL'], res['xL'], res['lams'] = yU, xU, yL, xL, lams
    return res


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("b = 2 cases (context: the known-open sharpening of MSS)")
    print("=" * 78)
    for c in [(4, 6, 3, 2), (6, 9, 3, 2), (8, 12, 3, 2), (3, 6, 4, 2),
              (4, 8, 4, 2), (6, 12, 4, 2), (4, 10, 5, 2)]:
        run(*c)
    print()
    print("=" * 78)
    print("b = 3 cases  -- THE OPEN REGIME")
    print("=" * 78)
    for c in [(3, 4, 4, 3), (6, 8, 4, 3), (9, 12, 4, 3), (3, 5, 5, 3),
              (6, 10, 5, 3), (3, 3, 3, 3), (4, 4, 3, 3), (5, 5, 3, 3),
              (6, 6, 3, 3), (7, 7, 3, 3), (8, 8, 3, 3), (3, 6, 6, 3),
              (6, 12, 6, 3)]:
        run(*c, show_law=True)
    print()
    print("=" * 78)
    print("b = 4 cases")
    print("=" * 78)
    for c in [(4, 5, 5, 4), (8, 10, 5, 4), (4, 4, 4, 4), (5, 5, 4, 4),
              (6, 6, 4, 4), (2, 3, 6, 4), (4, 6, 6, 4)]:
        run(*c, show_law=True)
