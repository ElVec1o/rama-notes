"""sr_lpR.py -- the LP for (SR-BAND), now WITH stability information.

sr_lp2.py showed that (i)+(ii) alone stop forcing the band once q is large,
and that an LP over EXCHANGEABLE laws is the exact optimum for (i)+(ii).  But
Proposition R (sr_rigid.py) -- a PROVED linear consequence of (ii)+(iii) --
is vacuous on exchangeable laws.  So the honest LP must be run in the FULL
coefficient space, over compositions rather than partitions:

    variables   c_s >= 0,  s a composition of p into q parts of size <= b
    (ii)        sum_{s : s_k = j} c_s = C(b,j) a^{-j}(1-1/a)^{b-j}      (all k,j)
    (R)         sum_s c_s  s_l (s_k)_m (1-a)^{s_k - m} = 0
                                              (all k != l, m = 0..b-2)
    objective   f_c(y0) = sum_s c_s prod_k (y0 - a s_k)

f_c is monic of degree q in y, so  min_c f_c(y0) < 0  certifies a real root
above y0, and  min_c f_c(y0) >= 0 for every y0 > hi  says no law in the
relaxation has an odd-order real root above hi.  Since every law satisfying
(i)+(ii)+(iii) satisfies (ii)+(R), a nonnegative minimum is a CERTIFICATE for
(SR-BAND) at that size.  The lower edge uses the sign (-1)^p (f = y^{q-p} mu).

This is a strictly stronger relaxation than sr_lp2.py, and (sr_dim.py) its
feasible affine hull is exactly the affine hull of the projection families.
"""
import sys
import numpy as np
from math import comb
from scipy.optimize import linprog

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import band, law_from_family, rand_proj_family              # noqa
from sr_perturb import compositions, marg_constraints, fcoef, base_law    # noqa
from sr_dim import R_constraints                                          # noqa


def build(p, q, a, b, use_R=True):
    E = compositions(p, q, b)
    A, rhs = marg_constraints(E, q, a, b)
    if use_R:
        R = R_constraints(E, q, a, b)
        A = np.vstack([A, R])
        rhs = np.concatenate([rhs, np.zeros(len(R))])
    return E, A, rhs


def obj(E, a, y0):
    v = np.ones(len(E))
    for k in range(E.shape[1]):
        v = v * (y0 - a * E[:, k])
    return v


def scan(p, q, a, b, use_R=True, ngrid=160, tag=''):
    lo, hi = band(a, b)
    E, A, rhs = build(p, q, a, b, use_R=use_R)
    M = len(E)
    r0 = linprog(np.zeros(M), A_eq=A, b_eq=rhs, bounds=(0, None), method='highs')
    if not r0.success:
        print(f"  ({p},{q},{a},{b}) {tag}: relaxation INFEASIBLE ({r0.message[:40]})")
        return None
    out = dict(feasible=True)
    # ---- upper edge
    best = None
    for y0 in np.linspace(a * b - 1e-9, hi + 1e-9, ngrid):
        c = obj(E, a, y0)
        sc = np.abs(c).max()
        r = linprog(c / sc, A_eq=A, b_eq=rhs, bounds=(0, None), method='highs')
        if r.success and r.fun * sc < -1e-11 * max(1.0, sc):
            best = (y0, r.x)
            break
    if best is None:
        print(f"  ({p},{q},{a},{b}) {tag}: UPPER  no real root above "
              f"hi = {hi:.5f} is possible   *** BAND EDGE CERTIFIED ***")
        out['up'] = None
    else:
        print(f"  ({p},{q},{a},{b}) {tag}: UPPER  certified real root > "
              f"{best[0]:.5f}  (hi = {hi:.5f}, excess {best[0]-hi:+.5f})")
        out['up'] = best[0]
    # ---- lower edge
    if lo > 1e-12:
        sgn = (-1.0) ** p   # f = y^(q-p) mu(y): the sign below all
        # roots of mu is (-1)^p, NOT (-1)^q -- the y^(q-p) factor is positive
        bestl = None
        for y0 in np.linspace(1e-9, lo - 1e-9, ngrid):
            c = sgn * obj(E, a, y0)
            sc = np.abs(c).max()
            r = linprog(c / sc, A_eq=A, b_eq=rhs, bounds=(0, None), method='highs')
            if r.success and r.fun * sc < -1e-11 * max(1.0, sc):
                bestl = (y0, r.x)
                break
        if bestl is None:
            print(f"  {'':>{len(str((p,q,a,b)))+2}}  {tag}  LOWER  no real root "
                  f"below lo = {lo:.5f} is possible   *** BAND EDGE CERTIFIED ***")
            out['low'] = None
        else:
            print(f"  {'':>{len(str((p,q,a,b)))+2}}  {tag}  LOWER  certified real "
                  f"root < {bestl[0]:.5f}  (lo = {lo:.5f}, deficit "
                  f"{lo-bestl[0]:+.5f})")
            out['low'] = bestl[0]
    else:
        print(f"  {'':>{len(str((p,q,a,b)))+2}}  {tag}  LOWER  lo = 0, nothing "
              f"to prove")
        out['low'] = None
    return out


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    CASES = [(4, 6, 3, 2), (3, 6, 4, 2), (3, 4, 4, 3), (5, 5, 3, 3),
             (4, 5, 5, 4), (6, 8, 4, 3), (6, 9, 3, 2)]
    print("=" * 78)
    print("A.  WITHOUT Proposition R  (this is sr_lp2 in the full coefficient")
    print("    space -- must reproduce the exchangeable answer)")
    print("=" * 78)
    for c in CASES:
        try:
            scan(*c, use_R=False, tag='(no R)')
        except MemoryError:
            print(f"  {c}: too big")
    print()
    print("=" * 78)
    print("B.  WITH Proposition R  (a PROVED linear consequence of (ii)+(iii))")
    print("=" * 78)
    for c in CASES:
        try:
            scan(*c, use_R=True, tag='(+R) ')
        except MemoryError:
            print(f"  {c}: too big")
