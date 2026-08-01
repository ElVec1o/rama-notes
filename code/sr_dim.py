"""sr_dim.py -- IS THE CLASS OF (SR-BAND) STRICTLY LARGER THAN THE MATRIX
CLASS?  A dimension count in the coefficient space of the pgf.

Everything lives in R^M, M = #{compositions of p into q parts of size <= b},
the coefficient space of  G(z) = sum_s c_s z^s.  Three nested sets:

    PROJ  = { c : c comes from a rank-b projection family }
    SR    = { c >= 0 : marginals = Bin(b,1/a),  G real stable }
    LP    = { c >= 0 : marginals = Bin(b,1/a) }                (the LP polytope)

and PROJ  subset  SR  subset  LP.  We compare AFFINE HULL DIMENSIONS:

  dim aff(LP)   = M - rank(marginal constraints)                    [exact]
  dim aff(SR)  <= M - rank(marginal constraints + Proposition R)    [upper bd,
                  because R is a necessary LINEAR consequence of (ii)+(iii)]
  dim aff(PROJ) = rank of the centred matrix of many sampled families
                                                                    [exact,
                  up to sampling]

If the R-bound already meets dim aff(PROJ), the two classes have the same
affine hull and (SR-BAND) is, at that size, not a strictly weaker hypothesis
than the matrix statement.  If the R-bound is much larger, either more linear
consequences of stability are missing, or the class is genuinely bigger.
"""
import sys
import numpy as np
from math import comb

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import (band, binom_pmf, law_from_family, graph_family,
                      rand_proj_family, icosahedral_rank2)               # noqa
from sr_perturb import compositions, marg_constraints, fcoef, base_law, Stab
from frac_naimark import GRAPHS                                          # noqa


def R_constraints(E, q, a, b):
    """rows r with r . c = E[s_l (s_k)_m (1-a)^{s_k-m}], for m = 0..b-2."""
    rows = []
    w0 = 1.0 - a
    for k in range(q):
        for l in range(q):
            if l == k:
                continue                      # automatic
            sk = E[:, k].astype(float)
            sl = E[:, l].astype(float)
            for m in range(b - 1):
                ff = np.ones(len(E))
                for t in range(m):
                    ff = ff * (sk - t)
                pw = np.where(sk - m >= 0, w0 ** np.maximum(sk - m, 0), 0.0)
                pw = np.where(sk >= m, pw, 0.0)
                rows.append(sl * ff * pw)
    return np.array(rows)


def proj_dim(p, q, a, b, E, nsamp=160, seed=0, complex_=False):
    idx = {tuple(s): i for i, s in enumerate(E)}
    C = []
    for t in range(nsamp):
        P, res = rand_proj_family(p, q, a, b, seed=seed + 1000 * t,
                                  complex_=complex_)
        if res > 1e-11:
            continue
        W, S = law_from_family(P, a, b)
        c = np.zeros(len(E))
        for wt, s in zip(W, S):
            c[idx[tuple(s.tolist())]] += wt
        C.append(c)
    C = np.array(C)
    Cc = C - C.mean(axis=0)
    sv = np.linalg.svd(Cc, compute_uv=False)
    tol = max(Cc.shape) * sv.max() * 1e-10
    return int((sv > tol).sum()), C, sv


def run(p, q, a, b, nsamp=120, seed=0, check_R=True):
    E = compositions(p, q, b)
    M = len(E)
    A, rhs = marg_constraints(E, q, a, b)
    rkA = np.linalg.matrix_rank(A, tol=1e-9)
    R = R_constraints(E, q, a, b)
    AR = np.vstack([A, R])
    rkAR = np.linalg.matrix_rank(AR, tol=1e-9)
    dproj, C, sv = proj_dim(p, q, a, b, E, nsamp=nsamp, seed=seed)
    # sanity: do the sampled families satisfy R to machine precision?
    resR = float(np.abs(R @ C.T).max()) if len(C) else np.nan
    print(f"({p},{q},{a},{b})  M = {M}")
    print(f"    rank(marginals) = {rkA}            -> dim aff(LP)  = {M - rkA}")
    print(f"    rank(marginals + R) = {rkAR}       -> dim aff(SR) <= {M - rkAR}"
          f"    (R adds {rkAR - rkA} independent constraints)")
    print(f"    dim aff(PROJ) = {dproj}  (from {len(C)} sampled real families; "
          f"max |R . c| over samples = {resR:.2e})")
    print(f"    singular values of the centred PROJ sample (top 12): "
          f"{np.array2string(sv[:12], precision=3)}")
    gap = (M - rkAR) - dproj
    print(f"    ==> gap between the R-bound and the matrix hull: {gap}"
          f"{'   (the two hulls could still coincide only if gap = 0)' if gap else '   *** EQUAL ***'}")
    return dict(M=M, rkA=rkA, rkAR=rkAR, dproj=dproj)


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("AFFINE-HULL DIMENSIONS:  PROJ  subset  SR  subset  LP")
    print("=" * 78)
    for (p, q, a, b) in [(3, 4, 4, 3), (4, 6, 3, 2), (3, 6, 4, 2),
                         (5, 5, 3, 3), (4, 5, 5, 4), (6, 8, 4, 3)]:
        run(p, q, a, b, nsamp=140, seed=7)
        print()
    print("=" * 78)
    print("The decisive size (6,9,3,2): the smallest (a,b) = (3,2) case where")
    print("(i)+(ii) alone permit a root at ab = 6 > hi = 5.82843.")
    print("=" * 78)
    run(6, 9, 3, 2, nsamp=90, seed=3)
