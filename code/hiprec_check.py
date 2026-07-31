"""High-precision (mpmath, 60 digits) recomputation of mu[A] to bound the
float64 error of mixed_char_poly on the family sizes we actually search."""
import numpy as np
from itertools import combinations
from math import comb
from mpmath import mp, mpf, matrix
from mixed_char_poly import mixed_char_poly
from tff import build_tff, build_psd_family

mp.dps = 60


def char_coeffs_mp(M, p):
    """e[0..p] with det(yI+M) = sum_m e[m] y^(p-m), Faddeev-LeVerrier in mp."""
    cs = [mpf(1)]
    Nk = None
    for k in range(1, p + 1):
        if k == 1:
            Ak = [row[:] for row in M]
        else:
            Ak = [[sum(M[i][t] * Nk[t][j] for t in range(p)) for j in range(p)]
                  for i in range(p)]
        tr = sum(Ak[i][i] for i in range(p))
        ck = -tr / k
        cs.append(ck)
        Nk = [[Ak[i][j] + (ck if i == j else mpf(0)) for j in range(p)]
              for i in range(p)]
    return [cs[k] * (-1) ** k for k in range(p + 1)]


def mixed_char_poly_mp(As):
    q = len(As)
    p = As[0].shape[0]
    Amp = [[[mpf(float(A[i][j])) for j in range(p)] for i in range(p)] for A in As]
    mu = [mpf(0)] * (p + 1)
    for r in range(q + 1):
        sgn = -1 if (r & 1) else 1
        for R in combinations(range(q), r):
            if r == 0:
                mu[0] += sgn
                continue
            M = [[sum(Amp[k][i][j] for k in R) for j in range(p)] for i in range(p)]
            e = char_coeffs_mp(M, p)
            for m in range(r, p + 1):
                mu[m] += sgn * comb(q - r, m - r) * e[m]
    return mu


rng = np.random.default_rng(7)
for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3)]:
    As, res = build_tff(p, q, a, b, rng)
    c_f = mixed_char_poly(As)
    c_m = mixed_char_poly_mp(As)
    # the mp input is the float64 matrix itself, so this isolates the
    # conditioning of the subset formula (not the input error)
    err = max(abs(mpf(float(c_f[i])) - c_m[i]) for i in range(p + 1))
    scale = max(abs(x) for x in c_m)
    rt_f = np.sort(np.roots(c_f).real)
    rt_m = np.sort(np.roots(np.array([float(x) for x in c_m])).real)
    print(f"p={p} q={q} (a,b)=({a},{b})  feas_res={res:.1e}  "
          f"coeff rel err (float64 vs 60-digit) = {float(err/scale):.3e}   "
          f"max root diff = {np.max(np.abs(rt_f-rt_m)):.3e}")
