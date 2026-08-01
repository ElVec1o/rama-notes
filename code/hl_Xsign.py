"""Adversarial search for a weighted 2-plane family and a direction with X_e(2 sqrt a) > 0.

Why this one number decides the band.  For a weighted 2-plane family A on R^m
(c_k >= 0, V_k a 2-plane, Adj(A) = sum_k c_k P_{V_k} <= a I) write F_A(x) = mu(x+a),
let A^(e) be the compression to e-perp, f_k = iota_e omega_k, theta_k = ||f_k||^2 and
A''_k the compression to span{e, f_k}-perp.  The vertex identity is

    F_A = x F_{A^(e)} - sum_k theta_k F_{A''_k} - X_e ,                        (1)

X_e being the overlap remainder, which vanishes identically for coordinate families
at coordinate directions -- there (1) is the Heilmann-Lieb vertex recursion.

Put R_e = F_A / F_{A^(e)}.  Dividing (1) by F_{A^(e)},

    R_e = x - sum_k theta_k / R'_k - X_e / F_{A^(e)},   R'_k = F_{A^(e)} / F_{A''_k}.

The class is closed under compression, and sum_k theta_k = <e, Adj(A) e> <= a.  So if
R'_k >= x/2 for every k by induction on the dimension, then

    R_e >= x - 2a/x - X_e / F_{A^(e)} ,     and     x - 2a/x >= x/2  iff  x >= 2 sqrt a,

with equality exactly at x = 2 sqrt a.  Hence: if X_e <= 0 for x >= 2 sqrt a, then
R_e >= x/2 > 0 there, so F_A has no root above 2 sqrt a; F_A is even or odd, so all
roots lie in [-2 sqrt a, 2 sqrt a], which is the band
mu-roots in [a - 2 sqrt a, a + 2 sqrt a].  The base case m <= 1 is R_e = x >= x/2.

The induction therefore has exactly one gap, the sign of X_e, and nothing else.
This script attacks that sign: it maximises X_e(2 sqrt a) over the sphere of
directions, for graph families, noncommuting projection families and general
weighted plane families, and reports the largest value found.

Usage:  python3 hl_Xsign.py
Deterministic: all seeds fixed.
"""
import math

import numpy as np
from scipy.optimize import minimize

import hl_planes as hp


def X_at(Bs, m, e, x):
    """X_e(x) from (1)."""
    d = hp.recursion(Bs, m, e / np.linalg.norm(e))
    return float(np.polyval(d['X'], x))


def C_coeffs(Bs, m, e):
    """X_e = sum_{r>=2} (-1)^{r-1} C_r x^{m-2r};  C_r = M_r - M'_r - sum_k theta_k M''_{k,r-1}."""
    d = hp.recursion(Bs, m, e / np.linalg.norm(e))
    return hp.C_list(d['X'], m)


def worst_direction(Bs, m, x, restarts=6, seed=0):
    """max over unit e of X_e(x), by multistart Nelder-Mead on the sphere."""
    rng = np.random.default_rng(seed)
    best, arg = -np.inf, None
    for _ in range(restarts):
        e0 = rng.normal(size=m)
        res = minimize(lambda v: -X_at(Bs, m, v, x), e0,
                       method='Nelder-Mead',
                       options=dict(maxiter=600, xatol=1e-9, fatol=1e-11))
        if -res.fun > best:
            best, arg = -res.fun, res.x / np.linalg.norm(res.x)
    return best, arg


def run(name, Bs, m, seed=0):
    a = float(np.trace(hp.Adj(Bs)) / m)
    x = 2 * math.sqrt(a)
    val, e = worst_direction(Bs, m, x, seed=seed)
    scale = abs(float(np.polyval(hp.F_dense(Bs, m), x)))
    C = C_coeffs(Bs, m, e)
    flag = 'X<=0' if val <= 1e-9 * max(1.0, scale) else '*** X>0 ***'
    print(f"{name:38} m={m:2} q={len(Bs):3} a={a:5.2f}   max_e X_e = {val:13.5g}"
          f"   (F_A = {scale:.4g})  {flag}")
    print(f"{'':38} C_r at that e: "
          f"{np.array2string(C, precision=4, max_line_width=110)}")
    return val <= 1e-9 * max(1.0, scale)


def main():
    print("=" * 108)
    print("Maximising X_e(2 sqrt a) over the sphere.  X_e <= 0 closes the induction "
          "and proves the band.")
    print("=" * 108)
    ok = True

    print("\n-- coordinate (graph) families --")
    for nm, ed, m in (("K_4", hp.Kn_edges(4), 4), ("K_5", hp.Kn_edges(5), 5),
                      ("K_6", hp.Kn_edges(6), 6), ("cube", hp.cube_edges(), 8)):
        ok &= run(nm, hp.graph_blocks(ed, m), m)

    print("\n-- noncommuting rank-2 projection families --")
    for m, a, s in ((4, 3, 0), (6, 3, 1), (6, 3, 2), (6, 4, 0)):
        Bs, err = hp.random_projection_family(m, a, seed=s)
        if err < 1e-10:
            ok &= run(f"projections a={a} seed={s}", Bs, m, seed=s)

    print("\n-- general weighted plane families (c_k != 1) --")
    for m, s in ((4, 0), (4, 1), (6, 0), (6, 1)):
        Bs, res = hp.random_plane_family(m, 3.0, seed=s)
        if Bs is not None:
            ok &= run(f"planes seed={s}", Bs, m, seed=s)

    print()
    print("no direction with X_e(2 sqrt a) > 0 found:" if ok else "COUNTEREXAMPLE FOUND:", ok)


if __name__ == "__main__":
    main()
