"""Adversarial search for a weighted 2-plane family and a direction with X_e(2 sqrt a) > 0,
and for one with a negative summed leading cross term C_2.

Why these two numbers decide the band.  For a weighted 2-plane family A on R^m
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

Writing X_e = sum_{r>=2} (-1)^{r-1} C_r x^{m-2r}, the leading term is -C_2 x^{m-4}, so
C_2 >= 0 is necessary for X_e <= 0 at large x.  C_2 is NOT nonnegative termwise -- single
pairs (k,l) and single subsets T take negative values -- so only the sum is in question,
and it is cheap to evaluate, which is why it gets the wider sweep here.

COST.  hp.recursion evaluates F_dense once per block plus twice more, and F_dense is a
determinant per subset of size <= m//2.  With q blocks that is about (q+2) * sum_r C(q,r)
determinants for ONE objective evaluation, so q must be kept small: hp.random_plane_family
defaults to q = 3m(m+1)/2, which is 63 blocks at m = 6 and makes a single evaluation cost
millions of determinants.  This script passes q explicitly and caps m, the restart count,
the iteration count and the wall clock.  It also pins the BLAS thread count to 1 (see
run_hl_Xsign.sh) so it cannot saturate every core.

Usage:  bash run_hl_Xsign.sh          (sets the thread caps, then runs this)
Deterministic: all seeds fixed.
"""
import itertools
import math
import time

import numpy as np
from scipy.optimize import minimize

import hl_planes as hp

BUDGET_S = 420.0          # hard wall clock for the whole script
_T0 = time.monotonic()


def over_budget():
    return time.monotonic() - _T0 > BUDGET_S


# ---------------------------------------------------------------------------
#  X_e, the quantity that decides the induction
# ---------------------------------------------------------------------------
def X_at(Bs, m, e, x):
    d = hp.recursion(Bs, m, e / np.linalg.norm(e))
    return float(np.polyval(d['X'], x))


def worst_direction(Bs, m, x, restarts=3, maxiter=150, seed=0):
    """max over unit e of X_e(x), by multistart Nelder-Mead on the sphere."""
    rng = np.random.default_rng(seed)
    best, arg = -np.inf, None
    for _ in range(restarts):
        if over_budget():
            break
        res = minimize(lambda v: -X_at(Bs, m, v, x), rng.normal(size=m),
                       method='Nelder-Mead',
                       options=dict(maxiter=maxiter, xatol=1e-9, fatol=1e-11))
        if -res.fun > best:
            best, arg = -res.fun, res.x / np.linalg.norm(res.x)
    return best, arg


# ---------------------------------------------------------------------------
#  C_2, the leading cross term -- cheap, so it gets the wider sweep
# ---------------------------------------------------------------------------
def C2(Bs, m, e):
    """C_2 = sum_{k<l} 2 <f_k ^ omega'_l , f_l ^ omega'_k>."""
    e = e / np.linalg.norm(e)
    Q = hp.ortho_complement([e], m)
    Bc = [Q @ B for B in Bs]
    fs = [Q @ hp.f_vec(B, e) for B in Bs]
    tot = 0.0
    for k, l in itertools.combinations(range(len(Bs)), 2):
        A1 = np.column_stack([fs[k], Bc[l][:, 0], Bc[l][:, 1]])
        A2 = np.column_stack([fs[l], Bc[k][:, 0], Bc[k][:, 1]])
        tot += 2.0 * float(np.linalg.det(A1.T @ A2))
    return tot


def min_C2(Bs, m, restarts=6, maxiter=800, seed=0):
    rng = np.random.default_rng(seed)
    best = np.inf
    for _ in range(restarts):
        if over_budget():
            break
        res = minimize(lambda v: C2(Bs, m, v), rng.normal(size=m),
                       method='Nelder-Mead',
                       options=dict(maxiter=maxiter, xatol=1e-10, fatol=1e-12))
        best = min(best, res.fun)
    return best


# ---------------------------------------------------------------------------
def families(kind, m, a=3.0, seed=0):
    """A small family of the requested kind, with q kept explicitly small."""
    if kind == 'graph':
        ed = {4: hp.Kn_edges(4), 5: hp.Kn_edges(5), 6: hp.Kn_edges(6),
              8: hp.cube_edges(), 10: hp.petersen_edges()}[m]
        return hp.graph_blocks(ed, m)
    if kind == 'proj':
        Bs, err = hp.random_projection_family(m, int(a), seed=seed)
        return Bs if err < 1e-10 else None
    q = m * (m + 1) // 2 + 2          # just above the minimum spanning count
    Bs, res = hp.random_plane_family(m, a, q=q, seed=seed)
    return Bs if (Bs is not None and res < 1e-9) else None


def main():
    print("=" * 96)
    print("PART 1.  max over unit e of X_e(2 sqrt a).   X_e <= 0 closes the induction.")
    print("=" * 96)
    okX = True
    cases = [('graph', 4, 3.0, 0), ('graph', 5, 4.0, 0), ('graph', 6, 5.0, 0),
             ('proj', 4, 3, 0), ('proj', 6, 3, 1),
             ('plane', 4, 3.0, 0), ('plane', 4, 3.0, 1), ('plane', 5, 3.0, 0),
             ('plane', 6, 3.0, 0)]
    for kind, m, a, s in cases:
        if over_budget():
            print("  [wall-clock budget reached, stopping PART 1]")
            break
        Bs = families(kind, m, a, s)
        if Bs is None:
            continue
        av = float(np.trace(hp.Adj(Bs)) / m)
        x = 2 * math.sqrt(av)
        val, _ = worst_direction(Bs, m, x, seed=s)
        sc = abs(float(np.polyval(hp.F_dense(Bs, m), x)))
        good = val <= 1e-9 * max(1.0, sc)
        okX &= good
        print(f"  {kind:6} m={m:2} q={len(Bs):3} a={av:5.2f}   max_e X_e = {val:12.5g}"
              f"   (F_A={sc:.4g})   {'X<=0' if good else '*** X>0 ***'}", flush=True)

    print()
    print("=" * 96)
    print("PART 2.  min over unit e of the summed leading cross term C_2.  C_2 >= 0 is")
    print("         necessary for X_e <= 0 at large x, and is false termwise.")
    print("=" * 96)
    okC = True
    for kind, m, a, s in [('graph', 4, 3.0, 0), ('graph', 5, 4.0, 0), ('graph', 6, 5.0, 0),
                          ('graph', 8, 3.0, 0), ('graph', 10, 3.0, 0),
                          ('proj', 4, 3, 0), ('proj', 6, 3, 1), ('proj', 8, 3, 0),
                          ('plane', 4, 3.0, 0), ('plane', 5, 3.0, 0),
                          ('plane', 6, 3.0, 0), ('plane', 7, 3.0, 0)]:
        if over_budget():
            print("  [wall-clock budget reached, stopping PART 2]")
            break
        Bs = families(kind, m, a, s)
        if Bs is None:
            continue
        v = min_C2(Bs, m, seed=s)
        okC &= v >= -1e-9
        print(f"  {kind:6} m={m:2} q={len(Bs):3}   min_e C_2 = {v:14.6g}"
              f"   {'C_2>=0' if v >= -1e-9 else '*** C_2 < 0 ***'}", flush=True)

    print()
    print(f"no direction with X_e(2 sqrt a) > 0 found : {okX}")
    print(f"no direction with C_2 < 0 found           : {okC}")
    print(f"elapsed {time.monotonic() - _T0:.0f}s of {BUDGET_S:.0f}s budget")


if __name__ == "__main__":
    main()
