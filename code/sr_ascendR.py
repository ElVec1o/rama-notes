"""sr_ascendR.py -- the sharpest falsification run for (SR-BAND).

sr_perturb.py ascended inside {c >= 0} cap {marginals} cap {stable} and could
not move at all: generic directions of the marginal null space leave the
stable set immediately.  sr_dim.py explains why -- Proposition R cuts that null
space down to (at these sizes) exactly the affine hull of the projection
families.  So the honest search is the ascent inside

        {c >= 0}  cap  {marginals}  cap  {R}  cap  {stable},

i.e. inside the affine hull of the matrix class, with stability enforced.
If lambda_max can be pushed past hi there, (SR-BAND) is FALSE; if it saturates
at the matrix optimum, the matrix families are locally extremal for the whole
strongly Rayleigh class.
"""
import sys
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import band                                                 # noqa
from sr_perturb import (compositions, marg_constraints, fcoef, base_law,
                        Stab)                                             # noqa
from sr_dim import R_constraints                                          # noqa


def run(p, q, a, b, seed=0, nsamp=200, iters=500, ndir=30, upper=True):
    lo, hi = band(a, b)
    E = compositions(p, q, b)
    A, rhs = marg_constraints(E, q, a, b)
    R = R_constraints(E, q, a, b)
    AR = np.vstack([A, R])
    F = fcoef(E, a, q)
    c0, res, P = base_law(p, q, a, b, E, kind='random', seed=seed)
    st = Stab(E, p, seed=seed + 5, nsamp=nsamp)
    U_, S_, Vt = np.linalg.svd(AR, full_matrices=True)
    rk = int((S_ > 1e-9 * S_.max()).sum())
    N = Vt[rk:].T
    print(f"({p},{q},{a},{b})  M={len(E)}  band=[{lo:.5f},{hi:.5f}]  "
          f"residual {res:.1e}")
    print(f"    R-constrained null space dimension = {N.shape[1]}  "
          f"(marginal-only was {len(E)-np.linalg.matrix_rank(A,tol=1e-9)})")
    print(f"    base: stability probe {st.worst(c0):.2e}, "
          f"|R.c0| = {np.abs(R@c0).max():.2e}")
    # --- how far can we move in a random R-null direction and stay stable?
    rng = np.random.default_rng(seed + 17)
    fr = []
    for _ in range(ndir):
        g = N @ rng.normal(size=N.shape[1])
        g /= np.linalg.norm(g)
        neg = g < 0
        emax = np.min(-c0[neg] / g[neg]) if neg.any() else 1.0
        e = emax
        for _ in range(30):
            c = c0 + e * g
            if c.min() >= -1e-14 and st.worst(c) < 1e-9:
                break
            e *= 0.6
        fr.append(e / max(emax, 1e-30))
    fr = np.array(fr)
    print(f"    stable fraction of the nonneg limit in R-null directions: "
          f"median {np.median(fr):.3g}, max {fr.max():.3g}  "
          f"({(fr>0.02).sum()}/{ndir} directions keep >2%)")
    # --- ascent
    c = c0.copy()
    step = 0.05
    y = None
    for it in range(iters):
        f = F.T @ c
        r = np.roots(f)
        rr = np.sort(r.real[np.abs(r.imag) < 1e-7 * max(1.0, np.abs(r).max())])
        rr = rr[np.abs(rr) > 1e-9]
        if len(rr) == 0:
            break
        y = rr.max() if upper else rr.min()
        fs = F @ np.array([y ** (q - i) for i in range(q + 1)])
        fp = np.polyval(np.polyder(f), y)
        g = (-fs / fp) * (1.0 if upper else -1.0)
        g = N @ (N.T @ g)
        g[(c <= 1e-14) & (g < 0)] = 0.0
        nr = np.linalg.norm(g)
        if nr < 1e-14:
            break
        g /= nr
        moved, s = False, step
        for _ in range(28):
            cn = np.maximum(c + s * g, 0.0)
            if (c + s * g).min() >= -1e-13 and st.worst(cn) < 1e-9:
                rn = np.roots(F.T @ cn)
                rrn = np.sort(rn.real[np.abs(rn.imag) < 1e-7 *
                                      max(1.0, np.abs(rn).max())])
                rrn = rrn[np.abs(rrn) > 1e-9]
                if len(rrn):
                    yn = rrn.max() if upper else rrn.min()
                    if (yn > y + 1e-13) if upper else (yn < y - 1e-13):
                        c, moved = cn, True
                        break
            s *= 0.5
        if not moved:
            step *= 0.5
            if step < 1e-10:
                break
        else:
            step = min(step * 1.25, 0.25)
        if it % 100 == 0:
            print(f"      it {it:4d}  lambda_{'max' if upper else 'min'} "
                  f"= {y:.6f}")
    tag = 'max' if upper else 'min'
    tgt = hi if upper else lo
    bad = (y > hi + 1e-7) if upper else (y < lo - 1e-7)
    print(f"    ASCENT lambda_{tag} -> {y:.6f}   ({'hi' if upper else 'lo'} = "
          f"{tgt:.6f})   {'*** (SR-BAND) VIOLATED ***' if bad else 'inside the band'}")
    print(f"    final: |R.c| = {np.abs(R@c).max():.2e}, "
          f"|marg err| = {np.abs(A@c-rhs).max():.2e}, "
          f"stability probe {st.worst(c):.2e}")
    return y, c


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("(4,6,3,2) -- control: (i)+(ii) alone already force the band")
    print("=" * 78)
    run(4, 6, 3, 2, seed=11, nsamp=180, iters=400, upper=True)
    run(4, 6, 3, 2, seed=11, nsamp=180, iters=400, upper=False)
    print()
    print("=" * 78)
    print("(6,9,3,2) -- THE decisive size: (i)+(ii)+(R) still permit a root at")
    print("ab = 6 > hi = 5.82843, so only the nonlinear part of stability can")
    print("save the band here.")
    print("=" * 78)
    run(6, 9, 3, 2, seed=23, nsamp=160, iters=400, upper=True)
    run(6, 9, 3, 2, seed=23, nsamp=160, iters=400, upper=False)
    print()
    print("=" * 78)
    print("(5,5,3,3) -- b = 3, where R leaves a dimension gap of 30")
    print("=" * 78)
    run(5, 5, 3, 3, seed=31, nsamp=160, iters=400, upper=True)
