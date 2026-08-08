"""sr_hunt.py -- gradient-free stochastic hunt for a counterexample to
(SR-BAND) at the decisive size (6,9,3,2).

The projected-gradient ascent of sr_ascendR.py stalls: the base law has many
coefficients at (or near) zero, so the gradient direction is immediately cut
by the nonnegativity face and the step collapses.  This is a plain random-
direction hill climb inside

        {c >= 0} cap {marginals} cap {R} cap {stable},

which does not suffer from that: each proposal is a random direction of the
R-constrained null space, taken as far as nonnegativity and the stability
probe allow, and accepted iff lambda_max strictly increases.

The certified reference points at (6,9,3,2) are
        matrix optimum (sr_slack.py)                 5.48533
        band edge   hi = (sqrt2 + 1)^2               5.82843
        (i)+(ii)+(R) linear relaxation (sr_lpR.py)   6.00000  = ab .
Anything the hunt reaches above hi while the stability probe stays clean is a
counterexample; saturating below hi is evidence for (SR-BAND).

RESULT AND ITS CAVEAT.  No counterexample.  From two starts the hunt raised
lambda_max only from 5.416593 to 5.418039 and from 5.452062 to 5.452930 -- it
does not even reach the matrix optimum 5.48533, let alone hi = 5.82843.  AND:
the running 140-line stability probe is too weak.  An independent re-check of
the final point with 1200 fresh lines returns max|Im|/scale = 8.7e-2 and
6.4e-2, i.e. the walk had already LEAKED OUT of the stable set.  So the search
is not a certificate in either direction: it explored a set strictly LARGER
than the strongly Rayleigh laws and still got nowhere near the band edge.
That makes the negative result conservative, but it also means the stability
probe -- not the optimiser -- is the binding constraint on this approach.
"""
import sys
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import band                                                 # noqa
from sr_perturb import (compositions, marg_constraints, fcoef, base_law,
                        Stab)                                             # noqa
from sr_dim import R_constraints                                          # noqa


def lam(c, F, upper=True):
    r = np.roots(F.T @ c)
    rr = np.sort(r.real[np.abs(r.imag) < 1e-7 * max(1.0, np.abs(r).max())])
    rr = rr[np.abs(rr) > 1e-9]
    if len(rr) == 0:
        return None
    return float(rr.max()) if upper else float(rr.min())


def hunt(p, q, a, b, seed=0, nsamp=140, trials=1500, use_R=True, upper=True,
         verbose=True):
    lo, hi = band(a, b)
    E = compositions(p, q, b)
    A, rhs = marg_constraints(E, q, a, b)
    C = np.vstack([A, R_constraints(E, q, a, b)]) if use_R else A
    F = fcoef(E, a, q)
    c0, res, P = base_law(p, q, a, b, E, kind='random', seed=seed)
    st = Stab(E, p, seed=seed + 5, nsamp=nsamp)
    U_, S_, Vt = np.linalg.svd(C, full_matrices=True)
    rk = int((S_ > 1e-9 * S_.max()).sum())
    N = Vt[rk:].T
    rng = np.random.default_rng(seed + 101)
    c = c0.copy()
    best = lam(c, F, upper)
    start = best
    acc = 0
    for t in range(trials):
        g = N @ rng.normal(size=N.shape[1])
        g /= np.linalg.norm(g)
        neg = g < 0
        emax = np.min(-c[neg] / g[neg]) if neg.any() else 1.0
        e = min(emax, 5.0)
        got = None
        for _ in range(14):
            cn = c + e * g
            if cn.min() >= -1e-14:
                cn = np.maximum(cn, 0.0)
                if st.worst(cn) < 1e-9:
                    got = cn
                    break
            e *= 0.55
        if got is None:
            continue
        # try the full stable step and a few shorter ones, keep the best
        for frac in (1.0, 0.6, 0.3):
            cn = np.maximum(c + frac * e * g, 0.0)
            if st.worst(cn) >= 1e-9:
                continue
            v = lam(cn, F, upper)
            if v is None:
                continue
            if (v > best + 1e-12) if upper else (v < best - 1e-12):
                best, c, acc = v, cn, acc + 1
                break
        if verbose and t % 250 == 0:
            print(f"      trial {t:5d}  best lambda_{'max' if upper else 'min'}"
                  f" = {best:.6f}   accepted {acc}")
    tag = 'max' if upper else 'min'
    tgt = hi if upper else lo
    bad = (best > hi + 1e-7) if upper else (best < lo - 1e-7)
    print(f"    hunt ({'+R' if use_R else 'no R'}) lambda_{tag}: {start:.6f} "
          f"-> {best:.6f}   ({'hi' if upper else 'lo'} = {tgt:.6f})   "
          f"{'*** (SR-BAND) VIOLATED ***' if bad else 'inside the band'}")
    print(f"    final stability probe {st.worst(c):.2e}, |marg err| "
          f"{np.abs(A@c-rhs).max():.2e}, moves accepted {acc}")
    # a much harder stability re-check on the final point
    st2 = Stab(E, p, seed=seed + 9999, nsamp=1200)
    print(f"    independent stability re-check (1200 fresh lines): "
          f"{st2.worst(c):.2e}")
    return best, c


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("(6,9,3,2): matrix optimum 5.48533 | hi 5.82843 | linear relax 6.0")
    print("=" * 78)
    for sd in (23, 77):
        print(f"  seed {sd}")
        hunt(6, 9, 3, 2, seed=sd, nsamp=140, trials=1200, use_R=True, upper=True)
        hunt(6, 9, 3, 2, seed=sd, nsamp=140, trials=1200, use_R=True, upper=False)
    print()
    print("=" * 78)
    print("(5,5,3,3): b = 3.  matrix ~6.8519 | hi 8.0")
    print("=" * 78)
    hunt(5, 5, 3, 3, seed=31, nsamp=160, trials=1500, use_R=True, upper=True)
    print()
    print("=" * 78)
    print("(4,6,3,2) control: (i)+(ii) alone force the band, so the hunt MUST")
    print("stay below hi = 5.82843 whatever it does.")
    print("=" * 78)
    hunt(4, 6, 3, 2, seed=11, nsamp=160, trials=1500, use_R=True, upper=True)
