"""ff_L3.py -- settling claim (L) inside the three-cumulant class.

THE CLASS.   T(a,b) := { tau prob. measure on R :
        m1 = a-1,  mu2 = (a-1)(b-1),  mu3 = (a-1)(b-1)(b-2) }
(the moment translation of "rho real-rooted with the FORCED kappa_1..kappa_3").
chi^{boxplus (a-1)} lies in T(a,b) and gives L = (sqrt(a-1)-sqrt(b-1))^2 exactly.

TWO PROVED STRUCTURAL FACTS, both verified here:

(S) SQUEEZE.   min supp(tau) <= L(tau) <= min supp(tau) + 1.
    Proof.  F(w) := K_chi(w)+K_tau(w)-1/w = R_chi(w) + K_tau(w).
    Writing R_nu(w) = x - 1/G_nu(x) at x = K_nu(w), one has
        d/dx [x - 1/G(x)] = 1 - G'(x)/G(x)^2 <= 0
    by Cauchy-Schwarz ( G(x)^2 = (int dnu/(x-t))^2 <= int dnu/(x-t)^2 = -G'(x) ),
    so R_nu decreases from m1(nu) (at x=-infty, w->0-) to min supp nu
    (at x -> min supp, w -> -infty).  Hence 0 <= R_chi(w) <= 1 for w<0, and
    K_tau(w) < min supp tau with limit min supp tau.  Both bounds follow.

(A) MAX ATOM AT THE LEFT EDGE.   if min supp tau >= c then
        tau({c})  <=  mu2 / ( mu2 + (m1-c)^2 ) ,
    by Cauchy-Schwarz on Y = X-c >= 0:  E[Y]^2 <= E[Y^2] P(Y>0).
    Combined with Bercovici-Voiculescu,  (chi boxplus tau)({c}) =
    max(chi({0}) + tau({c}) - 1, 0), so tau({c}) > 1/b forces L(tau) = c.

CONSEQUENCE (the counterexample engine).  tau({c}) > 1/b is compatible with
T(a,b) exactly when  (a-1-c)^2 < (b-1)^2 (a-1), i.e.
        c  >  c0(a,b) := (a-1) - (b-1) sqrt(a-1).
So for every c in ( c0(a,b), treeedge ) there is tau in T(a,b) with
supp tau contained in [c, infty) and L(tau) = c < treeedge: claim (L) FAILS.
"""
import sys
from math import sqrt

import numpy as np
from scipy.optimize import fsolve, least_squares

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_L as X                                                               # noqa


def c0(a, b):
    return (a - 1.0) - (b - 1.0) * sqrt(a - 1.0)


def max_atom(c, a, b):
    """Cauchy-Schwarz cap on tau({c}) for tau in T(a,b) with supp in [c,inf)."""
    m1, mu2, _ = X.forced_moments(a, b)
    return mu2 / (mu2 + (m1 - c) ** 2)


# --------------------------------------------------- explicit 3-atom witness
def witness(c, s, a, b):
    """tau = s delta_c + (1-s) * (2-atom on [c,inf)) with the exact forced
    moments.  Returns (atoms, weights) or None if not realisable."""
    m1, mu2, mu3 = X.forced_moments(a, b)
    M1, M2 = m1 - c, mu2 + (m1 - c) ** 2
    M3 = mu3 + 3.0 * M1 * mu2 + M1 ** 3
    if s >= mu2 / M2:
        return None
    # remaining mass 1-s carries raw moments M1,M2,M3 -> normalised
    n1, n2, n3 = M1 / (1 - s), M2 / (1 - s), M3 / (1 - s)
    v2 = n2 - n1 ** 2
    v3 = n3 - 3 * n1 * n2 + 2 * n1 ** 3
    if v2 <= 0:
        return None
    # 2-atom with mean n1, var v2, third central v3, CLOSED FORM:
    #   masses (r,1-r) at (u,u+d);  v2 = r(1-r)d^2,  v3 = r(1-r)(2r-1)d^3
    #   => skew g := v3/v2^{3/2} = 2x/sqrt(1-x^2) with x = 2r-1,
    #      so x = g/sqrt(4+g^2),  r = (1+x)/2,  d = sqrt(v2/(r(1-r))).
    g = v3 / v2 ** 1.5
    x = g / sqrt(4.0 + g * g)
    r = 0.5 * (1.0 + x)
    if not (0.0 < r < 1.0):
        return None
    d = sqrt(v2 / (r * (1.0 - r)))
    u = n1 - (1 - r) * d          # u, v are values of Y = X - c
    v = u + d
    if u < -1e-12:
        return None
    atoms = np.array([c, c + u, c + v])
    wts = np.array([s, (1 - s) * r, (1 - s) * (1 - r)])
    return atoms, wts


def check_moments(atoms, wts, a, b):
    m1t, m2t, m3t = X.forced_moments(a, b)
    w = wts / wts.sum()
    m1 = float(np.dot(w, atoms))
    mu2 = float(np.dot(w, (atoms - m1) ** 2))
    mu3 = float(np.dot(w, (atoms - m1) ** 3))
    return max(abs(m1 - m1t), abs(mu2 - m2t), abs(mu3 - m3t))


# --------------------------------------------- independent check: random matrix
def rm_free_edge(atoms, wts, b, N=1200, reps=6, seed=0):
    """empirical min eigenvalue of A + U B U*, A ~ chi, B ~ tau, U Haar.
    A large-N stand-in for min supp(chi boxplus tau)."""
    rng = np.random.default_rng(seed)
    da = np.concatenate([np.zeros(N - N // b), np.full(N // b, float(b))])
    cnt = np.maximum(1, np.round(np.asarray(wts) / np.sum(wts) * N).astype(int))
    while cnt.sum() > N:
        cnt[int(np.argmax(cnt))] -= 1
    while cnt.sum() < N:
        cnt[int(np.argmax(cnt))] += 1
    db = np.concatenate([np.full(cnt[i], float(atoms[i])) for i in range(len(atoms))])
    out = []
    for _ in range(reps):
        Z = rng.normal(size=(N, N))
        Q, R = np.linalg.qr(Z)
        Q = Q * np.sign(np.diag(R))
        M = np.diag(da) + (Q * db) @ Q.T
        out.append(float(np.linalg.eigvalsh(M)[0]))
    return float(np.mean(out)), float(np.std(out))


# --------------------------------- realise the witness as a real-rooted poly
def _fit_positions(fixed_vals, fixed_mult, free_mult, guess, a, b, lower=None):
    """p roots = fixed_vals with multiplicities fixed_mult, plus three free
    positions with multiplicities free_mult; solve the three moment equations."""
    m1, mu2, mu3 = X.forced_moments(a, b)
    fm = np.asarray(fixed_mult, int)
    gm = np.asarray(free_mult, int)
    fv = np.asarray(fixed_vals, float)
    P = fm.sum() + gm.sum()

    def resid(z):
        r = np.concatenate([np.repeat(fv, fm), np.repeat(z, gm)])
        mm = r.mean()
        return [mm - m1, ((r - mm) ** 2).mean() - mu2,
                ((r - mm) ** 3).mean() - mu3]

    lo = -np.inf if lower is None else lower
    best = None
    for scale in (1.0, 0.5, 2.0, 4.0, 0.25):
        g = np.asarray(guess, float)
        g = m1 + (g - m1) * scale
        g = np.maximum(g, lo + 1e-9) if lower is not None else g
        sol = least_squares(resid, g, bounds=(lo, np.inf), xtol=1e-15,
                            ftol=1e-15, gtol=1e-15)
        err = float(np.max(np.abs(resid(sol.x))))
        if best is None or err < best[0]:
            best = (err, sol.x)
        if err < 1e-11:
            break
    err, z = best
    roots = np.sort(np.concatenate([np.repeat(fv, fm), np.repeat(z, gm)]))
    return roots, err


def _splits(rest):
    """candidate multiplicity vectors for the three free positions."""
    out = []
    for k in (1, 2, 3, 5):
        for m in (1, 2, 3):
            if rest - k - m >= 1:
                out.append([rest - k - m, k, m])
    for f in (0.9, 0.8, 0.6, 0.5):
        n1 = max(1, int(round(rest * f)))
        n2 = max(1, (rest - n1) // 2)
        n3 = rest - n1 - n2
        if n3 >= 1:
            out.append([n1, n2, n3])
    return out


def _fit(fixed_vals, fixed_mult, rest, guess, a, b, lower=None):
    m1, mu2, _ = X.forced_moments(a, b)
    best = (np.inf, None)
    for n in _splits(rest):
        for sc in (1.0, 1.5, 2.5, 0.7, 4.0):
            g = np.array(guess, float)
            g = m1 + (g - m1) * sc
            if lower is not None:
                g = np.maximum(g, lower + 1e-9)
            r, err = _fit_positions(fixed_vals, fixed_mult, n, g, a, b, lower)
            if err < best[0]:
                best = (err, r)
            if err < 1e-11:
                return best[1], best[0]
    return best[1], best[0]


def poly_witness(c, a, b, p):
    """degree-p real-rooted rho with the forced kappa_1..3 and > p/b roots at c."""
    n0 = p // b + 1
    if n0 / p > max_atom(c, a, b):
        return None, np.inf
    m1, mu2, _ = X.forced_moments(a, b)
    w = witness(c, n0 / p, a, b)
    guess = ([w[0][1], w[0][2], w[0][2] * 1.3] if w is not None
             else [m1, m1 + sqrt(mu2), m1 + 3 * sqrt(mu2)])
    return _fit([c], [n0], p - n0, guess, a, b, lower=c)


def poly_outlier(a, b, p, frac=0.55):
    """degree-p real-rooted rho with the forced kappa_1..3 and ONE far-left root."""
    m1, mu2, _ = X.forced_moments(a, b)
    D = frac * sqrt(p * mu2)
    return _fit([m1 - D], [1], p - 1,
                [m1, m1 + sqrt(mu2), m1 + 3 * sqrt(mu2)], a, b)


# ================================================================== drivers
def part_atom_cap():
    print("=" * 96)
    print("[E1] the Cauchy-Schwarz atom cap, and where it beats 1/b")
    print("=" * 96)
    print("  %-8s %-11s %-11s %-13s %-13s %-9s" %
          ("(a,b)", "tree edge", "c0(a,b)", "maxatom(c=0)", "maxatom(tree)",
           "1/b"))
    for (a, b) in [(3, 2), (4, 2), (5, 2), (6, 2), (3, 3), (4, 3), (5, 3),
                   (6, 3), (7, 3), (9, 3), (4, 4), (6, 4), (10, 4), (43, 4),
                   (5, 5), (9, 5), (12, 7), (20, 9)]:
        lo, _ = X.tree_band(a, b)
        print("  (%2d,%d)   %11.6f %11.6f %13.6f %13.6f %9.6f   %s"
              % (a, b, lo, c0(a, b), max_atom(0.0, a, b), max_atom(lo, a, b),
                 1.0 / b,
                 "atom mechanism kills (L)" if c0(a, b) < lo else
                 ("tree edge > 1: squeeze kills (L)" if lo > 1 else "-- neither --")))
    print()


def part_witness():
    print("=" * 96)
    print("[E2] EXPLICIT COUNTEREXAMPLES to (L) inside T(a,b), supp in [c,inf)")
    print("=" * 96)
    print("  %-8s %-9s %-8s %-30s %-10s %-10s %-9s" %
          ("(a,b)", "c", "mass@c", "atoms of tau", "L(tau)", "tree edge",
           "moment err"))
    bad = 0
    for (a, b) in [(3, 3), (4, 3), (5, 3), (6, 3), (4, 4), (6, 4), (10, 4),
                   (5, 5), (9, 5), (12, 7), (20, 9), (6, 6)]:
        lo, _ = X.tree_band(a, b)
        if c0(a, b) >= lo:
            continue
        # prefer a counterexample with supp(tau) contained in [0,inf)
        left = max(c0(a, b), 0.0) if lo > 0 else c0(a, b)
        left = max(left, lo - 0.35)
        c = 0.5 * (left + lo)
        cap = max_atom(c, a, b)
        s = 0.5 * (1.0 / b + cap)
        w = witness(c, s, a, b)
        if w is None:
            print("  (%2d,%d)  -- witness solve failed at c=%.4f" % (a, b, c))
            continue
        atoms, wts = w
        L = X.L_edge(atoms, wts, b)
        err = check_moments(atoms, wts, a, b)
        bad += (L < lo - 1e-9)
        print("  (%2d,%d)  %9.5f %8.5f %-30s %10.6f %10.6f %9.1e  (L)=%s"
              % (a, b, c, s,
                 "[" + ",".join("%.3f" % z for z in atoms) + "]",
                 L, lo, err,
                 ("%s  supp>=0=%s" % (L >= lo - 1e-9, atoms.min() >= -1e-12))))
    print("  -> (L) violated in %d of the cases above" % bad)
    print()


def part_rm_check():
    print("=" * 96)
    print("[E3] independent check of L_edge by random matrices (A + U B U*)")
    print("=" * 96)
    for (a, b, c) in [(4, 3, 0.0), (6, 4, 0.1), (9, 5, 0.3)]:
        lo, _ = X.tree_band(a, b)
        cap = max_atom(c, a, b)
        s = 0.5 * (1.0 / b + cap)
        w = witness(c, s, a, b)
        if w is None:
            continue
        atoms, wts = w
        L = X.L_edge(atoms, wts, b)
        m, sd = rm_free_edge(atoms, wts, b)
        print("  (a,b)=(%d,%d) c=%.2f  K-transform L=%.6f   random-matrix "
              "lambda_min = %.6f +- %.4f   tree edge %.6f"
              % (a, b, c, L, m, sd, lo))
    # and a control where the answer is known: chi boxplus chi^{boxplus(a-1)}
    print("  control: chi boxplus (a-1 atoms approximating chi^{boxplus(a-1)})")
    for (a, b) in [(4, 3), (6, 4)]:
        lo, _ = X.tree_band(a, b)
        print("     (a,b)=(%d,%d)  chi_power_edge = %.8f   closed form %.8f"
              % (a, b, X.chi_power_edge(a, b, 'min'), lo))
    print()


def part_poly():
    print("=" * 96)
    print("[E4] the counterexample as a genuine REAL-ROOTED POLYNOMIAL of degree p")
    print("     rho(x) = prod (x - r_i);  kappa_1,2,3 forced;  > p/b roots at c")
    print("=" * 96)
    for (a, b, c, p) in [(4, 3, 0.0, 30), (4, 3, 0.0, 60), (4, 3, 0.05, 60),
                         (5, 3, 0.1, 30), (6, 3, 0.6, 60), (6, 4, 0.12, 40),
                         (9, 5, 0.5, 40), (12, 7, 0.6, 42), (20, 9, 2.2, 45)]:
        lo, _ = X.tree_band(a, b)
        r, err = poly_witness(c, a, b, p)
        if r is None or err > 1e-8:
            print("  (a,b)=(%d,%d) p=%2d c=%.2f  no fit (err=%s)" % (a, b, p, c, err))
            continue
        L = X.L_roots(r, b)
        print("  (a,b)=(%d,%d) p=%2d c=%.3f  #roots at c = %d/%d > p/b   "
              "L=%9.6f  tree=%9.6f  (L)=%-5s  moment err %.1e  min root %.4f"
              % (a, b, p, c, int(np.sum(np.abs(r - c) < 1e-9)), p, L, lo,
                 L >= lo - 1e-9, err, r.min()))
    print()


def part_far_outlier():
    print("=" * 96)
    print("[E5] the crude counterexample: ONE far-left root, no support hypothesis")
    print("=" * 96)
    for (a, b, p) in [(3, 2, 40), (4, 2, 40), (5, 2, 40), (4, 3, 40), (7, 3, 40),
                      (6, 4, 40), (9, 5, 40), (3, 2, 200), (5, 2, 200)]:
        lo, _ = X.tree_band(a, b)
        r, err = poly_outlier(a, b, p)
        if err > 1e-8:
            print("  (a,b,p)=(%d,%d,%d) no fit (err %.1e)" % (a, b, p, err))
            continue
        L = X.L_roots(r, b)
        print("  (a,b)=(%d,%d) p=%3d  min root=%10.4f  L=%10.4f  tree=%8.5f  "
              "(L)=%-5s  moment err %.1e"
              % (a, b, p, r.min(), L, lo, L >= lo - 1e-9, err))
    print()


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', '1'):
        part_atom_cap()
    if which in ('all', '2'):
        part_witness()
    if which in ('all', '3'):
        part_rm_check()
    if which in ('all', '4'):
        part_poly()
    if which in ('all', '5'):
        part_far_outlier()
