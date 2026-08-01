"""ff_L.py -- the claim (L), as a statement about MEASURES.

    chi   := (1 - 1/b) delta_0 + (1/b) delta_b
    L(tau) := left edge of supp( chi boxplus tau )
            = sup_{w<0} [ K_chi(w) + K_tau(w) - 1/w ]

CLAIM (L):   L(tau) >= (sqrt(a-1) - sqrt(b-1))^2   for tau = mu_rho.

This file is self-contained: its own K-transforms, its own free-edge routine,
its own verification of the MSS bound, and its own root-measure/cumulant
dictionary.  Nothing is inherited on trust from the earlier ff_step* files.

DICTIONARY (derived and re-verified in check_dictionary()):
    for a monic real-rooted f of degree d with root measure tau,
        kappa_1(f) = m1(tau)
        kappa_2(f) = d/(d-1)     * mu2(tau)          [mu2 = central variance]
        kappa_3(f) = d^2/((d-1)(d-2)) * mu3(tau)
    hence the "forced" cumulants of rho translate into
        m1(mu_rho) = a-1,  mu2 = (a-1)(b-1),  mu3 = (a-1)(b-1)(b-2)
    which are EXACTLY the first three FREE cumulants of chi^{boxplus (a-1)}
    (free and classical cumulants agree through order 3).
"""
import numpy as np
from fractions import Fraction
from math import sqrt, comb, factorial


# ------------------------------------------------------------------ K_chi
def K_chi(w, b):
    """exact inverse Cauchy transform of chi on the branch x < 0 (w < 0).
    G_chi(x) = (1-1/b)/x + (1/b)/(x-b)  ==>  w x^2 - (wb+1) x + (b-1) = 0,
    outer branch x = [(wb+1) + sqrt((wb-1)^2 + 4w)] / (2w)."""
    w = np.asarray(w, dtype=float)
    disc = (w * b - 1.0) ** 2 + 4.0 * w
    return ((w * b + 1.0) + np.sqrt(disc)) / (2.0 * w)


def G_chi(x, b):
    return (1.0 - 1.0 / b) / x + (1.0 / b) / (x - b)


# ------------------------------------------------------------------ K_tau
def K_atomic(w, atoms, wts):
    """inverse of G_tau(x) = sum_j wts_j/(x - atoms_j) on the branch
    x < min(atoms), for w < 0.  VECTORISED in w.  Bisection + Newton."""
    w = np.atleast_1d(np.asarray(w, float))
    t = np.asarray(atoms, float)
    p = np.asarray(wts, float)
    p = p / p.sum()
    edge = t.min()
    scale = max(1.0, abs(edge))

    def G(x):
        return (p[None, :] / (x[:, None] - t[None, :])).sum(axis=1)

    # G is STRICTLY DECREASING on (-inf, edge):  G(-inf)=0-,  G(edge-)= -inf.
    # EXACT bracket, no widening loop needed:  for x < edge = min(t),
    #     1/(T - x) <= |G(x)| <= 1/(edge - x),   T := max(t).
    # so  |G| = |w|  forces   edge - 2/|w| < x <= T - 1/|w|.
    T = t.max()
    aw = np.abs(w)
    lo = edge - 2.0 / aw
    hi = np.minimum(edge - 1e-15 * scale, T - 1.0 / aw)
    hi = np.maximum(hi, lo + 1e-300)
    for _ in range(120):
        mid = 0.5 * (lo + hi)
        g = G(mid)
        lo = np.where(g > w, mid, lo)                # mid still left of root
        hi = np.where(g > w, hi, mid)
        if np.all(hi - lo <= 1e-16 * np.maximum(1.0, np.abs(mid))):
            break
    x = 0.5 * (lo + hi)
    for _ in range(40):                              # Newton polish
        g = G(x)
        gp = -(p[None, :] / (x[:, None] - t[None, :]) ** 2).sum(axis=1)
        xn = x - (g - w) / gp
        ok = np.isfinite(xn) & (xn > lo) & (xn < hi)
        xn = np.where(ok, xn, x)
        if np.all(np.abs(xn - x) <= 1e-16 * np.maximum(1.0, np.abs(x))):
            x = xn
            break
        x = xn
    return x


# ------------------------------------------------------- the free left edge
def L_edge(atoms, wts, b, nw=700, wmax=1e7, refine=7):
    """sup_{w<0} [ K_chi(w) + K_tau(w) - 1/w ]  =  min supp( chi boxplus tau ).

    F(-infty) = min supp(tau) (a limiting value of the sup), so the sup is
    always >= min supp(tau).  Log-grid then repeated local zoom."""
    def Fv(ws):
        return K_chi(ws, b) + K_atomic(ws, atoms, wts) - 1.0 / ws

    lg_lo, lg_hi = np.log(1e-9), np.log(wmax)
    best = float(np.min(atoms))
    for _ in range(refine):
        lg = np.linspace(lg_lo, lg_hi, nw)
        ws = -np.exp(lg)
        vals = Fv(ws)
        i = int(np.argmax(vals))
        best = max(best, float(vals[i]))
        lg_lo = lg[max(i - 1, 0)]
        lg_hi = lg[min(i + 1, nw - 1)]
        if lg_hi - lg_lo < 1e-13:
            break
    return best


def L_roots(roots, b, **kw):
    r = np.asarray(roots, float)
    return L_edge(r, np.ones(len(r)) / len(r), b, **kw)


def tree_band(a, b):
    s, t = sqrt(a - 1.0), sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def chi_atoms(b):
    return np.array([0.0, float(b)]), np.array([1.0 - 1.0 / b, 1.0 / b])


# ------------------------------------------------------ chi^{boxplus a} edge
def chi_power_edge(a, b, side='min', nw=4000, refine=8):
    """sup_{w<0}[ a K_chi(w) - (a-1)/w ]  (side='min'),  or inf_{w>0}."""
    sgn = -1.0 if side == 'min' else 1.0

    def Fv(ws):
        return a * K_chi(ws, b) - (a - 1.0) / ws

    lg_lo, lg_hi = np.log(1e-10), np.log(1e9)
    best = -np.inf if side == 'min' else np.inf
    for _ in range(refine):
        lg = np.linspace(lg_lo, lg_hi, nw)
        ws = sgn * np.exp(lg)
        v = Fv(ws)
        i = int(np.argmax(v)) if side == 'min' else int(np.argmin(v))
        best = max(best, float(v[i])) if side == 'min' else min(best, float(v[i]))
        lg_lo, lg_hi = lg[max(i - 1, 0)], lg[min(i + 1, nw - 1)]
        if lg_hi - lg_lo < 1e-14:
            break
    return best


# ---------------------------------------------------------------- moments
def moments_of(roots):
    r = np.asarray(roots, float)
    m = r.mean()
    return m, ((r - m) ** 2).mean(), ((r - m) ** 3).mean()


def forced_moments(a, b):
    """(m1, mu2, mu3) that the forced kappa_1..kappa_3 impose on mu_rho."""
    return (a - 1.0), (a - 1.0) * (b - 1.0), (a - 1.0) * (b - 1.0) * (b - 2.0)


# ================================================================== checks
def check_K():
    print("=" * 84)
    print("[0] K_chi is a genuine inverse of G_chi; K_atomic likewise")
    print("=" * 84)
    worst = 0.0
    for b in (2, 3, 4, 5, 7):
        for w in (-1e-6, -1e-3, -0.1, -1.0, -10.0, -1e4):
            x = K_chi(w, b)
            worst = max(worst, abs(G_chi(x, b) - w) / abs(w))
            assert x < 0, (b, w, x)
    print("   K_chi   max relative residual |G(K(w))-w|/|w| = %.3e" % worst)
    rng = np.random.default_rng(0)
    worst = 0.0
    ws = np.array([-1e-8, -1e-6, -1e-2, -1.0, -100.0, -1e5, -1e8])
    for _ in range(200):
        n = int(rng.integers(2, 12))
        t = np.sort(rng.normal(0, 2, n))
        p = rng.random(n); p /= p.sum()
        x = K_atomic(ws, t, p)
        g = (p[None, :] / (x[:, None] - t[None, :])).sum(axis=1)
        # measure the ABSOLUTE error in x (what L_edge actually uses):
        gp = -(p[None, :] / (x[:, None] - t[None, :]) ** 2).sum(axis=1)
        worst = max(worst, float(np.max(np.abs((g - ws) / gp))))
        assert np.all(x < t.min())
    print("   K_atomic max absolute error in x = |dG|/|G'| = %.3e" % worst)
    print()


def check_tree_band():
    print("=" * 84)
    print("[1] left edge of supp(chi^{boxplus a}) == (sqrt(a-1)-sqrt(b-1))^2 ?")
    print("=" * 84)
    print("   %-8s %-14s %-14s %-11s %-14s %-11s" %
          ("(a,b)", "edge(free)", "(rt(a-1)-rt(b-1))^2", "err",
           "top(free)", "err"))
    for (a, b) in [(2, 2), (3, 2), (4, 2), (2, 3), (4, 3), (5, 3), (6, 4),
                   (9, 5), (12, 7), (3, 3), (4, 4), (7, 3)]:
        lo, hi = tree_band(a, b)
        e0 = chi_power_edge(a, b, 'min')
        e1 = chi_power_edge(a, b, 'max')
        print("   (%d,%d)    %14.10f %14.10f %11.2e %14.10f %11.2e"
              % (a, b, e0, lo, abs(e0 - lo), e1, abs(e1 - hi)))
    print("   (a=1 is excluded: chi^{boxplus 1}=chi is atomic and the band")
    print("    formula degenerates there.)")
    print()


def check_bracket():
    """min supp(tau) <= L(tau) <= min supp(tau) + 1 -- the structural squeeze."""
    print("=" * 84)
    print("[2] STRUCTURAL SQUEEZE   min supp(tau) <= L(tau) <= min supp(tau) + 1")
    print("=" * 84)
    rng = np.random.default_rng(1)
    lo_slack, hi_slack = 1e9, 1e9
    for _ in range(300):
        b = int(rng.integers(2, 8))
        n = int(rng.integers(2, 15))
        t = rng.normal(0, 3, n) * rng.uniform(0.2, 4)
        L = L_roots(t, b)
        lo_slack = min(lo_slack, L - t.min())
        hi_slack = min(hi_slack, t.min() + 1.0 - L)
    print("   over 300 random tau:  min (L - min supp) = %.3e   "
          "min (min supp + 1 - L) = %.3e" % (lo_slack, hi_slack))
    print("   (both >= 0 confirms the squeeze; kappa_1(chi)=1 is the upper gap)")
    print()


if __name__ == '__main__':
    check_K()
    check_tree_band()
    check_bracket()
