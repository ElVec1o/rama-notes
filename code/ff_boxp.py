"""ff_boxp.py -- finite free convolution box_p, exact, plus finite free cumulants.

CONVENTION.  A monic degree-d polynomial is stored as its list of SIGNED
elementary symmetric functions:

    f(x) = sum_{i=0}^{d} (-1)^i e_i x^{d-i},     e_0 = 1,
    e_i = e_i(roots).

MSS finite free additive convolution (Marcus-Spielman-Srivastava):

    (f box_d g)(x) = sum_{k=0}^d (-1)^k x^{d-k} sum_{i+j=k}
                        (d-i)! (d-j)! / ( d! (d-k)! )  e_i(f) e_j(g).

KEY REWRITE (used everywhere below).  Put  E_i := e_i / C(d,i).  Then the
formula collapses to a BINOMIAL (exponential) convolution

    E_k(f box_d g) = sum_{i+j=k} C(k,i) E_i(f) E_j(g),

i.e. the exponential generating function  A_f(t) = sum_i E_i t^i / i!
satisfies   A_{f box g} = A_f * A_g.   Consequently

    L_f(t) := log A_f(t) = sum_{n>=1} khat_n(f) t^n / n!

has khat_n EXACTLY additive under box_d.  These are the finite free cumulants
up to normalisation; the normalisation that matches the classical free cumulants
(calibrated on the finite free Poisson, see kappa() below) is

    kappa_n(f) := (-1)^{n-1} d^{n-1} khat_n(f) / (n-1)!  ,   equivalently
    sum_{n>=1} kappa_n u^n / n = -(1/d) log A_f(-d u).

Sanity: kappa_1 = mean of roots; kappa_2 = d/(d-1) * variance of roots;
kappa_n((x-c)^d) = 0 for n >= 2; and box_d^q of x^{d-1}(x-1) has kappa_n = q/d
for every n, exactly (free Poisson of rate q/d).
"""
from fractions import Fraction
from math import comb, factorial

import numpy as np


# ------------------------------------------------------------------ box_d
def norm_coeffs(e, d):
    """e[0..d] signed-elementary -> E[i] = e_i / C(d,i)."""
    return [Fraction(e[i], 1) / comb(d, i) if not isinstance(e[i], Fraction)
            else e[i] / comb(d, i) for i in range(d + 1)]


def denorm_coeffs(E, d):
    return [E[i] * comb(d, i) for i in range(d + 1)]


def boxp(e1, e2, d):
    """finite free convolution of two monic degree-d polys, signed-e convention."""
    A = norm_coeffs(e1, d)
    B = norm_coeffs(e2, d)
    C = [Fraction(0)] * (d + 1)
    for k in range(d + 1):
        s = Fraction(0)
        for i in range(k + 1):
            s += comb(k, i) * A[i] * B[k - i]
        C[k] = s
    return denorm_coeffs(C, d)


def boxp_power(e, d, q):
    """q-fold box_d power, by repeated binomial convolution (exact)."""
    A = norm_coeffs(e, d)
    R = [Fraction(0)] * (d + 1)
    R[0] = Fraction(1)
    for _ in range(q):
        S = [Fraction(0)] * (d + 1)
        for k in range(d + 1):
            acc = Fraction(0)
            for i in range(k + 1):
                acc += comb(k, i) * R[i] * A[k - i]
            S[k] = acc
        R = S
    return denorm_coeffs(R, d)


# ------------------------------------------------------------- cumulants
def khat(e, d, nmax=None):
    """khat_1..khat_nmax from log of the EGF of E_i = e_i/C(d,i)."""
    if nmax is None:
        nmax = d
    nmax = min(nmax, d)
    E = norm_coeffs(e, d)
    # L = log A,  A' = L' A  =>  E_{n+1} = sum_{i=1}^{n+1} C(n,i-1) khat_i E_{n+1-i}
    kh = [Fraction(0)] * (nmax + 1)
    for n in range(0, nmax):
        acc = Fraction(0)
        for i in range(1, n + 1):
            acc += comb(n, i - 1) * kh[i] * E[n + 1 - i]
        kh[n + 1] = E[n + 1] - acc
    return kh


def kappa(e, d, nmax=None):
    """Finite free cumulants, normalised to converge to the classical FREE
    cumulants as d -> oo:

        kappa_n = (-1)^{n-1} d^{n-1} khat_n / (n-1)!    equivalently
        sum_{n>=1} kappa_n u^n / n  =  -(1/d) log A(-d u).

    Calibrated on p(x) = box_d^q ( x^{d-1}(x-1) ), which must give kappa_n = q/d
    for every n (free Poisson of rate q/d, jump 1).  Verified in ff_step0.py.
    """
    kh = khat(e, d, nmax)
    return [Fraction(0)] + [(-1) ** (n - 1) * Fraction(d) ** (n - 1) * kh[n]
                            / factorial(n - 1) for n in range(1, len(kh))]


# --------------------------------------------------------------- helpers
def signed_e_from_roots(roots):
    d = len(roots)
    e = [Fraction(0)] * (d + 1)
    e[0] = Fraction(1)
    for r in roots:
        for i in range(d, 0, -1):
            e[i] += Fraction(r) * e[i - 1]
    return e


def poly_from_signed_e(e, d):
    """numpy coefficient vector, highest power first: sum_i (-1)^i e_i x^{d-i}."""
    return np.array([float((-1) ** i * e[i]) for i in range(d + 1)])


def moments_from_e(e, d, nmax):
    """power sums / d  (empirical moments of the roots) from signed e_i, Newton."""
    p = [Fraction(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        s = Fraction(0)
        for i in range(1, n):
            s += (-1) ** (i - 1) * e[i] * p[n - i]
        if n <= d:
            s += (-1) ** (n - 1) * n * e[n]
        p[n] = s
    return [x / d for x in p[1:]]


def proj_charpoly(p, b):
    """signed e of  x^{p-b} (x-1)^b."""
    return [Fraction(comb(b, i)) for i in range(p + 1)]


# --------------------------------------------- reconstruction from cumulants
def khat_from_kappa(kap, d):
    """inverse of kappa(): khat_n = (-1)^{n-1} (n-1)! kappa_n / d^{n-1}."""
    return [Fraction(0)] + [(-1) ** (n - 1) * factorial(n - 1) * kap[n]
                            / Fraction(d) ** (n - 1) for n in range(1, len(kap))]


def poly_from_khat(kh, d):
    """E = exp(L) as EGFs, then e_i = E_i C(d,i)."""
    E = [Fraction(0)] * (d + 1)
    E[0] = Fraction(1)
    for n in range(0, d):
        acc = Fraction(0)
        for i in range(1, n + 2):
            ki = kh[i] if i < len(kh) else Fraction(0)
            acc += comb(n, i - 1) * ki * E[n + 1 - i]
        E[n + 1] = acc
    return [E[i] * comb(d, i) for i in range(d + 1)]


def poly_from_kappa(kap, d):
    return poly_from_khat(khat_from_kappa(kap, d), d)


def ff_root(e, d, a):
    """the formal finite free a-th root: the unique monic degree-d polynomial
    phi with kappa_n(phi) = kappa_n(e)/a.  (Real-rootedness is NOT automatic.)"""
    k = kappa(e, d, d)
    k2 = [Fraction(0)] + [k[n] / a for n in range(1, len(k))]
    return poly_from_kappa(k2, d)


# ------------------------------------------------ EXACT real-root localisation
def _taylor_shift(c, t):
    """c = coefficients, highest power first (exact); return coeffs of f(x+t).
    Horner / repeated synthetic division.  Validated in ff_boxp self-test."""
    d = len(c) - 1
    out = list(c)
    for k in range(d):
        for i in range(1, d + 1 - k):
            out[i] += t * out[i - 1]
    return out


def coeffs_from_signed_e(e, d):
    """highest power first: [1, -e_1, e_2, -e_3, ...]"""
    return [Fraction((-1) ** i) * Fraction(e[i]) for i in range(d + 1)]


def all_roots_above(e, d, t):
    """EXACT test, valid for REAL-ROOTED f:  min root of f > t ?
    f(x+t) then has all roots > 0, hence strictly alternating coefficients."""
    g = _taylor_shift(coeffs_from_signed_e(e, d), Fraction(t))
    for i, v in enumerate(g):
        if v * (-1) ** i <= 0:
            return False
    return True


def all_roots_below(e, d, t):
    """EXACT test, valid for REAL-ROOTED f: max root of f < t ?
    f(x+t) has all roots < 0, hence all coefficients positive."""
    g = _taylor_shift(coeffs_from_signed_e(e, d), Fraction(t))
    return all(v > 0 for v in g)


def minroot_exact(e, d, lo=None, hi=None, iters=60):
    """bisection for the smallest root of a real-rooted f (exact sign tests)."""
    if lo is None:
        lo = Fraction(0)
        while not all_roots_above(e, d, lo):
            lo = lo * 2 - 1 if lo < 0 else Fraction(-1)
    lo, hi = Fraction(lo), Fraction(hi if hi is not None else Fraction(e[1], d))
    for _ in range(iters):
        mid = (lo + hi) / 2
        if all_roots_above(e, d, mid):
            lo = mid
        else:
            hi = mid
    return float(lo)


def maxroot_exact(e, d, lo=None, hi=None, iters=60):
    lo = Fraction(lo if lo is not None else Fraction(e[1], d))
    if hi is None:
        hi = Fraction(1)
        while not all_roots_below(e, d, hi):
            hi *= 2
    hi = Fraction(hi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if all_roots_below(e, d, mid):
            hi = mid
        else:
            lo = mid
    return float(hi)


# ------------------------------------------------------- high precision roots
def roots_hp(e, d, dps=None):
    """Roots of sum_i (-1)^i e_i x^{d-i} at high precision (exact Fractions in).
    Returns (min_real, max_real, max_abs_imag) as floats."""
    import mpmath as mp
    if dps is None:
        mag = max(1, max(len(str(abs(Fraction(x).numerator))) for x in e))
        dps = max(60, 3 * mag + 4 * d)
    with mp.workdps(dps):
        c = [mp.mpf(Fraction(e[i]).numerator) / mp.mpf(Fraction(e[i]).denominator)
             * (-1) ** i for i in range(d + 1)]
        r = mp.polyroots(c, maxsteps=200, extraprec=40 * d)
        re = [float(mp.re(z)) for z in r]
        im = [abs(float(mp.im(z))) for z in r]
    return min(re), max(re), max(im)


def scalar_family_e(p, q, a, b):
    """EXACT mu for the scalar family A_k = (b/p) I_p (rank p, trace b, sum aI):
        e_m = C(q,m) (b/p)^m p!/(p-m)! .
    (Generalised Laguerre; the family that attains the Marchenko-Pastur edges.)"""
    c = Fraction(b, p)
    e = [Fraction(0)] * (p + 1)
    ff = Fraction(1)
    for m in range(p + 1):
        if m > 0:
            ff *= (p - m + 1)
        e[m] = comb(q, m) * c ** m * ff
    return e
