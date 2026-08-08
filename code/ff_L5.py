"""ff_L5.py -- can MORE cumulants rescue (L)?

The brief's candidate rescues, tested in order:
  (a) an upper bound on kappa_4(rho);
  (b) support containment  supp(mu_rho) in [0, ab];
  (c) matching the first n free cumulants of chi^{boxplus (a-1)} for n > 3.

METHOD.  For a class defined by "first n moments equal to those of
chi^{boxplus (a-1)}, support in [c, C]", the LP

      max tau({c})   s.t.  sum w_i x_i^j = m_j (j=0..n),  w >= 0

is a truncated Hausdorff moment problem; its value exceeds 1/b exactly when
the atom mechanism (Bercovici-Voiculescu) forces L(tau) = c, killing (L).
"""
import sys
from fractions import Fraction
from math import sqrt

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
import ff_L as X                                                               # noqa
import ff_L2 as Y                                                              # noqa
import ff_L3 as W                                                              # noqa


# -------------------------------------------- free cumulants -> raw moments
def nc_partitions(n):
    """all non-crossing partitions of {0..n-1} as lists of block sizes."""
    if n == 0:
        yield []
        return
    # recursive: the block containing 0 splits the rest into intervals
    def rec(elts):
        if not elts:
            yield []
            return
        first = elts[0]
        rest = elts[1:]
        for k in range(len(rest) + 1):
            for sub in _combos(rest, k):
                blk = [first] + list(sub)
                gaps = _gaps(elts, blk)
                for parts in _prod([list(rec(g)) for g in gaps]):
                    out = [blk]
                    for pp in parts:
                        out += pp
                    yield out
    yield from rec(list(range(n)))


def _combos(seq, k):
    from itertools import combinations
    return combinations(seq, k)


def _gaps(elts, blk):
    """the maximal runs of elts strictly between consecutive members of blk"""
    pos = {e: i for i, e in enumerate(elts)}
    idx = sorted(pos[b] for b in blk)
    out = []
    for i in range(len(idx) - 1):
        g = elts[idx[i] + 1:idx[i + 1]]
        if g:
            out.append(g)
    tail = elts[idx[-1] + 1:]
    if tail:
        out.append(tail)
    return out


def _prod(lists):
    from itertools import product
    return product(*lists) if lists else [()]


def moments_from_free_cumulants(kap, n):
    """m_1..m_n from free cumulants kap[1..n] via non-crossing partitions."""
    m = []
    for k in range(1, n + 1):
        s = 0.0
        for part in nc_partitions(k):
            t = 1.0
            for blk in part:
                t *= kap[len(blk)]
            s += t
        m.append(s)
    return m


def chi_free_cumulants(b, n):
    """free cumulants of chi = (1-1/b)delta_0 + (1/b)delta_b.
    chi is the b*(free Bernoulli): R_chi(w) = (K_chi(w) - 1/w); expand."""
    # exact: R_chi(w) solves  w x^2 - (wb+1)x + (b-1) = 0 with x = 1/w + R.
    # substitute and expand in powers of w with sympy.
    import sympy as sp
    wv = sp.symbols('w')
    R = sp.Function('R')
    # series solve: x = 1/w + r(w),  w x^2 - (wb+1)x + (b-1) = 0
    r = sum(sp.symbols('r1:%d' % (n + 2))[i] * wv ** i for i in range(n + 1))
    x = 1 / wv + r
    expr = sp.expand(wv * x ** 2 - (wv * b + 1) * x + (b - 1))
    ser = sp.Poly(sp.expand(expr * wv), wv)
    sols = {}
    eqs = []
    co = sp.expand(expr).as_poly(wv)
    for k in range(0, n + 1):
        eqs.append(sp.expand(expr).coeff(wv, k))
    sol = sp.solve(eqs[:n + 1], sp.symbols('r1:%d' % (n + 2))[:n + 1], dict=True)
    s0 = sol[0]
    syms = sp.symbols('r1:%d' % (n + 2))
    return [0.0] + [float(s0[syms[i]]) for i in range(n)]


def target_moments(a, b, n):
    """raw moments m_1..m_n of chi^{boxplus (a-1)}."""
    kc = chi_free_cumulants(b, n)
    kap = [0.0] + [(a - 1) * kc[j] for j in range(1, n + 1)]
    return moments_from_free_cumulants(kap, n)


# --------------------------------------------------------------------- LP
def max_atom_lp(c, C, mom, n_grid=6001):
    """max tau({c}) over measures on [c,C] with raw moments mom (m_1..m_n)."""
    xs = np.linspace(c, C, n_grid)
    A = np.vstack([np.ones(n_grid)] + [xs ** j for j in range(1, len(mom) + 1)])
    bvec = np.array([1.0] + list(mom))
    obj = np.zeros(n_grid)
    obj[0] = -1.0
    res = linprog(obj, A_eq=A, b_eq=bvec, bounds=[(0, 1)] * n_grid,
                  method='highs')
    if not res.success:
        return None, None
    w = res.x
    keep = w > 1e-9
    return float(w[0]), (xs[keep], w[keep])


def scan():
    print("=" * 108)
    print("[K] how many matched free cumulants does it take to kill the atom "
          "mechanism?")
    print("    class: supp(tau) in [c, ab], first n moments = those of "
          "chi^{boxplus(a-1)}")
    print("=" * 108)
    print("  %-8s %-9s %-8s %-9s %s" % ("(a,b)", "c", "1/b", "tree lo",
                                        "max tau({c}) for n = 3,4,5,6,7"))
    for (a, b) in [(4, 3), (5, 3), (6, 3), (7, 3), (6, 4), (10, 4), (9, 5),
                   (12, 7), (3, 2), (4, 2), (5, 2)]:
        lo, _ = X.tree_band(a, b)
        c = max(0.0, lo * 0.99)
        row = []
        for n in (3, 4, 5, 6, 7):
            mom = target_moments(a, b, n)
            s, _ = max_atom_lp(c, float(a * b), mom)
            row.append(s if s is not None else float('nan'))
        print("  (%2d,%d)   %9.5f %8.5f %9.5f  %s   -> atom mechanism alive up "
              "to n = %s"
              % (a, b, c, 1.0 / b, lo,
                 " ".join("%7.4f" % v for v in row),
                 max([n for n, v in zip((3, 4, 5, 6, 7), row)
                      if v > 1.0 / b + 1e-9], default=None)))
    print()


def kappa4_survey():
    print("=" * 108)
    print("[K4] kappa_4(rho): genuine families vs the counterexamples")
    print("=" * 108)
    print("  %-30s %-11s %-12s %-12s %-12s" %
          ("object", "(p,a,b)", "kappa_4(rho)", "(a-1)k4(psi0)", "L vs tree"))
    for nm, p, q, a, b, e in Y.families():
        if p < 5:
            continue
        rho = Y.deconv(e, Y.psi0(p, b), p)
        k = F.kappa(rho, p, 4)
        kpsi = F.kappa(Y.psi0(p, b), p, 4)
        r = np.roots(F.poly_from_signed_e(rho, p))
        rr = float(np.max(np.abs(r.imag))) / max(1.0, float(np.max(np.abs(r)))) < 1e-7
        L = X.L_roots(np.sort(r.real), b) if rr else float('nan')
        lo, _ = X.tree_band(a, b)
        print("  %-30s (%2d,%d,%d)   %12.5f %12.5f  L=%8.5f tree=%8.5f %s"
              % (nm, p, a, b, float(k[4]), float((a - 1) * kpsi[4]), L, lo,
                 "" if rr else "(rho not real-rooted)"))
    print("  --- counterexamples ---")
    for (a, b, c, p) in [(4, 3, 0.0, 60), (4, 3, 0.05, 60), (6, 4, 0.12, 40),
                         (9, 5, 0.5, 40)]:
        r, err = W.poly_witness(c, a, b, p)
        if r is None or err > 1e-8:
            continue
        e = F.signed_e_from_roots([Fraction(x).limit_denominator(10 ** 12)
                                   for x in r])
        k = F.kappa(e, p, 4)
        kpsi = F.kappa(Y.psi0(p, b), p, 4)
        lo, _ = X.tree_band(a, b)
        print("  %-30s (%2d,%d,%d)   %12.5f %12.5f  L=%8.5f tree=%8.5f"
              % ("counterexample c=%.2f" % c, p, a, b, float(k[4]),
                 float((a - 1) * kpsi[4]), X.L_roots(r, b), lo))
    print()


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', 'K'):
        scan()
    if which in ('all', '4'):
        kappa4_survey()
