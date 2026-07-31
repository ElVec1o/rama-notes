"""ff_cumulants.py -- finite free cumulants of mu[P] for the tight-fusion-frame
class, exact in (p,q,a,b) where they are universal, and numeric where they are not.

BACKGROUND (established earlier in this project, dpp_rep.py):
    y^{q-p} mu(y) = E_S prod_{k=1}^q ( y - a s_k ),  s_k = |S cap B_k|,
    S ~ DPP(Pi), and s_k ~ Binomial(b, 1/a) EXACTLY for every k.
Hence, with mu(y) = sum_m (-1)^m e_m y^{p-m},

    e_m = a^m E[ e_m(s_1..s_q) ].

Newton's identities express e_1,e_2,e_3 through p_1,p_2,p_3 LINEARLY, and
E p_j = q * E[s^j] is a MARGINAL quantity -> universal in (p,q,a,b).
e_4 is the first to contain E[p_2^2], a genuine PAIR correlation -> family dependent.
"""
import sys
from fractions import Fraction
from math import comb

import numpy as np
import sympy as sp

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from ff_boxp import kappa, khat, norm_coeffs                                 # noqa
from mcp2 import mcp                                                         # noqa
from frac_naimark import GRAPHS, nu_coeffs, degrees_ok                       # noqa
from dpp_rep import rand_proj_family, graph_family, noncommutativity         # noqa


# ---------------------------------------------------------------- symbolic
def symbolic_e():
    """exact e_1,e_2,e_3 of mu in terms of (p,a,b)  [q = p a / b]."""
    p, a, b = sp.symbols('p a b', positive=True)
    q = p * a / b
    th = 1 / a
    # binomial(b, 1/a) raw moments via falling factorials
    mu1 = b * th
    mu2 = b * (b - 1) * th ** 2 + b * th
    mu3 = b * (b - 1) * (b - 2) * th ** 3 + 3 * b * (b - 1) * th ** 2 + b * th
    mu4 = (b * (b - 1) * (b - 2) * (b - 3) * th ** 4
           + 6 * b * (b - 1) * (b - 2) * th ** 3
           + 7 * b * (b - 1) * th ** 2 + b * th)
    P1 = p                                   # deterministic
    E2, E3, E4 = q * mu2, q * mu3, q * mu4   # E[p_2], E[p_3], E[p_4]
    e1 = a * P1
    e2 = a ** 2 * (P1 ** 2 - E2) / 2
    e3 = a ** 3 * (P1 ** 3 - 3 * P1 * E2 + 2 * E3) / 6
    return p, a, b, [sp.simplify(sp.expand(x)) for x in (e1, e2, e3)], (E2, E3, E4)


def symbolic_kappas():
    """kappa_1,kappa_2,kappa_3 of mu in closed form (p,a,b)."""
    p, a, b, (e1, e2, e3), _ = symbolic_e()
    E = [sp.Integer(1),
         e1 / sp.binomial(p, 1), e2 / sp.binomial(p, 2), e3 / sp.binomial(p, 3)]
    # khat from log EGF:  khat_{n+1} = E_{n+1} - sum_{i=1}^{n} C(n,i-1) khat_i E_{n+1-i}
    kh = [sp.Integer(0)] * 4
    for n in range(3):
        acc = sum(sp.binomial(n, i - 1) * kh[i] * E[n + 1 - i] for i in range(1, n + 1))
        kh[n + 1] = sp.simplify(E[n + 1] - acc)
    kap = [sp.Integer(0)] + [sp.simplify(sp.factor((-1) ** (n - 1) * p ** (n - 1)
                                                   * kh[n] / sp.factorial(n - 1)))
                             for n in range(1, 4)]
    return p, a, b, kap


# ---------------------------------------------------------------- numeric
def signed_e_of_mu(mu):
    p = len(mu) - 1
    return [(-1) ** m * mu[m] for m in range(p + 1)]


def exact_signed_e_graph(adj, p, q):
    """exact integer e_m for a graph family: e_m = m(G,m) matching numbers."""
    c = nu_coeffs(adj, p, q)              # c[j] = coeff of y^j
    return [Fraction((-1) ** m * c[p - m]) for m in range(p + 1)]


def all_families(extra_random=True):
    fams = []
    for name, (adj, p, q, a, b) in GRAPHS.items():
        assert degrees_ok(adj, p, q, a, b), name
        fams.append(('G ' + name, p, q, a, b, exact_signed_e_graph(adj, p, q)))
    if extra_random:
        for (p, q, a, b, seed) in [(4, 6, 3, 2, 5), (4, 6, 3, 2, 17),
                                   (6, 8, 4, 3, 9), (6, 8, 4, 3, 23),
                                   (6, 9, 3, 2, 3), (8, 12, 3, 2, 4),
                                   (5, 10, 4, 2, 7), (6, 10, 5, 3, 12),
                                   (4, 8, 4, 2, 31), (6, 12, 4, 2, 33),
                                   (8, 12, 6, 4, 41)]:
            P, r = rand_proj_family(p, q, a, b, seed=seed)
            if r > 1e-11:
                continue
            e = [Fraction(x).limit_denominator(10 ** 9)
                 for x in signed_e_of_mu(mcp(np.asarray(P, float)))]
            fams.append(('R (%d,%d,%d,%d) s%d nc=%.2f' % (p, q, a, b, seed,
                                                          noncommutativity(P)),
                         p, q, a, b, e))
    return fams


def report():
    p_, a_, b_, kap = symbolic_kappas()
    print("=" * 78)
    print("EXACT UNIVERSAL FINITE FREE CUMULANTS OF mu   (d = p, q = pa/b)")
    print("=" * 78)
    for n in (1, 2, 3):
        print("  kappa_%d = %s" % (n, sp.simplify(kap[n])))
    print()
    print("  large-p limits:")
    for n in (1, 2, 3):
        print("    kappa_%d -> %s" % (n, sp.simplify(sp.limit(kap[n], p_, sp.oo))))
    print()

    print("=" * 78)
    print("NUMERICAL CHECK across families:  kappa_1..kappa_5")
    print("=" * 78)
    subs = lambda expr, p, a, b: float(expr.subs({p_: p, a_: a, b_: b}))
    hdr = "%-34s %8s %10s %12s %14s %14s" % ("family", "k1", "k2", "k3", "k4", "k5")
    print(hdr)
    for name, p, q, a, b, e in all_families():
        k = kappa(e, p, min(5, p))
        row = "%-34s" % name
        for n in range(1, 6):
            row += " %13.6g" % (float(k[n]) if n < len(k) else float('nan'))
        print(row)
        # universality check
        ok = []
        for n in (1, 2, 3):
            if n < len(k):
                ok.append(abs(float(k[n]) - subs(kap[n], p, a, b)) < 1e-6 *
                          max(1.0, abs(subs(kap[n], p, a, b))))
        print("      universal k1..k3 match:", ok)


if __name__ == '__main__':
    report()
