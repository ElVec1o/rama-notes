"""sr_rigid.py -- NEW linear consequences of (ii) + real stability.

PROPOSITION R (proved here, verified below).  Let s = (s_1..s_q) satisfy
(ii) s_k ~ Bin(b,1/a) for every k and (iii) G(z) = E prod z_k^{s_k} real
stable.  Then for ALL k and l,

        H_{k,l}(w) := E[ s_l w^{s_k} ]   is divisible by  (w + a - 1)^{b-1}.

Equivalently  d^m/dw^m E[s_l w^{s_k}] = 0 at w = 1-a for m = 0,...,b-2, i.e.

        E[ s_l (s_k)_m (1-a)^{s_k - m} ] = 0,        m = 0, ..., b-2,

where (x)_m is the falling factorial.  For l = k this is automatic; for l != k
it is a NEW linear constraint on the law, invisible to (i)+(ii).

PROOF.  Fix k != l.  Put z_k = w, z_l = 1 + eps, all other coordinates 1, and
let psi(w,eps) = G(...).  Real stability of G implies that for every real eps
the univariate w |-> psi(w,eps) is real rooted (real stable polynomials are
real rooted in each variable when the others are given real values).  By (ii),
psi(w,0) = a^{-b}(w+a-1)^b, which has a b-fold root at w_0 = 1-a, and its
leading coefficient a^{-b} is nonzero, so for small eps all b roots of
psi(.,eps) stay near w_0.  Write w = w_0 + delta and expand:

   psi(w_0+delta, eps) = a^{-b} delta^b + eps H_{k,l}(w_0+delta) + O(eps^2)
                       = a^{-b} delta^b
                         + eps [ H(w_0) + H'(w_0) delta + ... ] + O(eps^2).

Suppose H(w_0), ..., H^{(m-1)}(w_0) all vanish but H^{(m)}(w_0) != 0 for some
m <= b-2.  The Newton polygon of the two dominant terms  a^{-b} delta^b  and
eps H^{(m)}(w_0) delta^m / m!  gives  delta^{b-m} ~ -eps a^b H^{(m)}(w_0)/m! ,
i.e. b-m >= 2 branches equal to the (b-m)-th roots of a nonzero number times
eps.  For b-m >= 3 at most two of those branches are real, for either sign of
eps; for b-m = 2 the two branches are purely imaginary for one of the two
signs of eps.  Either way psi(.,eps) has a non-real root for arbitrarily small
real eps, contradicting real stability.  (The dropped O(eps^2) and higher
delta terms lie strictly above that Newton segment: with delta ~ eps^{1/(b-m)}
the term eps^2 has weight 2 > 1 and eps*delta^{m+1} has weight
1 + 1/(b-m) > 1 only in the delta direction, both dominated.)  Hence
H^{(m)}(w_0) = 0 for all m <= b-2.  QED

CONSEQUENCE.  These constraints are LINEAR in the law and they are NOT implied
by (i)+(ii).  However -- and this is the reason the LP of sr_lp2.py cannot see
them -- their S_q-symmetrisation IS implied: summing over l != k gives
E[(p - s_k) w^{s_k}] = a^{-b}(w+a-1)^{b-1}[p(w+a-1) - wb], already divisible.
So Proposition R is exactly a piece of stability that symmetrisation destroys,
and any LP over exchangeable laws is blind to it.
"""
import sys
import numpy as np
from math import comb
from itertools import combinations

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import (band, binom_pmf, law_from_family, graph_family,
                      rand_proj_family, icosahedral_rank2, epoly)        # noqa
from frac_naimark import GRAPHS, degrees_ok                              # noqa
from sr_collapse import hypergeom_block_law                              # noqa


def H_poly(W, S, k, l, b):
    """coefficients of H_{k,l}(w) = E[s_l w^{s_k}], ascending in w."""
    h = np.zeros(b + 1)
    np.add.at(h, S[:, k], W * S[:, l])
    return h


def div_order(h, a, tol=1e-9):
    """order of vanishing of h(w) at w = 1-a (numerically)."""
    w0 = 1.0 - a
    scale = max(1.0, np.abs(h).sum())
    m = 0
    c = h.copy()
    while len(c) > 0:
        v = np.polyval(c[::-1], w0)
        if abs(v) > tol * scale:
            break
        m += 1
        c = np.polyder(c[::-1])[::-1]
    return m


def report_family(name, W, S, p, q, a, b):
    orders = np.zeros((q, q), dtype=int)
    for k in range(q):
        for l in range(q):
            orders[k, l] = div_order(H_poly(W, S, k, l, b), a)
    off = orders[~np.eye(q, dtype=bool)]
    print(f"   {name:34s} (p,q,a,b)=({p},{q},{a},{b})  b-1 = {b-1}")
    print(f"      order of vanishing of H_kl at w=1-a:  diagonal "
          f"{sorted(set(orders.diagonal().tolist()))}, "
          f"off-diagonal {sorted(set(off.tolist()))}   "
          f"{'OK (>= b-1)' if off.min() >= b-1 else '*** FAILS ***'}")
    return orders


def second_order_probe(W, S, p, q, a, b):
    """How far does the vanishing go for MIXED derivatives?
    E[(s_l)_m1 (s_l')_m2 ... (1-a)^{s_k}]"""
    w0 = 1.0 - a
    res = {}
    for (l1, l2) in [(1, 2)]:
        k = 0
        if q < 3:
            return res
        val = float(np.sum(W * S[:, l1] * S[:, l2] * (w0 ** S[:, k])))
        res['E[s_l s_l\' (1-a)^{s_k}]'] = val
    k = 0
    res['E[(1-a)^{s_k}]'] = float(np.sum(W * (w0 ** S[:, k])))
    res['E[s_1 (1-a)^{s_0}]'] = float(np.sum(W * S[:, 1] * (w0 ** S[:, 0])))
    res['E[s_1 s_0 (1-a)^{s_0}]'] = float(np.sum(W * S[:, 1] * S[:, 0] *
                                                 (w0 ** S[:, 0])))
    if q >= 2:
        res['E[(1-a)^{s_0+s_1}]'] = float(np.sum(W * (w0 ** (S[:, 0] + S[:, 1]))))
        res['E[s_2 (1-a)^{s_0+s_1}]'] = float(np.sum(W * S[:, 2] *
                                                     (w0 ** (S[:, 0] + S[:, 1])))) \
            if q >= 3 else None
    return res


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("VERIFY PROPOSITION R on projection families")
    print("=" * 78)
    for name, (adj, p, q, a, b) in GRAPHS.items():
        W, S = law_from_family(graph_family(adj, p, q, a, b), a, b)
        report_family(name, W, S, p, q, a, b)
    P, p, q, a, b = icosahedral_rank2()
    W, S = law_from_family(P, a, b)
    report_family('icosahedral', W, S, p, q, a, b)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (5, 5, 3, 3),
                         (4, 5, 5, 4)]:
        P, r = rand_proj_family(p, q, a, b, seed=91 * p + 7 * q)
        W, S = law_from_family(P, a, b)
        report_family(f'random (res {r:.0e})', W, S, p, q, a, b)
    print()

    print("=" * 78)
    print("HOW FAR DOES THE DEGENERACY GO?  (mixed evaluations at w = 1-a)")
    print("=" * 78)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (5, 5, 3, 3)]:
        P, r = rand_proj_family(p, q, a, b, seed=17 * p + 3 * q)
        W, S = law_from_family(P, a, b)
        d = second_order_probe(W, S, p, q, a, b)
        print(f"   ({p},{q},{a},{b}):")
        for key, v in d.items():
            if v is None:
                continue
            print(f"       {key:30s} = {v: .6e}")
    print()

    print("=" * 78)
    print("CONTROL: does the NA counterexample (permutation law) satisfy R?")
    print("   ((6,9,3,2), composition (2,1,1,1,1,0,0,0,0) in uniform random")
    print("   order -- exact Bin(2,1/3) marginals, sum = 6, NOT stable)")
    print("=" * 78)
    from itertools import permutations
    lam = [2, 1, 1, 1, 1, 0, 0, 0, 0]
    perms = sorted(set(permutations(lam)))
    S = np.array(perms, dtype=int)
    W = np.full(len(perms), 1.0 / len(perms))
    a, b, p, q = 3, 2, 6, 9
    o = report_family('NA counterexample (permutation)', W, S, p, q, a, b)
    print(f"      H_01(w) coefficients: {H_poly(W,S,0,1,b)}  "
          f"value at w=1-a: {np.polyval(H_poly(W,S,0,1,b)[::-1], 1.0-a):.6f}")
    print("      ==> Proposition R HOLDS for it.  That is not a bug: R is")
    print("          VACUOUS on exchangeable laws (summing over l != k gives")
    print("          E[(p-s_k)w^{s_k}], already divisible), and the permutation")
    print("          law is exchangeable.  R only constrains laws that are NOT")
    print("          exchangeable -- exactly the information symmetrisation")
    print("          destroys.  The permutation law is still excluded by (iii)")
    print("          via the complex-rooted 2-block pgf (na_counterexample.py).")
    print()

    print("=" * 78)
    print("CONTROL: the hypergeometric (uniform p-subset) law -- SR but the")
    print("   marginals are NOT Bin(b,1/a), so R need not (and does not) hold")
    print("=" * 78)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2)]:
        W, S = hypergeom_block_law(q * b, b, p, q)
        report_family('hypergeometric blocks', W, S, p, q, a, b)
