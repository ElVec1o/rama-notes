"""profile_pgf.py -- the mixed characteristic polynomial is the joint pgf of the
HIGH-OCCUPANCY PROFILE of S, evaluated on an explicit rational curve.

From  y^{q-p} mu(y) = E prod_k (y - a s_k)  and the two deterministic identities
sum_k s_k = p, sum_k 1 = q, write n_j = #{k : s_k = j}.  Then
    n_1 = p - sum_{j>=2} j n_j ,     n_0 = q-p + sum_{j>=2} (j-1) n_j ,
so prod_k (y - a s_k) = y^{q-p} (y-a)^p prod_{j>=2} theta_j(y)^{n_j} with

    theta_j(y) = y^{j-1} (y - a j) / (y - a)^j .

Hence   THEOREM C:
    mu[P_1..P_q](y) = (y-a)^p * Psi( theta_2(y), ..., theta_b(y) ),
    Psi(u_2..u_b) = E prod_{j>=2} u_j^{n_j}   (joint pgf of (n_2..n_b)).

Degree count: sum_{j>=2}(j-1)n_j <= (p - n_1)/1 ... the polynomial identity is
exact.  For b = 2 there is a single variable and

    mu(y) = (y-a)^p Psi(theta),  theta = 1 - a^2/(y-a)^2,   Psi(u) = E u^{n_2}.

MSS real-rootedness of mu then forces Psi to be real-rooted with roots <= 0,
i.e. n_2 = # doubly-occupied blocks is a SUM OF INDEPENDENT BERNOULLIS,
n_2 ~ sum_i Bern(pi_i), and

    lambda_max = a (1 + sqrt(pi_max)),   lambda_min = a (1 - sqrt(pi_max)).

So at b=2 the band  [(sqrt(a-1)-1)^2, (sqrt(a-1)+1)^2]  is EXACTLY EQUIVALENT to

    (INEQ-2)      pi_max  <=  4(a-1)/a^2 .
"""
import sys
import numpy as np
from itertools import combinations
from math import comb

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from mcp2 import mcp, restore_proj, rand_X, proj_from_X                  # noqa
from frac_naimark import GRAPHS, degrees_ok                              # noqa
from dpp_rep import (naimark_slots, dpp_data, band, graph_family,        # noqa
                     rand_proj_family, noncommutativity)


def profile_law(w, svec, b, q):
    """law of the profile (n_2,...,n_b) as a dict {tuple: prob}."""
    out = {}
    for wt, s in zip(w, svec):
        if wt <= 0:
            continue
        prof = tuple(int((s == j).sum()) for j in range(2, b + 1))
        out[prof] = out.get(prof, 0.0) + wt
    return out


def mu_from_profile(law, p, a, b, y):
    """(y-a)^p * Psi(theta_2(y),..,theta_b(y)) evaluated at scalar/array y."""
    y = np.asarray(y, dtype=float)
    tot = np.zeros_like(y)
    for prof, wt in law.items():
        term = np.ones_like(y)
        for idx, j in enumerate(range(2, b + 1)):
            th = y ** (j - 1) * (y - a * j) / (y - a) ** j
            term = term * th ** prof[idx]
        tot = tot + wt * term
    return (y - a) ** p * tot


def psi_poly_b2(law, p):
    """b=2: coefficient list of Psi(u) = E u^{n_2}, index = power of u."""
    J = max(k[0] for k in law)
    c = np.zeros(J + 1)
    for prof, wt in law.items():
        c[prof[0]] += wt
    return c


def check(name, P, a, b, verbose=True):
    q, p, _ = P.shape
    U, Pi = naimark_slots(P, a, b)
    w, svec, idx = dpp_data(U, p, q, b)
    law = profile_law(w, svec, b, q)
    mu = mcp(P)                                   # c[m] coeff of y^{p-m}
    ys = np.array([0.37, 1.11, 2.5, 3.9, 5.7, 8.3, 11.2, 17.0, 23.5])
    ys = ys[np.abs(ys - a) > 1e-6]
    lhs = np.polyval(mu, ys)
    rhs = mu_from_profile(law, p, a, b, ys)
    scale = np.maximum(1.0, np.abs(lhs))
    err = float(np.max(np.abs(lhs - rhs) / scale))

    lo, hi = band(a, b)
    rts = np.sort(np.roots(mu).real)
    line = (f"  {name:32s} p={p:2d} q={q:2d} (a,b)=({a},{b})  "
            f"|mu - (y-a)^p Psi(theta)| rel = {err:.2e}")
    extra = ''
    if b == 2:
        c = psi_poly_b2(law, p)
        rr = np.roots(c[::-1]) if len(c) > 1 else np.array([])
        imx = float(np.abs(rr.imag).max()) if len(rr) else 0.0
        th = np.sort(rr.real)
        pis = 1.0 / (1.0 - th) if len(th) else np.array([])
        pimax = float(pis.max()) if len(pis) else 0.0
        bound = 4.0 * (a - 1) / a ** 2
        lam_pred = a * (1 + np.sqrt(pimax)) if pimax > 0 else float(rts.max())
        extra = (f"\n      b=2: n_2 ~ sum Bern(pi), pi = {np.array2string(np.sort(pis), precision=5)}"
                 f"\n           |Im(roots of Psi)| = {imx:.1e}   "
                 f"pi_max = {pimax:.6f}  vs  4(a-1)/a^2 = {bound:.6f}   "
                 f"{'OK' if pimax <= bound + 1e-9 else 'VIOLATION'}"
                 f"\n           a(1+sqrt(pi_max)) = {lam_pred:.6f}   "
                 f"lambda_max = {rts.max():.6f}   "
                 f"a(1-sqrt(pi_max)) = {a*(1-np.sqrt(pimax)):.6f}  "
                 f"lambda_min = {rts.min():.6f}")
    if verbose:
        print(line + extra)
    return err, law


if __name__ == '__main__':
    print("=" * 78)
    print("THEOREM C check: mu(y) = (y-a)^p Psi(theta_2(y),...,theta_b(y))")
    print("=" * 78)
    print("-- graphs --")
    for name, (adj, p, q, a, b) in GRAPHS.items():
        check(name, graph_family(adj, p, q, a, b), a, b)
    print("-- noncommuting --")
    cases = [(4, 6, 3, 2, False), (3, 6, 4, 2, False), (4, 8, 4, 2, False),
             (5, 10, 4, 2, False), (6, 9, 3, 2, False), (6, 8, 4, 3, False),
             (4, 6, 3, 2, True), (6, 10, 5, 3, False)]
    for (p, q, a, b, cx) in cases:
        if p * a != q * b:
            continue
        P, res = rand_proj_family(p, q, a, b, seed=2000 + p * 31 + q * 7 + a,
                                  complex_=cx)
        if res > 1e-11:
            print(f"  [skip ({p},{q},{a},{b}): residual {res:.1e}]")
            continue
        check(("cx " if cx else "") + f"random({p},{q},{a},{b})", P, a, b)

    # ---------------------------------------------------------------- b=2 sweep
    print()
    print("=" * 78)
    print("INEQ-2 stress test at b=2:  pi_max <= 4(a-1)/a^2 ?")
    print("=" * 78)
    rng = np.random.default_rng(12345)
    worst = {}
    for (p, q, a) in [(4, 6, 3), (6, 9, 3), (8, 12, 3), (3, 6, 4), (4, 8, 4),
                      (5, 10, 4), (6, 12, 4), (4, 10, 5), (6, 15, 5)]:
        b = 2
        bound = 4.0 * (a - 1) / a ** 2
        best = -1.0
        for trial in range(12):
            X = rand_X(q, p, b, rng)
            A = proj_from_X(X)
            A, r = restore_proj(A, q, p, a, b, iters=4000, tol=1e-14)
            if r > 1e-11:
                continue
            U, Pi = naimark_slots(A, a, b)
            w, svec, _ = dpp_data(U, p, q, b)
            law = profile_law(w, svec, b, q)
            c = psi_poly_b2(law, p)
            rr = np.roots(c[::-1]) if len(c) > 1 else np.array([])
            if not len(rr):
                continue
            pim = float((1.0 / (1.0 - rr.real)).max())
            best = max(best, pim)
        worst[(p, q, a)] = (best, bound)
        print(f"  (p,q,a)=({p},{q},{a})  max over 12 random families: "
              f"pi_max = {best:.6f}   bound 4(a-1)/a^2 = {bound:.6f}   "
              f"ratio {best/bound:.4f}  {'OK' if best <= bound + 1e-9 else 'VIOLATION'}")
