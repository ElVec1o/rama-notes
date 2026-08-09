"""Can the power-sum certificate ever prove Song-Fan-Miao in general?

The certificate says: if P_m q^m <= 1 with q >= tau^2 then no nonzero root lies below tau.
The obvious next step is to bound P_m uniformly in the size of the graph. This script asks
whether that is possible at all, before any effort is spent on it.

THE TRAP. P_m^{-1/m} is the reciprocal of the l^m norm of the reciprocals of the roots, and
for a finite family of positive reals that norm decreases to the l^infinity norm. Hence

    sup_m P_m^{-1/m}  =  y_1  exactly,

so optimising the certificate over m does not approximate the smallest root, it COMPUTES it.
The certificate therefore succeeds for a graph precisely when y_1 > tau^2, which is
Song-Fan-Miao for that graph. There is no shortcut: a uniform bound on P_m strong enough to
give the conjecture would already be the conjecture.

Part A tests the convergence directly, tabulating P_m^{-1/m} against the true y_1 as m grows.
Part B tests the consequence: as the graph grows, y_1 decreases toward tau^2, so the margin
the certificate needs shrinks, and the number of roots it must beat grows. If y_1 approaches
tau^2 the certificate must eventually fail, which is what a no-go looks like numerically.

The honest exit state is REFORMULATION, not a proof route: the certificate is a complete
decision procedure with exact rational arithmetic, and it is nothing more.
"""

import sys
import math
import random
import numpy as np
import sympy as sp

sys.path.insert(0, 'code')
x = sp.Symbol('x')


def even_part(poly):
    p = sp.Poly(poly, x)
    co = p.all_coeffs()[::-1]
    d = 0
    while d < len(co) and co[d] == 0:
        d += 1
    rest = co[d:]
    assert all(rest[i] == 0 for i in range(1, len(rest), 2))
    return list(rest[0::2]), d          # ascending coefficients of Gt


def power_sums(asc, M):
    """p_m = sum (1/y_i)^m by Newton's identities on the reversed polynomial."""
    c = [sp.Rational(t) for t in asc]
    nu = len(c) - 1
    a = [c[nu - j] for j in range(nu + 1)]
    lead = a[nu]
    e = [(-1) ** k * a[nu - k] / lead for k in range(nu + 1)]
    p = [sp.Rational(0)] * (M + 1)
    for m in range(1, M + 1):
        s = sp.Rational(0)
        for i in range(1, m):
            if i <= nu:
                s += (-1) ** (i - 1) * e[i] * p[m - i]
        if m <= nu:
            s += (-1) ** (m - 1) * m * e[m]
        p[m] = s
    return p


def counts(nA, nB, adjA):
    size = 1 << nB
    dp = np.zeros(size, dtype=object)
    dp[0] = 1
    idx = np.arange(size)
    for i in range(nA):
        new = dp.copy()
        for bv in adjA[i]:
            bit = 1 << bv
            has = (idx & bit) != 0
            new[has] += dp[idx[has] ^ bit]
        dp = new
    pc = np.array([bin(t).count('1') for t in idx])
    return [int(dp[pc == k].sum()) for k in range(nB + 1)]


def random_biregular(a, b, k, rng, tries=600):
    nA, nB = b * k, a * k
    for _ in range(tries):
        sa = [i for i in range(nA) for _ in range(a)]
        sb = [j for j in range(nB) for _ in range(b)]
        rng.shuffle(sb)
        e = list(zip(sa, sb))
        if len(set(e)) != len(e):
            continue
        adjA = [[] for _ in range(nA)]
        for (i, j) in e:
            adjA[i].append(j)
        nbrB = [[] for _ in range(nB)]
        for (i, j) in e:
            nbrB[j].append(i)
        seen = {('A', 0)}; st = [('A', 0)]
        while st:
            side, v = st.pop()
            nb = [('B', t) for t in adjA[v]] if side == 'A' else [('A', t) for t in nbrB[v]]
            for w in nb:
                if w not in seen:
                    seen.add(w); st.append(w)
        if len(seen) == nA + nB:
            return nA, nB, adjA
    return None


def analyse(nA, nB, adjA):
    n = nA + nB
    m = counts(nA, nB, adjA)
    poly = sum((-1) ** kk * m[kk] * x ** (n - 2 * kk) for kk in range(len(m)))
    asc, d = even_part(sp.expand(poly))
    cop = sp.Poly(poly, x).all_coeffs()
    while cop and cop[-1] == 0:
        cop.pop()
    rts = [abs(complex(r)) for r in sp.Poly(cop, x).nroots(n=25, maxsteps=800)
           if abs(sp.im(r)) < 1e-9 and abs(sp.re(r)) > 1e-9]
    return asc, (min(rts) ** 2 if rts else float('nan'))


def main():
    rng = random.Random(7)
    print("A. does P_m^{-1/m} converge to the true smallest root?\n")
    print(f"{'a':>3}{'b':>3}{'k':>3}{'n':>4}" +
          "".join(f"{'m='+str(mm):>10}" for mm in (1, 2, 4, 8, 16, 32)) +
          f"{'true y1':>10}")
    for (a, b) in [(3, 4), (3, 5)]:
        for k in (2, 3, 4):
            g = random_biregular(a, b, k, rng)
            if g is None:
                continue
            nA, nB, adjA = g
            if nB > 12:
                continue
            asc, true1 = analyse(nA, nB, adjA)
            P = power_sums(asc, 32)
            row = ""
            for mm in (1, 2, 4, 8, 16, 32):
                v = abs(float(P[mm]))
                row += f"{(v ** (-1.0 / mm) if v > 0 else float('inf')):>10.5f}"
            print(f"{a:>3}{b:>3}{k:>3}{nA+nB:>4}{row}{true1:>10.5f}")
    print("\nthe m-column converges upward to the true value, confirming")
    print("sup_m P_m^{-1/m} = y_1: optimising over m computes the root, it does not bound it.\n")

    print("B. does the margin shrink as the graph grows?\n")
    print(f"{'a':>3}{'b':>3}{'k':>3}{'n':>4}{'tau^2':>9}{'true y1':>10}"
          f"{'y1/tau^2':>10}{'certifiable?':>14}")
    for (a, b) in [(3, 4), (3, 5), (4, 5)]:
        tau2 = (math.sqrt(a - 1) - math.sqrt(b - 1)) ** 2
        for k in (1, 2, 3, 4):
            g = random_biregular(a, b, k, rng)
            if g is None:
                continue
            nA, nB, adjA = g
            if nB > 12:
                continue
            asc, true1 = analyse(nA, nB, adjA)
            ratio = true1 / tau2
            print(f"{a:>3}{b:>3}{k:>3}{nA+nB:>4}{tau2:>9.5f}{true1:>10.5f}"
                  f"{ratio:>10.3f}{('yes' if ratio > 1 else 'NO'):>14}")
    print("\nthe certificate succeeds exactly when y1 > tau^2, which is the conjecture for")
    print("that graph. As the graph grows y1 decreases toward tau^2, so the margin the")
    print("certificate needs shrinks. A uniform bound on P_m strong enough to give the")
    print("conjecture would already BE the conjecture: the difficulty has not moved.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
