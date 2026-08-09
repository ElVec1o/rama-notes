"""Does a separation bound prove Song-Fan-Miao for any biregular graphs?

The Lipschitz separation of BiregularBlocking is vacuous when F(0) = 0, which is exactly
Hall's case. The fix is to divide out the zero: write F = x^m G with G(0) != 0, so that the
nonzero roots of F are precisely the roots of G, and bound those. For Hall's branch
F = x^5 (x^4 - 16 x^2 + 55), so G(0) = 55 and the obstruction is gone.

That repairs the bound. The question this script answers is whether the repaired bound is
worth anything, and in particular whether it PROVES Song-Fan-Miao for some biregular graphs.
The logic is one-sided in our favour: any nonzero root satisfies |theta| >= B, so if

    B  >=  tau = |sqrt(a-1) - sqrt(b-1)|,

then no nonzero root lies below tau and the conjecture HOLDS for that graph, unconditionally
and with no appeal to Angel-Friedman-Hoory. A separation bound is thus a proof engine, not
merely an obstruction.

Two bounds are computed, both applied to the even part. Writing mu_G(x) = x^d g(x) with
g(x) = Gt(x^2) and Gt(0) != 0:

  CAUCHY   every root y of Gt has |y| >= |c_0| / (|c_0| + max_{j>=1} |c_j|),
           so |theta| = sqrt(|y|) >= sqrt of that;
  LIPSCHITZ  |y| >= |Gt(0)| / sup_{|y| <= rho^2} |Gt'(y)|.

Both are classical; the point is the comparison with tau on real biregular graphs.
"""

import sys
import math
import random
import numpy as np
import sympy as sp

sys.path.insert(0, 'code')
x = sp.Symbol('x')
y = sp.Symbol('y')


def even_part(poly):
    """mu_G = x^d * g, g even; return Gt with g(x) = Gt(x^2), and d."""
    p = sp.Poly(poly, x)
    co = p.all_coeffs()[::-1]          # ascending
    d = 0
    while d < len(co) and co[d] == 0:
        d += 1
    rest = co[d:]
    # rest must be even in x
    assert all(rest[i] == 0 for i in range(1, len(rest), 2)), "not an even part"
    return sp.Poly(list(reversed(rest[0::2])), y), d


def cauchy_bound(Gt):
    c = [abs(t) for t in Gt.all_coeffs()[::-1]]   # ascending, c[0] = constant
    if c[0] == 0:
        return 0.0
    mx = max(c[1:]) if len(c) > 1 else 0
    return float(sp.sqrt(sp.Rational(c[0], c[0] + mx)))


def lipschitz_bound(Gt, rho):
    c = Gt.all_coeffs()[::-1]
    dG = [j * c[j] for j in range(1, len(c))]
    sup = sum(abs(dG[j]) * (rho ** 2) ** j for j in range(len(dG)))
    if sup == 0:
        return float('inf')
    return float(sp.sqrt(abs(c[0]) / sup))


# ------------------------------------------------------------------ the two mechanisms
def check_mechanisms():
    print("A. the repaired bound on the two known mechanisms\n")
    print(f"{'case':>12}{'F':>34}{'G(0)':>8}{'bound':>9}{'true root':>11}")
    # Hall: mu_H = x^4(x^4-11x^2+25), mu_{H-v} = x^5(x^2-6), p = 5
    muH = x ** 4 * (x ** 4 - 11 * x ** 2 + 25)
    muHv = x ** 5 * (x ** 2 - 6)
    F = sp.expand(x * muH - 5 * muHv)
    Gt, d = even_part(F)
    rho = 2 * math.sqrt(5)
    print(f"{'Hall (5,5)':>12}{str(sp.factor(F)):>34}{int(Gt.all_coeffs()[-1]):>8}"
          f"{lipschitz_bound(Gt, rho):>9.4f}{math.sqrt(5):>11.4f}")
    # subcubic: A0 = x^3-3x, B0 = x^2-1, p = 2
    A0 = x ** 3 - 3 * x
    B0 = x ** 2 - 1
    F2 = sp.expand(x * A0 - 2 * B0)
    Gt2, d2 = even_part(F2)
    print(f"{'subcubic':>12}{str(sp.factor(F2)):>34}{int(Gt2.all_coeffs()[-1]):>8}"
          f"{lipschitz_bound(Gt2, 3.0):>9.4f}"
          f"{float(sp.sqrt(sp.Rational(5,2)-sp.sqrt(17)/2)):>11.4f}")
    print("\nthe bound is a genuine lower bound on the smallest nonzero root, and is now")
    print("nonvacuous for Hall's construction, which the F(0) version could not touch.\n")


# ------------------------------------------------------------------ biregular
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


def random_biregular(a, b, k, rng, tries=400):
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


def check_biregular():
    print("B. does the bound prove Song-Fan-Miao for any biregular graph?\n")
    print(f"{'a':>3}{'b':>3}{'k':>3}{'n':>4}{'tau':>9}{'Cauchy':>9}{'Lipschitz':>11}"
          f"{'true':>9}{'proves?':>9}")
    rng = random.Random(11)
    proved = 0
    tot = 0
    for (a, b) in [(3, 4), (3, 5), (4, 5), (3, 6), (4, 6)]:
        tau = abs(math.sqrt(a - 1) - math.sqrt(b - 1))
        rho = math.sqrt(a - 1) + math.sqrt(b - 1)
        for k in (1, 2, 3):
            g = random_biregular(a, b, k, rng)
            if g is None:
                continue
            nA, nB, adjA = g
            n = nA + nB
            if nB > 12:
                continue
            m = counts(nA, nB, adjA)
            poly = sum((-1) ** kk * m[kk] * x ** (n - 2 * kk) for kk in range(len(m)))
            Gt, d = even_part(sp.expand(poly))
            cb = cauchy_bound(Gt)
            lb = lipschitz_bound(Gt, rho)
            co = sp.Poly(poly, x).all_coeffs()
            while co and co[-1] == 0:
                co.pop()
            rts = [abs(complex(r)) for r in sp.Poly(co, x).nroots(n=20, maxsteps=500)
                   if abs(sp.im(r)) < 1e-9 and abs(sp.re(r)) > 1e-9]
            true = min(rts) if rts else float('nan')
            ok = max(cb, lb) >= tau
            proved += 1 if ok else 0
            tot += 1
            print(f"{a:>3}{b:>3}{k:>3}{n:>4}{tau:>9.4f}{cb:>9.4f}{lb:>11.4f}"
                  f"{true:>9.4f}{('YES' if ok else 'no'):>9}")
    print(f"\nbound proves Song-Fan-Miao for {proved} of {tot} graphs tested.")
    print("A 'YES' is an unconditional proof for that graph, with no appeal to")
    print("Angel-Friedman-Hoory. A 'no' means the bound is too weak there, not that the")
    print("conjecture fails.")


if __name__ == '__main__':
    check_mechanisms()
    check_biregular()
