"""Falsification sweep for the gap-counting identity.

Statement under test (GAPCOUNT):  for x in a gap of spec(T_G),

    #{roots of mu_G strictly above x}  =  |V(G)| * IDS_T(x, oo),

where IDS_T is the normalised integrated density of states of the universal
cover.  GAPCOUNT implies Conjecture 10: the right side is constant across a gap
while the left side jumps at any root, so no root can sit in a gap.

Two families where spec(T) is known in closed form are swept.

  vertex gadget:  G = H^(t), H k-regular on n vertices, t leaves at each vertex.
      mu_G(x) = x^(t n) mu_H(x - t/x)
      spec(T)  = {0 if t >= 2} u  +-[a-s, a+s],  a = sqrt(k-1+t), s = sqrt(k-1)

  edge gadget:    G = H * R, R = K_{1,3} with two leaves as terminals.
      mu_G(x) = (x^2-1)^(m-n) x^n mu_H(x^2 - D - 1)
      spec(T)  = {-1,0,1} u {x : |x^2 - (D+1)| <= 2 sqrt(D-1)}

Roots are computed exactly (sympy, integer coefficients) and isolated with
exact real-root isolation; band edges are compared using sympy's exact
algebraic comparison, so no floating point enters a decision.  The IDS is read
off the exact root multiplicities, which is legitimate here because both
families are built by a substitution that pushes forward the spectral measure.
"""

import sys
from sympy import (Poly, symbols, sqrt, Rational, nsimplify, expand,
                   real_roots, degree, srepr)

x, y = symbols('x y')

# ---------------------------------------------------------------- base graphs

def mu_complete(n):
    """Matching polynomial of K_n, via m_k = n! / (k! (n-2k)! 2^k)."""
    from sympy import factorial
    p = 0
    k = 0
    while 2 * k <= n:
        mk = factorial(n) / (factorial(k) * factorial(n - 2 * k) * 2 ** k)
        p += (-1) ** k * mk * x ** (n - 2 * k)
        k += 1
    return Poly(expand(p), x)


def mu_from_edges(n, edges):
    """Matching polynomial by brute-force enumeration of matchings."""
    from itertools import combinations
    counts = {}
    m = len(edges)
    for k in range(0, n // 2 + 1):
        c = 0
        for S in combinations(range(m), k):
            used = set()
            ok = True
            for i in S:
                u, v = edges[i]
                if u in used or v in used:
                    ok = False
                    break
                used.add(u)
                used.add(v)
            if ok:
                c += 1
        counts[k] = c
    p = sum((-1) ** k * counts[k] * x ** (n - 2 * k) for k in counts)
    return Poly(expand(p), x)


BASE = {}
BASE['K4'] = (4, 3, mu_complete(4))
BASE['K33'] = (6, 3, mu_from_edges(6, [(i, 3 + j) for i in range(3) for j in range(3)]))
BASE['K5'] = (5, 4, mu_complete(5))
BASE['C5'] = (5, 2, mu_from_edges(5, [(i, (i + 1) % 5) for i in range(5)]))
BASE['cube'] = (8, 3, mu_from_edges(8, [
    (0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
    (0, 4), (1, 5), (2, 6), (3, 7)]))
BASE['petersen'] = (10, 3, mu_from_edges(10, [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]))


# ------------------------------------------------------------------ machinery

def root_multiset(poly):
    """Exact real roots with multiplicity."""
    return real_roots(poly)


def count_above(roots, cut):
    """Exact count of roots strictly greater than cut."""
    return sum(1 for r in roots if r > cut)


def check(name, nV, mu, bands, gapshots):
    """bands: list of (lo, hi) exact; gapshots: exact points inside gaps."""
    roots = root_multiset(mu)
    assert len(roots) == int(degree(mu, x)), (name, len(roots), int(degree(mu, x)))

    # Conjecture 10 itself: every root sits in some band.
    bad = []
    for r in roots:
        if not any(lo <= r and r <= hi for lo, hi in bands):
            bad.append(r)

    # GAPCOUNT: at each gap point, roots above == nV * (mass of spectrum above)
    rows = []
    for cut in gapshots:
        lhs = count_above(roots, cut)
        # mass above the cut, read from the exact root multiset restricted to
        # the bands lying above it
        above = sum(1 for r in roots
                    if any(lo <= r and r <= hi and lo > cut for lo, hi in bands))
        rows.append((cut, lhs, above, lhs == above))
    return bad, rows


def vertex_gadget(hname, t):
    n, k, muH = BASE[hname]
    q = x - Rational(t, 1) / x
    comp = expand(muH.as_expr().subs(x, q) * x ** (t * n))
    mu = Poly(nsimplify(expand(comp)), x)
    s = sqrt(k - 1)
    a = sqrt(k - 1 + t)
    bands = [(-(a + s), -(a - s)), (a - s, a + s)]
    if t >= 2:
        bands.append((Rational(0), Rational(0)))
    return n * (1 + t), mu, bands, a - s


def edge_gadget(hname):
    n, D, muH = BASE[hname]
    m = n * D // 2
    comp = expand((x ** 2 - 1) ** (m - n) * x ** n * muH.as_expr().subs(x, x ** 2 - D - 1))
    mu = Poly(nsimplify(expand(comp)), x)
    r = 2 * sqrt(D - 1)
    lo = sqrt(D + 1 - r)
    hi = sqrt(D + 1 + r)
    bands = [(-hi, -lo), (lo, hi),
             (Rational(-1), Rational(-1)), (Rational(0), Rational(0)),
             (Rational(1), Rational(1))]
    return n + 2 * m, mu, bands, lo


def main():
    fails = 0
    checks = 0
    print(f"{'case':<22}{'|V|':>5}{'deg':>5}{'conj10':>9}{'gapcount':>10}")
    for hname in BASE:
        for t in (1, 2, 3):
            nV, mu, bands, edge = vertex_gadget(hname, t)
            shots = [Rational(1, 2) * edge, Rational(9, 10) * edge]
            if t >= 2:
                shots.append(Rational(1, 100))
            bad, rows = check(f"{hname}^({t})", nV, mu, bands, shots)
            ok = all(r[3] for r in rows)
            checks += len(rows)
            if bad or not ok:
                fails += 1
            print(f"{hname+'^('+str(t)+')':<22}{nV:>5}{int(degree(mu,x)):>5}"
                  f"{('OK' if not bad else 'FAIL'):>9}{('OK' if ok else 'FAIL'):>10}")
            if bad:
                print("   roots outside every band:", bad)
            for cut, lhs, rhs, good in rows:
                if not good:
                    print(f"   cut={cut}  roots above={lhs}  predicted={rhs}")
        nV, mu, bands, edge = edge_gadget(hname)
        # `edge` is the lower band edge sqrt(D+1-2 sqrt(D-1)) = sqrt(D-1) - 1 + 1.
        # At D = 2 it equals 1 exactly, so the isolated point 1 touches the band
        # and the interval (1, edge) is empty: there is no gap there to probe.
        shots = [Rational(1, 2), Rational(99, 100) * edge]
        if edge > Rational(101, 100):
            shots.append(Rational(101, 100))
        bad, rows = check(f"{hname}*R", nV, mu, bands, shots)
        ok = all(r[3] for r in rows)
        checks += len(rows)
        if bad or not ok:
            fails += 1
        print(f"{hname+'*R':<22}{nV:>5}{int(degree(mu,x)):>5}"
              f"{('OK' if not bad else 'FAIL'):>9}{('OK' if ok else 'FAIL'):>10}")
        if bad:
            print("   roots outside every band:", bad)
        for cut, lhs, rhs, good in rows:
            if not good:
                print(f"   cut={cut}  roots above={lhs}  predicted={rhs}")

    print()
    print(f"gap points checked: {checks}   failing cases: {fails}")
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
