"""A graph showing the degree bound is sharp at minimum degree three.

Proposition degbound says a nonzero eigenvalue of T_G forces Delta > 2(delta-1); the refined form
says Delta > (delta-2) kappa(theta) + 2. At delta = 3 with theta = +-1, whose theta-critical tree is
K_2 and so kappa = 2, both read Delta >= 5. This graph attains it.

Take five disjoint edges as the Aomoto components and four boundary vertices. Each of the ten
branch vertices has one edge inside its K_2 and takes two boundary neighbours, reaching degree 3;
the twenty resulting edges are shared out five to each boundary vertex, so Delta = 5. The branch
set S induces a forest with cc = 5 components, each having +-1 as an eigenvalue, and |boundary| = 4
< 5, so S is a (+-1)-Aomoto subset.

The counting chain also forces this to be the smallest such graph. With delta = 3 and kappa = 2 it
reads c(1*2+2) <= Delta(c-1), so 4c <= 5(c-1) and c >= 5; then e = 4c = 20 <= Delta b = 5b gives
b >= 4, while the Aomoto inequality gives b <= c-1 = 4. Hence b = 4, c = 5, and n >= 2*5 + 4 = 14.

Verified by the exact certificate: E_G = gcd over 2-regular Gamma of mu_{G-Gamma} equals
(x-1)(x+1), so the point spectrum of T_G is exactly {+1, -1}. No floating point.
"""

import sys
import sympy as sp

sys.path.insert(0, '.')
from point_spectrum_exact import point_spectrum_poly, mu_poly, x, connected

PAIRS = [(0, 1), (0, 1), (0, 2), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3), (2, 3), (2, 3)]


def build():
    e = [(4 + 2 * i, 5 + 2 * i) for i in range(5)]
    for j, v in enumerate(range(4, 14)):
        p, q = PAIRS[j]
        e += [(v, p), (v, q)]
    return 14, sorted((min(a, b), max(a, b)) for a, b in e)


def main():
    n, e = build()
    deg = [0] * n
    for a, b in e:
        deg[a] += 1
        deg[b] += 1
    assert len(set(e)) == len(e) and connected(n, e)
    E, ns = point_spectrum_poly(n, e)
    core = sp.cancel(E.as_expr() / x ** sp.degree(sp.gcd(E.as_expr(), x ** n), x))
    print(f"n={n} delta={min(deg)} Delta={max(deg)} edges={len(e)} 2-regular subgraphs={ns}")
    print(f"mu_G = {sp.factor(mu_poly(n, e).as_expr())}")
    print(f"E_G  = {sp.factor(E.as_expr())}")
    print(f"point spectrum of T_G = roots of {sp.factor(core)}")
    ok = sp.simplify(core - (x ** 2 - 1)) == 0
    print(f"\n  Delta = 5 = 2 delta - 1, so Proposition degbound is SHARP at delta = 3: {ok}")
    print("  and the counting chain forces c >= 5, b = 4, hence n >= 14, so this is the")
    print("  smallest such graph. Everything above is exact.")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
