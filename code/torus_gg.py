"""Two claims, checked before either is used.

CLAIM A (the torus form of Godsil-Gutman).

    mu_G(x)  =  integral over T^b of det( x I - A_G(z) ) dz.

Godsil and Gutman average the characteristic polynomial over the 2^m sign patterns. The same
computation runs over the torus of the maximal abelian cover, and the cancellation is easier
to see there: a permutation contributes the monomial z^{[C_1] + ... + [C_r]} where [C] is the
homology class of a cycle, every cycle uses at least one cotree edge, and vertex-disjoint
cycles use disjoint cotree edges, so a sum of classes of disjoint cycles is never zero. Only
fixed points and transpositions survive, which is exactly the matching polynomial.

CLAIM B (what the torus buys that signings do not).

    x not in spec(G^ab)  implies  mu_G(x) != 0,   that is   Zeros(mu_G) is inside spec(G^ab).

det(x I - A_G(z)) is real because the matrix is Hermitian. If it never vanishes on T^b, then
being continuous on a CONNECTED space it has one sign, so its average is nonzero. The sign
patterns of Godsil and Gutman form a discrete set and admit no such argument; connectedness
of the torus is the whole content.

This is weaker than Heilmann-Lieb outside the spectrum, since spec(G^ab) contains the Perron
value of G. It is stronger inside: it settles Conjecture 10 at every point of a gap of
spec(T) that also misses spec(G^ab), for every graph and every first Betti number, with no
feedback vertex hypothesis and no analytic estimate.

The script checks A against the matching polynomial computed combinatorially, and reports for
each graph whether the gap points of spec(T) are inside spec(G^ab), which is the residue that
claim B does not reach.
"""

import sys
import math
import cmath
import itertools
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

TESTS = {
    'K3': (3, [(0, 1), (1, 2), (0, 2)]),
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'C5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]),
    'twotri': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)]),
    'K23': (5, [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]),
    'petersenish': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3)]),
    'K33': (6, [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
                (2, 3), (2, 4), (2, 5)]),
}


def avg_det(n, edges, cot, x, steps):
    """Trapezoid average of det(xI - A_G(z)) over the torus, exact for trigonometric
    polynomials once steps exceeds the degree in each variable, which is 2."""
    b = len(cot)
    grid = [2 * math.pi * k / steps for k in range(steps)]
    tot, acc = steps ** b, 0.0
    for t in range(tot):
        th, r = [], t
        for _ in range(b):
            th.append(grid[r % steps]); r //= steps
        M = magnetic(n, edges, cot, th)
        acc += np.real(np.linalg.det(x * np.eye(n) - M))
    return acc / tot


def coeffs(n, edges, cot, x):
    """The 3^b Fourier coefficients of f(z) = det(xI - A_G(z)), exactly. f has degree one in
    each z_e, so exponents lie in {-1,0,1} and a 3-point DFT per direction is exact."""
    b = len(cot)
    S = 3
    vals = np.empty((S,) * b, dtype=complex)
    for idx in itertools.product(range(S), repeat=b):
        th = [2 * math.pi * k / S for k in idx]
        vals[idx] = np.linalg.det(x * np.eye(n) - magnetic(n, edges, cot, th))
    return np.fft.fftn(vals) / (S ** b)      # index j means exponent j, wrapped mod 3


def certified_min(n, edges, cot, x, grid0=48):
    """A certified verdict on whether x lies in spec(G^ab).

    Returns (lower bound on |f|, verdict). A sign change on the grid certifies 'inside' by
    the intermediate value theorem. Otherwise the grid minimum minus L * h / 2, with L the
    exact gradient bound from the Fourier coefficients, certifies 'outside' when positive."""
    b = len(cot)
    c = coeffs(n, edges, cot, x)
    # gradient bound: |d f / d theta_j| <= sum over alpha of |alpha_j| |c_alpha|
    L = 0.0
    for idx in itertools.product(range(3), repeat=b):
        a = [0 if k == 0 else (1 if k == 1 else -1) for k in idx]
        L += sum(abs(v) for v in a) * abs(c[idx])
    S = grid0
    while S <= 3072:
        h = 2 * math.pi / S
        vals = np.empty((S,) * b)
        for idx in itertools.product(range(S), repeat=b):
            th = [h * k for k in idx]
            vals[idx] = np.real(np.linalg.det(x * np.eye(n) -
                                              magnetic(n, edges, cot, th)))
        if vals.min() < 0 < vals.max():
            return 0.0, 'inside'
        lb = np.abs(vals).min() - L * h * math.sqrt(b) / 2
        if lb > 0:
            return float(lb), 'outside'
        S *= 2
        if S ** b > 4_000_000:
            break
    return float(np.abs(vals).min()), 'undecided'


def main():
    print("CLAIM A: mu_G(x) = average over the torus of det(xI - A_G(z))\n")
    print(f"{'graph':>12}{'n':>3}{'b':>3}{'x':>7}{'mu_G(x)':>14}{'avg det':>14}{'err':>10}")
    worst = 0.0
    for name, (n, edges) in TESTS.items():
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        c = matching_coeffs(n, edges)

        def mu(t):
            a = 0.0
            for j in range(len(c) - 1, -1, -1):
                a = a * t + c[j]
            return a
        steps = 5 if b <= 3 else 5
        for x in (-2.3, -0.7, 0.4, 1.9, 3.1):
            got = avg_det(n, edges, cot, x, steps)
            want = mu(x)
            err = abs(got - want) / max(abs(want), 1.0)
            worst = max(worst, err)
            print(f"{name:>12}{n:>3}{b:>3}{x:>7.1f}{want:>14.6f}{got:>14.6f}{err:>10.2e}")
    print(f"\nworst relative error {worst:.2e}\n")
    if worst > 1e-9:
        print("CLAIM A FAILS")
        return 1

    print("CLAIM B: how much of Conjecture 10 does 'x outside spec(G^ab)' settle?\n")
    print("The test has to be certified. det(xI - A_G(z)) vanishes on a CURVE in T^b, so a")
    print("grid minimum proves nothing by itself. But f(z) = det(xI - A_G(z)) is a")
    print("trigonometric polynomial of degree one in each z_e, so its 3^b coefficients are")
    print("recovered exactly by a DFT on a 3-point grid, they bound the gradient, and a grid")
    print("search plus that Lipschitz constant certifies a positive lower bound. A sign")
    print("change on the grid certifies the opposite, that x lies in spec(G^ab).\n")
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    print(f"{'graph':>12}{'gap':>22}{'x':>9}{'certified min':>15}{'verdict':>26}")
    tally = {'outside': 0, 'inside': 0, 'undecided': 0}
    for name, (n, edges) in TESTS.items():
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        if b > 3:
            print(f"{name:>12}   b = {b}, torus search skipped")
            continue
        R = 6.0
        got = None
        for eta in (1e-4, 1e-3, 1e-2):
            es, ds, _ = scan(n, edges, -R, R, 900, eta=eta)
            if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.03:
                got = (es, ds); break
        if got is None:
            print(f"{name:>12}   spec(T) not resolved")
            continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.08]
        if not internal:
            print(f"{name:>12}   spec(T) has no internal gap")
            continue
        for lo, hi in internal:
            x = 0.5 * (lo + hi)
            lb, verdict = certified_min(n, edges, cot, x)
            tally[verdict] += 1
            print(f"{name:>12}   ({lo:>8.4f},{hi:>8.4f}){x:>9.4f}{lb:>15.6f}{verdict:>26}")
    print(f"\n{tally['outside']} settled by claim B, {tally['inside']} in the residue, "
          f"{tally['undecided']} undecided")
    print("'outside' means x misses spec(G^ab) and Conjecture 10 holds there for free.")
    print("'inside' is the residue: a gap of spec(T) swallowed by a band of the cover.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
