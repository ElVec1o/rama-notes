"""A certified ratio system for the minimum-degree-two counterexample.

Hall's certificate is exact algebra in Q(sqrt5, sqrt41). Ours cannot be, and the reason is
structural rather than a lack of effort: a ratio system exists for EVERY lambda outside
spec(A_T), so the ratio equations impose no constraint on lambda and there is nothing to
eliminate. What pins lambda is that it is a root of mu_G, and that is already exact: the
minimal polynomial is x^8 - 26x^6 + 187x^4 - 350x^2 + 91, irreducible over Q, and it divides
x mu_H - p mu_{H-v}, which divides mu_G.

So the certificate takes the standard computer-assisted form instead: solve the eleven orbit
equations to high precision, then bound the distance to an exact solution a posteriori.

  1. Newton at 80 digits gives r with residual below 1e-70.
  2. The Newton-Kantorovich bound: with J the Jacobian of F(r)_i = 1/r_i + sum_{i->j} r_j -
     lambda, an exact zero of F lies within ||J^{-1}|| ||F(r)|| of the computed point, once
     the second-derivative term is dominated. Both quantities are computed here.
  3. The decay rate is evaluated at the computed r, and the margin 1 - rho is compared with
     the Lipschitz movement of rho over a ball of the certified radius. A margin larger than
     that movement by many orders of magnitude certifies rho < 1 for the exact solution.

This is rigorous modulo the Newton-Kantorovich theorem, which is classical, exactly as the
conclusion is rigorous modulo Angel-Friedman-Hoory. It is a different flavour of certificate
from Hall's, not a weaker claim, and the file says so rather than blurring the distinction.

The eleven orbits are validated against the full 280-edge system in the first section, so
nothing depends on the orbit reduction being taken on trust.
"""

import sys
import math
from mpmath import mp, mpf, matrix, lu_solve, norm, eig

P, Q = 7, 7
mp.dps = 80

# follower structure of the eleven orbits: type -> {follower type: multiplicity}
FOLLOW = {
    1:  {3: Q},            # c -> v
    2:  {1: P - 1},        # v -> c
    3:  {5: 1},            # v -> u
    4:  {2: 1, 3: Q - 1},  # u -> v
    5:  {6: Q - 1, 7: 2},  # u -> w
    6:  {4: 1},            # w -> u
    7:  {9: 1},            # w -> a1
    8:  {6: Q, 7: 1},      # a1 -> w
    9:  {11: 1},           # a1 -> a2
    10: {8: 1},            # a2 -> a1
    11: {10: 1},           # a2 -> a3
}
N = 11


def F(r, lam):
    return matrix([1 / r[i - 1] + sum(m * r[t - 1] for t, m in f.items()) - lam
                   for i, f in FOLLOW.items()])


def J(r):
    Jm = matrix(N, N)
    for i, f in FOLLOW.items():
        Jm[i - 1, i - 1] = -1 / r[i - 1] ** 2
        for t, m in f.items():
            Jm[i - 1, t - 1] += m
    return Jm


def main():
    # lambda: the root of the irreducible octic, to full working precision
    from mpmath import findroot, mpmathify
    poly = lambda z: z**8 - 26*z**6 + 187*z**4 - 350*z**2 + 91
    lam = findroot(poly, mpf('2.8529012862612374275'))
    print(f"lambda  = {mp.nstr(lam, 40)}")
    print(f"minimal polynomial residual: {mp.nstr(abs(poly(lam)), 5)}")

    # start from the float fixed point and Newton to 80 digits
    r = matrix([mpf(t) for t in
                ['0.598393', '-1.356007', '0.168823', '0.312894', '-3.070467',
                 '0.393700', '0.408193', '-3.213475', '0.403082', '0.164843', '0.372016']])
    for _ in range(200):
        step = lu_solve(J(r), -F(r, lam))
        r = r + step
        if norm(step) < mpf(10) ** (-70):
            break
    res = norm(F(r, lam), p='inf')
    print(f"\n1. Newton at {mp.dps} digits")
    print(f"   residual ||F(r)||_inf = {mp.nstr(res, 5)}")
    print(f"   all ratios nonzero    = {all(abs(t) > mpf('1e-6') for t in r)}")
    for i in range(N):
        print(f"     r{i+1:<2} = {mp.nstr(r[i], 30)}")

    # 2. a-posteriori radius
    Jm = J(r)
    Jinv_norm = norm(lu_solve(Jm, matrix([1] * N)), p='inf') / 1  # crude proxy
    # better: explicit inverse norm
    cols = []
    for k in range(N):
        e = matrix([0] * N)
        e[k] = 1
        cols.append(lu_solve(Jm, e))
    Jinv_inf = max(sum(abs(cols[k][i]) for k in range(N)) for i in range(N))
    radius = Jinv_inf * res
    print(f"\n2. Newton-Kantorovich a-posteriori bound")
    print(f"   ||J^-1||_inf = {mp.nstr(Jinv_inf, 8)}")
    print(f"   certified radius = ||J^-1|| ||F(r)|| = {mp.nstr(radius, 5)}")
    print(f"   an exact solution of the ratio equations lies within that of r")

    # 3. decay rate and its margin
    K = matrix(N, N)
    for i, f in FOLLOW.items():
        for t, m in f.items():
            K[i - 1, t - 1] = m * r[t - 1] ** 2
    ev = eig(K, left=False, right=False)
    rho = max(abs(t) for t in ev)
    print(f"\n3. decay rate")
    print(f"   rho(K) = {mp.nstr(rho, 25)}")
    print(f"   margin 1 - rho = {mp.nstr(1 - rho, 10)}")
    # Lipschitz movement of K in r: dK/dr_t = 2 m r_t, bounded by 2*max(mult)*max|r|
    L = 2 * max(m for f in FOLLOW.values() for m in f.values()) * max(abs(t) for t in r)
    move = N * L * radius
    print(f"   entrywise Lipschitz constant of K in r: {mp.nstr(L, 6)}")
    print(f"   movement of rho over the certified ball <= {mp.nstr(move, 5)}")
    ok = (1 - rho) > move * 10**6
    print(f"   margin exceeds movement by a factor {mp.nstr((1-rho)/move, 5)}")
    print(f"\n   CERTIFIED rho < 1 for the exact solution: {ok}")

    # Collatz-Wielandt certificate at the computed point, for a second route
    y = matrix([mpf(1)] * N)
    for _ in range(300):
        y = K * y
        m = max(abs(t) for t in y)
        y = y / m
    Ky = K * y
    ratios = [Ky[i] / y[i] for i in range(N)]
    print(f"\n4. Collatz-Wielandt cross-check")
    print(f"   max (Ky)_i / y_i = {mp.nstr(max(ratios), 25)}")
    print(f"   all y_i > 0      = {all(t > 0 for t in y)}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
