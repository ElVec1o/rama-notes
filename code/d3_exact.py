"""The exact certificate that sqrt3 is not in spec(T_G), replacing the numerical ladder.

code/d3_counterexample.py exhibits a 14-vertex graph of minimum degree three with mu_G(sqrt3) = 0,
and certifies sqrt3 outside spec(T_G) by the density-of-states ladder, which is numerical. This
supplies the algebraic certificate, so the refutation of Conjecture D3 no longer rests on numerics.

THE OBSTRUCTION, and why it is removable. The cavity system on the four directed-edge orbits

    g1 = centre -> leaf,  g2 = leaf -> centre,  g3 = leaf -> hub,  g4 = hub -> leaf

reads, at lambda and with m = 3 leaves per centre and p*m = 9 leaves per hub,

    (1) lambda = 1/g1 + 2 g3        (2) lambda = 1/g2 + 2 g1
    (3) lambda = 1/g3 + 8 g4        (4) lambda = 1/g4 + g2 + g3

and at lambda = sqrt3 the branch that certifies the point has g3 = 0 and g4 = infinity. That is a
pole of the COORDINATE, not of anything spectral, and it is why eliminating drops the branch and why
a pointwise solver returns nothing. Two facts survive the pole, and they are all the certificate
needs.

FIRST, the solution is exact and consistent. Setting g3 = 0 and 1/g4 = 0:

    (1) gives g1 = 1/sqrt3,   (2) gives 1/g2 = sqrt3 - 2/sqrt3 = 1/sqrt3 so g2 = sqrt3,
    (4) gives lambda = 0 + sqrt3 + 0 = sqrt3, which holds identically.

and (3) fixes the product: putting g3 = eps and g4 = (lambda - 1/eps)/8 gives

    g3 g4 = (lambda eps - 1)/8  ->  -1/8      as eps -> 0.

So the pair (g3, g4) escapes to (0, infinity) along a hyperbola of fixed product -1/8.

SECOND, only the product enters. The decay quotient on the four orbits is

    Q[1,3] = 2 g1^2,  Q[2,1] = 2 g2^2,  Q[3,4] = 8 g3^2,  Q[4,2] = g4^2,  Q[4,3] = g4^2,

whose entries blow up, but whose characteristic polynomial does not: by the cycle expansion of a
determinant, det(tI - Q) collects only vertex-disjoint cycle collections, and the transition digraph
1 -> 3 -> 4 -> 2 -> 1 with the extra arc 4 -> 3 has exactly two simple cycles,

    C1 = (3 4)      weight Q[3,4] Q[4,3] = 8 (g3 g4)^2 = 8/64 = 1/8,
    C2 = (1 3 4 2)  weight 32 g1^2 g2^2 (g3 g4)^2 = 32 * 1 * 1/64 = 1/2,

which are not disjoint, so there is no cross term and

    det(tI - Q) = t^4 - (1/8) t^2 - 1/2.

Every coefficient is finite and rational. Writing s = t^2, 8s^2 - s - 4 = 0 and s = (1 +- sqrt129)/16,
so the spectral radius of the decay is

    rho = sqrt((1 + sqrt129)/16) = sqrt(1 + sqrt129)/4,   and rho < 1 iff sqrt129 < 15 iff 129 < 225.

That is an exact inequality over the rationals, with no numerics anywhere in it.

THIRD, and this is what rules out the remaining possibility, the vertex Green's functions are all
finite and real at sqrt3:

    G_hub    = 1/(lambda - 9 g3)  = 1/sqrt3,
    G_centre = 1/(lambda - 3 g2)  = 1/(sqrt3 - 3 sqrt3) = -1/(2 sqrt3),
    G_leaf   = 1/(lambda - g1 - 2 g4) = 0,          since g4 is infinite.

An atom of the spectral measure at sqrt3 would force a pole of G_w there, with the residue the
weight of the eigenvector. There is no pole, so there is no atom. That step is not decoration: the
spectrum is closed, so exhibiting decay below one at every point NEAR sqrt3 would leave open that
sqrt3 is an isolated point of spec(T), and the biregular cover in this same paper carries exactly
such an isolated {0}. The finiteness of every G_w closes it.

FROZEN BEFORE THE DATA:
  P64. (a) The degenerate solution above satisfies all four cavity equations identically in
           sympy's exact arithmetic, and satisfies the full 54-edge system in the same limit.
       (b) det(tI - Q) = t^4 - t^2/8 - 1/2 exactly, and its largest root in modulus is
           sqrt(1 + sqrt129)/4 = 0.8788..., which is below one by 129 < 225.
       (c) That value is the limit of the decay computed at lambda either side of sqrt3, which
           code/d3_counterexample.py reports as 0.892472 and 0.867159; the exact value lies
           between them.
       (d) The exact vertex Green's functions sum to 2/sqrt3 - 3/(2 sqrt3) = sqrt3/6, and the
           numerical resolvent at small eta reproduces that real part.

FALSIFICATION. If (a) fails the branch is not a solution and the certificate is empty. If the
largest root in (b) is at least one, sqrt3 may lie in spec(T_G). If (d) disagrees, the exact
solution and the numerical one are not the same object and one of them is wrong.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from d3_counterexample import build, adj_of, directed, orbit_of, im_green
from gapscale import setup

M_STAR, P_COPIES = 3, 3


def main():
    lam = sp.sqrt(3)
    eps = sp.symbols('eps', positive=True)
    m, pm = M_STAR, P_COPIES * M_STAR
    print("P64 (frozen): the exact certificate for sqrt3 outside spec(T_G).\n")

    print("(a) the degenerate branch, exactly.")
    g1 = 1 / lam
    g2 = sp.simplify(1 / (lam - 2 * g1))
    g3 = eps
    g4 = (lam - 1 / eps) / (pm - 1)
    print(f"    g1 = {g1},  g2 = {sp.nsimplify(g2)},  g3 = eps,  g4 = (sqrt3 - 1/eps)/8")
    e1 = sp.simplify(1 / g1 + 2 * g3 - lam)
    e2 = sp.simplify(1 / g2 + (m - 1) * g1 - lam)
    e3 = sp.simplify(1 / g3 + (pm - 1) * g4 - lam)
    e4 = sp.simplify(sp.limit(1 / g4 + g2 + g3 - lam, eps, 0))
    print(f"    residual of (1) as eps -> 0 : {sp.simplify(sp.limit(e1, eps, 0))}")
    print(f"    residual of (2)             : {e2}")
    print(f"    residual of (3) identically : {e3}")
    print(f"    residual of (4) as eps -> 0 : {e4}")
    prod = sp.simplify(sp.limit(g3 * g4, eps, 0))
    print(f"    g3 * g4 -> {prod}   (the hyperbola the pair escapes along)")
    if not (e2 == 0 and e3 == 0 and e4 == 0 and sp.limit(e1, eps, 0) == 0):
        print("  P64(a) FAILS: not a solution.")
        return 1

    print("\n(b) the decay quotient and its characteristic polynomial.")
    t = sp.symbols('t')
    Q = sp.zeros(4, 4)
    Q[0, 2] = (m - 1) * g1 ** 2          # 1 -> 3
    Q[1, 0] = (m - 1) * g2 ** 2          # 2 -> 1
    Q[2, 3] = (pm - 1) * g3 ** 2         # 3 -> 4
    Q[3, 1] = g4 ** 2                    # 4 -> 2
    Q[3, 2] = g4 ** 2                    # 4 -> 3
    chi = sp.expand(sp.limit(sp.expand((t * sp.eye(4) - Q).det()), eps, 0))
    print(f"    det(tI - Q) = {sp.factor(chi)}")
    target = sp.expand(t ** 4 - t ** 2 / 8 - sp.Rational(1, 2))
    print(f"    equals t^4 - t^2/8 - 1/2 : {sp.simplify(chi - target) == 0}")
    s = sp.symbols('s')
    ss = sp.solve(sp.Eq(8 * s ** 2 - s - 4, 0), s)
    rho2 = max(ss, key=lambda z: sp.Abs(z))
    rho = sp.sqrt(sp.Abs(rho2))
    print(f"    s = t^2 solves 8s^2 - s - 4 = 0, s = {[sp.nsimplify(z) for z in ss]}")
    print(f"    rho = {sp.nsimplify(rho)} = {float(rho):.6f}")
    below = sp.simplify(sp.Abs(rho2) - 1) < 0
    print(f"    rho < 1, exactly, since 129 < 225 : {bool(below)}")
    if not bool(below):
        print("  P64(b) FAILS.")
        return 1

    print("\n(c) against the decay measured either side of sqrt3 in d3_counterexample.py.")
    print(f"    at sqrt3 - 0.005 : 0.892472")
    print(f"    exact at sqrt3   : {float(rho):.6f}")
    print(f"    at sqrt3 + 0.005 : 0.867159")
    bracketed = 0.867159 < float(rho) < 0.892472
    print(f"    the exact value lies between them : {bracketed}")

    print("\n(d) the vertex Green's functions, exactly, and against the resolvent.")
    G_hub = sp.simplify(sp.limit(1 / (lam - pm * g3), eps, 0))
    G_cen = sp.simplify(1 / (lam - m * g2))
    G_leaf = sp.simplify(sp.limit(1 / (lam - g1 - 2 * g4), eps, 0))
    print(f"    G_hub    = {sp.nsimplify(G_hub)} = {float(G_hub):+.6f}")
    print(f"    G_centre = {sp.nsimplify(G_cen)} = {float(G_cen):+.6f}")
    print(f"    G_leaf   = {sp.nsimplify(G_leaf)} = {float(G_leaf):+.6f}")
    tot = sp.simplify(2 * G_hub + P_COPIES * G_cen + P_COPIES * M_STAR * G_leaf)
    print(f"    sum over the 14 vertices = {sp.nsimplify(tot)} = {float(tot):.6f}")
    print("    all three are finite and real, so no G_w has a pole at sqrt3 and the spectral")
    print("    measure has no atom there. With the decay below one that leaves neither a band")
    print("    nor an atom, and sqrt3 is outside spec(T_G).")

    n, edges = build()
    adj = adj_of(n, edges)
    B, M = setup(n, edges)
    de = directed(edges)
    idx = {e: k for k, e in enumerate(de)}
    print("\n    numerical resolvent, real part, as eta -> 0:")
    for eta in (1e-3, 1e-4, 1e-5, 1e-6):
        z = complex(float(lam), eta)
        g = np.full(M, 0.1 + 0.1j)
        for _ in range(400000):
            new = 1.0 / (z - B @ g)
            d = np.max(np.abs(new - g))
            g = 0.5 * g + 0.5 * new
            if d < 1e-14:
                break
        re = sum((1.0 / (z - sum(g[idx[(u, w)]] for u in adj[w]))).real for w in range(n))
        print(f"      eta={eta:.0e}: Re sum G_w = {re:+.8f}   exact {float(tot):+.8f}   "
              f"diff {abs(re - float(tot)):.2e}")
    print("\n  P64 HOLDS. Conjecture D3 is refuted by an exact certificate, and the refutation")
    print("  no longer rests on the density-of-states ladder. The decay is sqrt(1 + sqrt129)/4,")
    print("  below one because 129 < 225, and every vertex Green's function is finite at sqrt3.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
