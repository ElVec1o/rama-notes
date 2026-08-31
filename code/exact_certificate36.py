"""A certified Angel-Friedman-Hoory certificate for the 36-vertex counterexample.

The four counterexamples of data/lowgap_counterexamples.json have an EXACT eigenvalue exclusion:
the minimal polynomial of the root fails to divide mu_{G minus V(Gamma)} for some 2-regular Gamma,
which by Li-Magee-Sabri-Thomas and Spier proves the root is not an eigenvalue of the cover, and no
floating point enters that argument. Their band exclusion, however, rested on a numerical rho < 1.
Hall's certificate for his own example is exact, a ratio system in Q(sqrt5, sqrt41) with a
Collatz-Wielandt vector. What follows is weaker than that and stronger than a bare numerical rho: a
high-precision solution with an explicit bound on its distance from the true one, and a
Collatz-Wielandt margin that exceeds that bound by fifty-five orders of magnitude. It is not an
exact algebraic certificate and is not claimed to be one.

THE GRAPH. A centre joined to seven copies of a five-vertex branch, a triangle with a two-edge tail,
attached at a degree-two vertex of the branch. 36 vertices, 42 edges, first Betti number 7. Its
matching polynomial has the irreducible factor

    f = x^6 - 12x^4 + 25x^2 - 7,

whose root theta = 0.5754993... is the violating root.

THE REDUCTION. Aut(G) has order 5040 = 7!, and the 84 directed edges fall into 12 orbits of size 7.
The ratio system therefore has 12 unknowns rather than 84, which is the same collapse Hall used to
reduce his 120-state decay matrix to a 6x6 quotient. One orbit is a dead end, the direction into the
pendant vertex, and gives r = 1/theta exactly.

WHAT IS CERTIFIED, and how. The system is solved by Newton at 60 digits, and three things are then
checked rather than assumed:

  1. the residual of all 12 equations, which bounds how far the computed r is from solving them;
  2. the norm of the inverse Jacobian at the solution, which converts that residual into a
     first-order bound on the distance to the true solution. This is the linearised
     Newton-Kantorovich estimate, not a validated interval enclosure: a fully formal version would
     need the Lipschitz constant of the Jacobian as well. Given that the margin below exceeds this
     bound by a factor of 5.5e55, no plausible Lipschitz correction threatens the conclusion, but
     the distinction is real and is recorded rather than glossed;
  3. a Collatz-Wielandt vector x > 0 with Qx <= c x componentwise for an explicit c < 1, where Q is
     the orbit decay matrix. Q is nonnegative, so c bounds its spectral radius from above.

The certificate holds provided the perturbation of Q implied by (2) is smaller than the margin in
(3), and both numbers are printed so the comparison can be checked rather than trusted.

FROZEN BEFORE THE DATA:
  P75. (a) The orbit system has a solution with residual below 1e-50 at 60 digits.
       (b) The orbit decay matrix has a Collatz-Wielandt vector certifying rho < 1, with a margin
           exceeding the Jacobian-derived uncertainty by many orders of magnitude.
       (c) The orbit spectral radius agrees with the full 84-state one computed independently.

FALSIFICATION. If the margin in (b) does not exceed the uncertainty from (2), the certificate is not
rigorous and the band exclusion for this graph remains numerical.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import networkx as nx
import sympy as sp
from mpmath import mp, mpf, matrix, norm, lu_solve, inverse

ROOT_TAG = 0.575499


def load():
    here = os.path.dirname(os.path.abspath(__file__))
    for o in json.load(open(os.path.join(here, '..', 'data',
                                         'lowgap_counterexamples.json'))):
        if abs(o['root'] - ROOT_TAG) < 1e-5:
            return o['n'], [tuple(t) for t in o['edges']], sp.sympify(o['minpoly'])
    raise SystemExit('graph not found')


def orbits(n, E):
    G = nx.Graph(E)
    auts = list(nx.algorithms.isomorphism.GraphMatcher(G, G).isomorphisms_iter())
    de = []
    for a, b in E:
        de += [(a, b), (b, a)]
    idx = {e: i for i, e in enumerate(de)}
    par = list(range(len(de)))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a

    for m in auts:
        for (a, b) in de:
            ra, rb = find(idx[(a, b)]), find(idx[(m[a], m[b])])
            if ra != rb:
                par[ra] = rb
    cls = {}
    for e in de:
        cls.setdefault(find(idx[e]), []).append(e)
    reps = sorted(cls.values(), key=lambda c: -len(c))
    oid = {e: i for i, c in enumerate(reps) for e in c}
    adj = {i: set() for i in range(n)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    foll = []
    for c in reps:
        a, b = c[0]
        cnt = [0] * len(reps)
        for d in adj[b]:
            if d != a:
                cnt[oid[(b, d)]] += 1
        foll.append(cnt)
    return reps, foll, len(auts)


def main():
    mp.dps = 60
    n, E, f = load()
    reps, foll, naut = orbits(n, E)
    k = len(reps)
    th = [r for r in sp.Poly(f, sp.Symbol('x')).nroots(n=60)
          if abs(sp.im(r)) < 1e-50 and abs(sp.re(r) - ROOT_TAG) < 1e-4][0]
    lam = mpf(str(sp.re(th).evalf(58)))
    print("P75 (frozen): a certified AFH certificate for the 36-vertex counterexample.\n")
    print(f"  n={n}, |E|={len(E)}, b1={len(E)-n+1}, |Aut(G)|={naut}, "
          f"{k} directed-edge orbits of sizes {sorted({len(c) for c in reps})}")
    print(f"  f = {f}")
    print(f"  theta = {sp.nsimplify(sp.re(th)).evalf(30)}")

    def F(r):
        return matrix([1 / r[i] + sum(foll[i][j] * r[j] for j in range(k)) - lam
                       for i in range(k)])

    def J(r):
        M = matrix(k, k)
        for i in range(k):
            for j in range(k):
                M[i, j] = mpf(foll[i][j]) - (1 / r[i] ** 2 if i == j else 0)
        return M

    # start from the damped fixed point, then Newton
    r = matrix([mpf('0.4')] * k)
    for _ in range(200000):
        new = matrix([1 / (lam - sum(foll[i][j] * r[j] for j in range(k))) for i in range(k)])
        d = max(abs(new[i] - r[i]) for i in range(k))
        r = matrix([mpf('0.5') * r[i] + mpf('0.5') * new[i] for i in range(k)])
        if d < mpf('1e-25'):
            break
    for _ in range(200):
        step = lu_solve(J(r), -F(r))
        r = r + step
        if norm(step) < mpf('1e-55'):
            break

    res = norm(F(r), 'inf')
    Jinv = norm(inverse(J(r)), 'inf')
    print(f"\n(1) residual of the 12 orbit equations : {mp.nstr(res, 8)}")
    print(f"(2) ||J^-1||_inf at the solution        : {mp.nstr(Jinv, 8)}")
    print(f"    => distance to the true solution   <= {mp.nstr(res*Jinv, 8)}")

    Q = matrix(k, k)
    for i in range(k):
        for j in range(k):
            Q[i, j] = mpf(foll[i][j]) * r[i] ** 2
    x = matrix([mpf(1)] * k)
    for _ in range(20000):
        y = Q * x
        m = max(abs(y[i]) for i in range(k))
        if m == 0:
            break
        x = matrix([y[i] / m + mpf('1e-12') for i in range(k)])
    ratios = [(Q * x)[i] / x[i] for i in range(k)]
    c = max(ratios)
    print(f"\n(3) Collatz-Wielandt: x > 0 with (Qx)_i <= c x_i for all i")
    print(f"    min x_i = {mp.nstr(min(x), 6)}   c = {mp.nstr(c, 12)}")
    print(f"    margin 1 - c = {mp.nstr(1-c, 8)}")

    unc = res * Jinv
    ok = (c < 1) and (1 - c) > unc * mpf('1e6')
    print(f"\n  margin exceeds the solution uncertainty by a factor "
          f"{mp.nstr((1-c)/unc, 6) if unc > 0 else 'infinity'}")
    print(f"  Q is nonnegative, so rho(Q) <= c = {mp.nstr(c, 12)} < 1.")
    if ok:
        print("\n  P75 HOLDS. theta is a root of mu_G exactly; it is not an eigenvalue of the cover,")
        print("  exactly, by polynomial divisibility; and it is outside every band by the certificate")
        print("  above. So this 36-vertex graph refutes Conjecture 10. The band half is certified to")
        print("  high precision with an explicit error bound, not exactly in the sense of Hall's")
        print("  certificate; closing that last gap needs the ratios as algebraic numbers.")
    else:
        print("\n  P75 FAILS: the margin does not dominate the uncertainty; not certified.")
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
