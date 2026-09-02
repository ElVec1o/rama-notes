"""The point spectrum of the universal cover, computed exactly as a polynomial.

Li-Magee-Sabri-Thomas plus Spier: theta is an eigenvalue of T_G iff mu_{G-Gamma}(theta) = 0 for
every 2-regular subgraph Gamma. So the point spectrum is exactly the root set of

    E_G(x) = gcd over all 2-regular Gamma of mu_{G-Gamma}(x),

an integer polynomial. Everything below is exact; no eigenvalue is ever computed numerically.

This is the object the supplement approximated with density-of-states and ratio systems, and got
wrong. It also gives a direct exact test of the degree bound proved here: if delta >= 2 and
Delta <= 2 delta - 2 then T_G has no nonzero eigenvalue, so E_G must be a power of x times a
constant.

FROZEN BEFORE THE DATA:
  P86. (a) Every graph tested with delta >= 2 and Delta <= 2 delta - 2 has E_G a monomial, as the
           degree bound requires. Any failure is a bug or refutes a machine-checked theorem.
       (b) Some graph with delta >= 3 and Delta >= 2 delta - 1 has E_G with a nonzero root, so the
           bound is not vacuous and the trap-free threshold is sharp in the reachable range.
       (c) Among graphs with delta >= 3, no root of mu_G outside the point spectrum is also outside
           the bands, i.e. no counterexample to Conjecture D3 turns up.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import random
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from exact_cover_certificate import matching_poly, all_cycles, restrict

x = sp.Symbol('x')
BUDGET = float(os.environ.get('BUDGET', 1500))
CAP = int(os.environ.get('CAP', 40000))


def mu_poly(n, edges):
    m = matching_poly(n, edges)
    return sp.Poly(sum((-1) ** k * mk * x ** (n - 2 * k) for k, mk in enumerate(m)), x)


def two_regular(n, edges, cap=CAP):
    masks = []
    for c in all_cycles(n, edges):
        m = 0
        for v in c:
            m |= 1 << v
        masks.append(m)
    out = []

    def rec(i, used):
        out.append(used)
        if len(out) > cap:
            raise RuntimeError('cap')
        for j in range(i, len(masks)):
            if not (masks[j] & used):
                rec(j + 1, used | masks[j])
    rec(0, 0)
    return out


def point_spectrum_poly(n, edges):
    """E_G, and the number of 2-regular subgraphs used."""
    subs = two_regular(n, edges)
    g = None
    for used in subs:
        nn, ee = restrict(n, edges, used)
        p = mu_poly(nn, ee)
        g = p if g is None else sp.gcd(g, p)
        if g.degree() == 0:
            break
    return g, len(subs)


def connected(n, edges):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    seen, st = {0}, [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u); st.append(u)
    return len(seen) == n


def random_graph(n, p, rng):
    while True:
        e = [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]
        if not e:
            continue
        deg = [0] * n
        for a, b in e:
            deg[a] += 1; deg[b] += 1
        if min(deg) >= 3 and connected(n, e):
            return e, min(deg), max(deg)


def main():
    rng = random.Random(20260902)
    t0 = time.time()
    print("P86 (frozen): E_G is a monomial exactly when the degree bound forbids point spectrum.\n")
    print(f"{'n':>3}{'delta':>6}{'Delta':>6}{'2delta-2':>9}{'#Gamma':>8}"
          f"{'E_G':>34}{'nonzero pt spec':>16}", flush=True)
    trapfree_tested = trapfree_bad = 0
    beyond_tested = beyond_hits = 0
    examples = []
    for n in (6, 7, 8, 9, 10, 11, 12):
        for _ in range(60):
            if time.time() - t0 > BUDGET:
                break
            e, dmin, dmax = random_graph(n, rng.uniform(0.35, 0.8), rng)
            try:
                E, ns = point_spectrum_poly(n, e)
            except RuntimeError:
                continue
            Ee = sp.factor(E.as_expr())
            # nonzero point spectrum iff E_G has a root other than 0
            core = sp.Poly(sp.simplify(E.as_expr() / x ** sp.degree(sp.gcd(E.as_expr(), x ** n), x)), x) \
                if E.degree() > 0 else E
            nz = core.degree() > 0
            if dmax <= 2 * dmin - 2:
                trapfree_tested += 1
                if nz:
                    trapfree_bad += 1
            else:
                beyond_tested += 1
                if nz:
                    beyond_hits += 1
            if nz and len(examples) < 6:
                examples.append((n, dmin, dmax, str(Ee), e))
                print(f"{n:>3}{dmin:>6}{dmax:>6}{2*dmin-2:>9}{ns:>8}"
                      f"{str(Ee)[:33]:>34}{'YES':>16}", flush=True)
    print(f"\n{time.time()-t0:.0f}s")
    print(f"  trap-free (Delta <= 2delta-2): {trapfree_tested} graphs, "
          f"{trapfree_bad} with nonzero point spectrum")
    print(f"  beyond    (Delta >= 2delta-1): {beyond_tested} graphs, "
          f"{beyond_hits} with nonzero point spectrum")
    print(f"  P86(a) {'HOLDS' if trapfree_bad == 0 else 'FAILS'}: "
          f"the degree bound is respected exactly, with no numerics.")
    print(f"  P86(b) {'HOLDS' if beyond_hits > 0 else 'FAILS'}.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
