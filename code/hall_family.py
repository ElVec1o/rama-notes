"""Mining Chris Hall's counterexample: is it isolated, or one of a family?

THE COUNTEREXAMPLE IS HALL'S (personal communication, August 2026). This script is our own
follow-up work: it asks how special the graph is.

Hall's graph is the case p = q = 5 of

    G(p, q) = a central vertex c joined to v_1..v_p; for each i a copy of K_{2,q} on
              v_i, w_i with middle vertices u_{i,1..q}; and a pendant leaf at each w_i.

The branch arithmetic is uniform in (p, q). With H the branch after deleting c,

    mu_{H-v}    = x^q (x^2 - (q+1))          the star K_{1,q+1}
    mu_{H-v-u}  = x^{q-1} (x^2 - q)          the star K_{1,q}
    mu_H        = x^{q-1} ( x^4 - (2q+1) x^2 + q^2 )
    x mu_H - p mu_{H-v} = x^q ( x^4 - (2q+1+p) x^2 + q^2 + p(q+1) ),

so the candidate roots are x^2 = (S +- sqrt(D))/2 with S = 2q+1+p and
D = S^2 - 4(q^2 + p(q+1)). At p = q = 5, S = 16 and D = 36, giving x^2 in {5, 11}.

Two questions, both answered here:

  1. For which (p, q) is D a perfect square, so that the roots are as clean as Hall's?
  2. For which (p, q) does a root actually land in an INTERNAL GAP of spec(T)? That is the
     property that refutes Conjecture 10; a clean root is necessary but not sufficient.

The spectral test avoids the cavity mass gate, which these graphs fail: pendant leaves give
flat bands and the gate discards the run. Instead we use the scaling of the density of states
at the candidate root as eta decreases. Outside the spectrum the cavity Green function is real
and DOS(x + i eta) vanishes linearly in eta; inside, DOS converges to a positive limit. The
ratio DOS(eta)/eta is therefore the diagnostic: bounded means outside, blowing up means
inside.

We also test the role of the pendant leaf, since the leaf is what repaired the common
spectral parameter in Hall's construction, by running the same family with the leaf removed.
"""

import sys
import math
import cmath
import sympy as sp

sys.path.insert(0, 'code')

x = sp.Symbol('x')


def branch_polys(q, leaf=True):
    """mu_{H-v} and mu_H for one branch, exactly."""
    if leaf:
        # H - v is the star K_{1,q+1} centred at w (q middles + the leaf)
        muHv = x ** q * (x ** 2 - (q + 1))
    else:
        muHv = x ** (q - 1) * (x ** 2 - q)
    # H - v - u_j is the star K_{1,q} (leaf case) or K_{1,q-1}
    muHvu = x ** (q - 1) * (x ** 2 - q) if leaf else x ** (q - 2) * (x ** 2 - (q - 1))
    muH = sp.expand(x * muHv - q * muHvu)
    return sp.expand(muHv), muH


def graph(p, q, leaf=True):
    """Vertices: c=0; v_i; w_i; leaves; u_{i,j}. Returns (n, edges)."""
    edges = []
    nxt = 1
    vs, ws = [], []
    for _ in range(p):
        vs.append(nxt); nxt += 1
        ws.append(nxt); nxt += 1
    ls = []
    if leaf:
        for _ in range(p):
            ls.append(nxt); nxt += 1
    for i in range(p):
        edges.append((0, vs[i]))
        if leaf:
            edges.append((ws[i], ls[i]))
        for _ in range(q):
            u = nxt; nxt += 1
            edges.append((vs[i], u))
            edges.append((u, ws[i]))
    return nxt, edges


def dos_scaling(n, edges, root, etas=(1e-4, 1e-5, 1e-6, 1e-7)):
    """DOS(root + i eta)/eta across a ladder of eta. Bounded => root outside spec(T)."""
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    foll = [[idx[(b, c)] for c in adj[b] if c != a] for (a, b) in de]
    h = [complex(0.0, -0.1)] * len(de)
    out = []
    for eta in etas:
        z = complex(root, eta)
        for _ in range(20000):
            diff = 0.0
            new = [0j] * len(de)
            for k in range(len(de)):
                ssum = z
                for f in foll[k]:
                    ssum -= h[f]
                val = 1.0 / ssum
                diff = max(diff, abs(val - h[k]))
                new[k] = val
            h = new
            if diff < 1e-14:
                break
        acc = 0.0
        for u in range(n):
            ssum = z
            for b in adj[u]:
                ssum -= h[idx[(u, b)]]
            acc += (1.0 / ssum).imag
        d = -acc / (math.pi * n)
        out.append(d / eta)
    return out


def main():
    for leaf in (True, False):
        tag = "with pendant leaf" if leaf else "no leaf (min degree 2 on w)"
        print(f"\n{'='*78}\nFAMILY G(p,q) {tag}\n{'='*78}")
        print(f"{'p':>3}{'q':>3}{'n':>5}{'disc':>7}{'square':>8}{'roots x^2':>18}"
              f"{'root':>9}{'DOS/eta ladder':>34}{'verdict':>10}")
        for q in range(2, 8):
            for p in range(2, 8):
                S = 2 * q + 1 + p if leaf else None
                muHv, muH = branch_polys(q, leaf)
                last = sp.expand(x * muH - p * muHv)
                poly = sp.Poly(sp.simplify(sp.cancel(last / x ** sp.degree(
                    sp.gcd(last, x ** 50), x))), x)
                # quartic factor in x^2
                z = sp.Symbol('z')
                quart = sp.Poly(sp.expand(poly.as_expr().subs(x, sp.sqrt(z))), z)
                try:
                    c2, c1, c0 = quart.all_coeffs()[-3:]
                except ValueError:
                    continue
                disc = sp.simplify(c1 ** 2 - 4 * c2 * c0)
                if not disc.is_number or disc < 0:
                    continue
                issq = sp.sqrt(disc).is_Integer
                r2 = sp.solve(sp.Eq(c2 * z ** 2 + c1 * z + c0, 0), z)
                r2 = [sp.nsimplify(t) for t in r2 if t.is_number and t > 0]
                if not r2:
                    continue
                n, edges = graph(p, q, leaf)
                if n > 90:
                    continue
                # test the SMALLER positive root, the one in the interior
                root = float(sp.sqrt(min(r2)))
                lad = dos_scaling(n, edges, root)
                bounded = max(lad) < 50.0
                verdict = "GAP" if bounded else "in spec"
                print(f"{p:>3}{q:>3}{n:>5}{int(disc):>7}{str(bool(issq)):>8}"
                      f"{str([sp.nsimplify(t) for t in sorted(r2)]):>18}{root:>9.5f}"
                      f"{str([f'{t:.2f}' for t in lad]):>34}{verdict:>10}")
        print("\nDOS/eta bounded across the ladder means the root sits in a gap of spec(T),")
        print("so Conjecture 10 fails there. Growing means the root is in the spectrum.")


if __name__ == '__main__':
    sys.exit(main())
