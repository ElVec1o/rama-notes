"""RETRACTED. The conclusion of this script is wrong.

It concluded that a graph built from p identical branches on a k-vertex separator, with p > k,
gives a root of mu_G outside spec(T_G), and hence refutes Conjecture D3 or C2. It does not. In
every such graph the branch union is a theta-Aomoto subset: its components are the p branches, its
boundary lies in the separator so has at most k vertices, and p > k is exactly the Aomoto
inequality |boundary| < components. By the criterion of Banks, Garza-Vargas and Mukherjee the root
is therefore an EIGENVALUE of the universal cover, hence lies IN spec(T_G).

The spectral certificates below are the source of the error. The Angel-Friedman-Hoory ratio system
degenerates at the root with g(hub -> leaf) = infinity; that pole is the localized eigenstate
announcing itself, and it was misread as a removable coordinate singularity. The resolvent then
reported a vertex Green's function of exactly zero at the leaf, which is the same divergence sitting
in a denominator, and that was misread as the absence of an atom.

The correct analysis is in code/aomoto_obstruction.py. Conjectures D3 and C2 are OPEN. This file is
kept for the record and because the two-cut identity and the gap scans in it are still correct; only
the spectral verdict is retracted.
"""

"""Does 3-connectivity survive the star divisor, or does C2 fall the same way D3 did?

Conjecture D3 is refuted in code/d3_counterexample.py by a 14-vertex graph of minimum degree three
whose divisor is the star K_{1,3}. That graph has vertex connectivity two, the two hubs being a
separating pair, so the 3-connected statement C2 is untouched by it and is now the live conjecture.

The lesson of the D3 refutation predicts C2 falls too. Minimum degree failed because it constrains
the ambient graph G and never the divisor H; a star's leaves have degree one in H however large
their degree is in G. Connectivity is a constraint on G of exactly the same kind. If the
construction can be run with a larger separator while leaving A alone, the same root should survive.

THE GENERALISATION. The two-cut identity gives A^{p-2} | mu_G for two hubs. The reason is not
special to two: with p identical branches attached at a separator S of size k, a matching can send
each vertex of S into at most one branch, so at most k branches interact with S and the remaining
p - k contribute their full matching polynomial. Hence

    A^{p-k} | mu_G     for p >= k + 1.

So take k hubs, p copies of the star K_{1,m}, and join every leaf to ALL k hubs. Then

    deg(centre) = m,   deg(leaf) = 1 + k,   deg(hub) = p*m,

the divisor is still A = mu_{K_{1,m}} = x^{m-1}(x^2 - m) with top root sqrt(m), and the separator
is the k hubs. At k = 3, m = 3, p = 4 that is 19 vertices with minimum degree three and vertex
connectivity three, which is exactly the hypothesis of C2.

FROZEN BEFORE THE DATA:
  P65. (a) A^{p-k} | mu_G for the k-hub star construction, verified exactly at k = 3 against mu_G
           computed from the graph by the deletion recursion.
       (b) At k = 3 the construction has minimum degree three and vertex connectivity three.
       (c) sqrt(m) lies outside spec(T_G) there, so C2 is false as well, and the whole
           repair programme by ambient hypotheses is dead rather than merely the local one.

(c) is predicted rather than its negation because the divisor is untouched by k. If instead the
extra hub closes the gap, C2 genuinely separates from D3 and connectivity is doing work that
minimum degree could not, which is a real result in the other direction and would say where the
repair actually lives.

FALSIFICATION. If (a) fails there is no divisor and the construction is pointless. If (c) fails at
every k = 3 instance, C2 survives this attack.

OUTCOME, recorded against the frozen text rather than folded into it. (a) and (b) hold. The first
clause of (c) holds: C2 is false, at k=3, m=3, p=5 on 23 vertices. The SECOND clause of (c), that
the repair programme by ambient hypotheses is dead in general, is NOT supported and was an
overreach. The construction does not scale in k: k=3, m=3 violates at p=5 and p=6 but not at p=4,
and both k=4 attempts land in a band, (4,3,5) on 24 vertices and (4,4,5) on 29 vertices at
kappa=4. Raising k raises every leaf's degree too, which fills the gap in. 4-connectivity is
untouched by this construction and is not claimed to fail.

The spectral verdict uses the density-of-states ladder of code/d3_counterexample.py, whose three
signatures are validated there against covers with known spectrum, and which is run here with the
same internal control: the atom at the origin must still register.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from twocut import mu_of, x
from gapscale import gap_profile, connectivity
from d3_counterexample import adj_of, classify
import quickmode


def build_k(k, m, p):
    """k hubs, p copies of K_{1,m}, every leaf joined to all k hubs."""
    edges = []
    nxt = k
    for _ in range(p):
        c = nxt; nxt += 1
        for _ in range(m):
            l = nxt; nxt += 1
            edges.append((c, l))
            for h in range(k):
                edges.append((l, h))
    return nxt, sorted(edges)


CASES = [(3, 3, 4), (3, 3, 5), (3, 4, 4), (3, 3, 6), (4, 3, 5), (3, 5, 4), (4, 4, 5)]


def main():
    print("P65 (frozen): the star divisor should not care about connectivity either, so C2")
    print("should fall exactly as D3 did.\n")
    print(f"{'k':>2}{'m':>3}{'p':>3}{'n':>5}{'dmin':>5}{'kappa':>6}{'divides':>9}"
          f"{'sqrt(m)':>9}{'verdict':>15}", flush=True)

    hits = []
    for (k, m, p) in (CASES[:3] if quickmode.QUICK else CASES):
        n, edges = build_k(k, m, p)
        adj = adj_of(n, edges)
        deg = [len(adj[i]) for i in range(n)]
        kap = connectivity(n, edges)
        lam = math.sqrt(m)

        divides = None
        if n <= 24:                       # the deletion recursion is exact but not cheap
            mu = sp.Poly(sp.expand(mu_of(adj, set(range(n)))), x)
            A = sp.Poly(sp.expand(x ** (m - 1) * (x ** 2 - m)), x)
            q, rem = sp.div(mu, A ** max(p - k, 0))
            divides = bool(rem.is_zero)
            root0 = sp.simplify(mu.eval(sp.sqrt(m))) == 0
            if not root0:
                print(f"{k:>2}{m:>3}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{'NO ROOT':>9}"
                      f"{lam:>9.4f}{'not a candidate':>15}", flush=True)
                continue

        gaps = [t for t in gap_profile(n, edges) if t[1] - t[0] >= 0.05]
        ingap = [(lo, hi) for lo, hi in gaps if lo < lam < hi]
        if not ingap:
            print(f"{k:>2}{m:>3}{p:>3}{n:>5}{min(deg):>5}{kap:>6}"
                  f"{str(divides):>9}{lam:>9.4f}{'in spec (band)':>15}", flush=True)
            continue

        kind, v = classify(n, edges, lam)
        ctrl, _ = classify(n, edges, 0.0)
        verdict = 'VIOLATION' if kind == 'outside spec' else kind
        print(f"{k:>2}{m:>3}{p:>3}{n:>5}{min(deg):>5}{kap:>6}"
              f"{str(divides):>9}{lam:>9.4f}{verdict:>15}", flush=True)
        print(f"     gaps {[(round(a, 3), round(b, 3)) for a, b in gaps]};  "
              f"|Im G| = {'  '.join(f'{q:.2e}' for q in v)};  control at 0: {ctrl}")
        if kind == 'outside spec' and ctrl == 'ATOM' and kap >= 3:
            hits.append((k, m, p, n, min(deg), kap, lam))

    if hits:
        print("\n  P65(c) HOLDS. C2 IS FALSE TOO:")
        for (k, m, p, n, dm, kap, lam) in hits:
            print(f"    k={k} m={m} p={p}: n={n}, minimum degree {dm}, connectivity {kap}, "
                  f"root sqrt{m} = {lam:.6f} outside spec(T_G)")
        print("  Connectivity constrains G and not the divisor, exactly as minimum degree did.")
        print("  But the construction does NOT simply scale in k, and the negative rows above are")
        print("  the reason to say so: raising k also raises every leaf's degree and fills the gap")
        print("  in. k=3,m=3 violates at p=5 and p=6 and not at p=4, and both k=4 attempts land in")
        print("  a band, including (4,4,5) at kappa=4. So 4-connectivity is untouched here and is")
        print("  NOT claimed to fail. What is shown is that the two hypotheses actually proposed as")
        print("  repairs, minimum degree three and 3-connectivity, are both false.")
    else:
        print("\n  P65(c) FAILS on this sweep: no 3-connected violation found. C2 separates from")
        print("  D3, the extra hub is doing real work, and connectivity is where the repair lives.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
