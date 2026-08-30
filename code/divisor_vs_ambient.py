"""SUPERSEDED. This script's spectral verdict cannot be trusted.

It uses the density-of-states and ratio-system machinery of code/d3_counterexample.py, whose
spectral verdict is retracted: in the graphs built here the branch union is a theta-Aomoto subset,
so the root is an EIGENVALUE of the universal cover and lies IN spec(T_G), not outside it. The
graph constructions, the two-cut identity and the gap scans are still correct; only the conclusion
drawn about spec(T_G) is wrong. See code/aomoto_obstruction.py. Conjectures D3 and C2 are OPEN.
"""

"""Is the barrier the ambient graph, or the divisor? The two are confounded until you separate them.

code/kboundary.py settles that k = 4 is not itself a threshold: at k = 4, m = 3 the gap reopens once
p >= 6, so the two clean rows of c2_attack.py were p too small. But it leaves a sharper question. In
that construction every violating row has m = 3 and every clean row has m >= 4, and m sets three
things at once:

    the divisor's top root sqrt(m),   the centre's degree m,   and kappa = min(m, k).

So "violations need m = 3" is compatible with three different readings: that the DIVISOR must be
small (root below 2), that the MINIMUM DEGREE must be three, or that the CONNECTIVITY must be three.
Raising m tests all three at once and distinguishes none of them.

BREAKING THE CONFOUND. Join the centre to the hubs as well as the leaves. The hubs are not branch
vertices, so the induced subgraph on a branch is still exactly K_{1,3} and

    A = mu_{K_{1,3}} = x^2 (x^2 - 3),   top root sqrt3,

unchanged, and the Divisibility Lemma still gives A^{p-k} | mu_G. But now

    deg(leaf) = 1 + k,   deg(centre) = 3 + k,   so delta(G) = k + 1 and kappa(G) = k.

The divisor is pinned while the ambient graph is free. At k = 4 that is minimum degree five and
vertex connectivity four, with the same rogue root sqrt3 as the 14-vertex counterexample.

FROZEN BEFORE THE DATA:
  P67. (a) The induced branch is still K_{1,3}, so A is unchanged and A^{p-k} | mu_G, verified
           exactly where n allows.
       (b) The construction VIOLATES at k = 4, hence at minimum degree five and connectivity four,
           so neither delta >= 4 nor kappa >= 4 is a threshold and the barrier is not ambient.
       (c) It violates at k = 5 as well, on the same reasoning, needing only larger p.

(b) is predicted because the mechanism that opened the gap was never the branch's own degrees: it
was the hub degree p*m, and pinning the divisor leaves that free. If (b) fails, the ambient degrees
really do swallow the root even when the divisor is held fixed, and that is a genuine structural
threshold rather than an accident of the K_{1,3} shape. Either answer is publishable; only one of
them is the answer the paper currently reaches for, which is why it is worth the compute.

FALSIFICATION. If the k >= 4 series is clean across the whole p range while k = 3 violates in it,
(b) is refuted and the ambient barrier is real.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
from twocut import mu_of, x
from gapscale import gap_profile, connectivity
from d3_counterexample import adj_of, classify
import quickmode

BUDGET = 2400.0
NMAX = 52
ETAS = (1e-3, 1e-4, 1e-5)
M_STAR = 3


def build_pinned(k, p, m=M_STAR):
    """k hubs, p copies of K_{1,m}, and EVERY branch vertex joined to all k hubs.

    The hubs are outside the branch, so the induced subgraph on a branch is still K_{1,m} and the
    divisor A is untouched; only the ambient degrees move."""
    edges = []
    nxt = k
    for _ in range(p):
        c = nxt; nxt += 1
        leaves = []
        for _ in range(m):
            l = nxt; nxt += 1
            edges.append((c, l))
            leaves.append(l)
        for w in [c] + leaves:
            for h in range(k):
                edges.append((w, h))
    return nxt, sorted(edges)


def main():
    lam = math.sqrt(M_STAR)
    print("P67 (frozen): pin the divisor, free the ambient graph, and the violation should")
    print(f"survive. Divisor is K_{{1,{M_STAR}}} throughout, root sqrt{M_STAR} = {lam:.6f}.\n")
    print(f"{'k':>2}{'p':>3}{'n':>5}{'dmin':>5}{'kappa':>6}{'A^(p-k)|mu':>12}"
          f"{'gap holding it':>18}{'verdict':>15}", flush=True)
    t0 = time.time()
    series = {}
    for k in ([3, 4] if quickmode.QUICK else [3, 4, 5]):
        for p in range(k + 1, 10):
            n = k + p * (M_STAR + 1)
            if n > NMAX or time.time() - t0 > BUDGET:
                continue
            edges = build_pinned(k, p)[1]
            adj = adj_of(n, edges)
            deg = [len(adj[i]) for i in range(n)]
            kap = connectivity(n, edges)

            div = '-'
            if n <= 24:
                mu = sp.Poly(sp.expand(mu_of(adj, set(range(n)))), x)
                A = sp.Poly(sp.expand(x ** (M_STAR - 1) * (x ** 2 - M_STAR)), x)
                _, rem = sp.div(mu, A ** (p - k))
                root0 = sp.simplify(mu.eval(sp.sqrt(M_STAR))) == 0
                div = 'yes' if (rem.is_zero and root0) else 'NO'
                if div == 'NO':
                    print(f"{k:>2}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{div:>12}"
                          f"{'-':>18}{'not a candidate':>15}", flush=True)
                    continue

            gaps = [t for t in gap_profile(n, edges) if t[1] - t[0] >= 0.05]
            ingap = [(lo, hi) for lo, hi in gaps if lo < lam < hi]
            if not ingap:
                print(f"{k:>2}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{div:>12}"
                      f"{'-':>18}{'in a band':>15}", flush=True)
                series.setdefault(k, []).append((p, False))
                continue
            kind, v = classify(n, edges, lam, etas=ETAS)
            ctrl, _ = classify(n, edges, 0.0, etas=ETAS)
            bad = (kind == 'outside spec' and ctrl == 'ATOM')
            g = ingap[0]
            print(f"{k:>2}{p:>3}{n:>5}{min(deg):>5}{kap:>6}{div:>12}"
                  f"{f'({g[0]:.2f},{g[1]:.2f})':>18}"
                  f"{('VIOLATION' if bad else kind):>15}", flush=True)
            series.setdefault(k, []).append((p, bad))

    print(f"\n{time.time()-t0:.0f}s\n")
    print("by k, with the divisor pinned to K_{1,3}:")
    for k in sorted(series):
        hits = [p for p, b in series[k] if b]
        rng = [p for p, _ in series[k]]
        print(f"  k={k} (delta={k+1}, kappa={k}): p tested {min(rng)}..{max(rng)}, "
              f"violates at p = {hits if hits else 'never in range'}")

    big = [k for k in series if k >= 4 and any(b for _, b in series[k])]
    if big:
        print("\n  P67(b) HOLDS. The barrier is NOT ambient. With the divisor pinned to K_{1,3},")
        print(f"  the violation survives at k = {sorted(big)}, that is at minimum degree "
              f"{min(big)+1} and")
        print(f"  vertex connectivity {min(big)}. So neither a minimum-degree nor a connectivity")
        print("  hypothesis is a threshold, and the clean rows of kboundary.py were the DIVISOR")
        print("  growing with m, not the ambient graph. What must be constrained is the divisor.")
    else:
        print("\n  P67(b) IS REFUTED. With the divisor held fixed, raising the ambient degrees")
        print("  closes the gap and keeps it closed across the p range tested. The band-widening")
        print("  barrier is real and is a property of the ambient graph, not of the K_{1,3} shape.")
        print("  That is evidence for a genuine threshold, bounded by the p and n ranges above.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
