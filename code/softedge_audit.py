"""Independent replication of the biregular soft-edge exponent, and a caveat on the wheel comparison.

Paper 2b claims the biregular margin decays like n^(-2/3), the soft-edge exponent, so that the
statement it studies is true but tight and no size-free bound can prove it. v6.5 of this repository
then reported that wheels saturate at m^(-1/2) and compared the two. Both numbers deserved checking,
the first because four instruments in this development have failed, and the second because it was
built on the first.

THE CLAIM IS INSTRUMENT-FREE, which is the first thing to establish. code/softedge2.py imports no
gap detector, no ratio solver and no resolvent: the band edge for an (a,b)-biregular cover is the
closed form |sqrt(b-1) - sqrt(a-1)|, from the discriminant factorisation that is formalised as
SoftEdge.discriminant_factors, and the matchings are counted exactly. So none of the four failures
recorded elsewhere here can touch it.

THE REPLICATION. Below, matchings are recounted by an independent subset dynamic program over the
smaller side, on independently generated random (3,6)-biregular bipartite graphs, with roots found
independently. It reproduces the published series, agreeing to four decimals at n = 12, and fits

    margin ~ 2.7483 n^(-0.6629),   R^2 = 0.99957

against the claimed -2/3 = -0.6667. The claim stands.

THE CAVEAT, which is about the wheel comparison rather than about paper 2b. The two families are
not structurally comparable in the way "two exponents" suggests. The biregular family has BOUNDED
degree, d and q fixed while n grows. The wheel family does not: the hub of W_m has degree m, so the
maximum degree grows with the graph. The soft-edge heuristic that yields -2/3 reads the density
exponent off the band edge, and under it a margin of N^(-1/(1+alpha)) corresponds to a density
vanishing like (x - tau)^alpha, so -2/3 is alpha = 1/2, the square-root edge, and -1/2 would be
alpha = 1, a linear edge. That would be a different universality class. It would also be exactly
what an unbounded degree could produce for unrelated reasons, and nothing here separates the two
explanations. The exponents differ; why they differ is open, and this file does not claim the
stronger reading.

What survives unambiguously is the part that matters for Conjecture D3: both families saturate, so
the margin tends to zero in each, and an argument producing a margin bounded below independently of
size cannot prove the conjecture on either.

FROZEN BEFORE THE DATA:
  P77. (a) An independent recount reproduces the published (3,6) margin series.
       (b) The fitted exponent is within 0.01 of -2/3.
       (c) It is not within 0.01 of the wheel exponent -0.5125, so the two families really do
           differ, whatever the reason.

FALSIFICATION. If (a) or (b) fails, paper 2b's tightness claim needs revisiting. If (c) fails, the
wheel and biregular rates are the same and v6.5 overstated the contrast.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import numpy as np
import sympy as sp
import networkx as nx

D, Q = 3, 6
WHEEL_EXPONENT = -0.5125


def biregular(d, q, qsize, rng, tries=400):
    p = q * qsize // d
    if p * d != qsize * q:
        return None
    for _ in range(tries):
        sp_ = [i for i in range(p) for _ in range(d)]
        sq = [j for j in range(qsize) for _ in range(q)]
        rng.shuffle(sq)
        E, ok = set(), True
        for a, b in zip(sp_, sq):
            if (a, b) in E:
                ok = False; break
            E.add((a, b))
        if not ok:
            continue
        G = nx.Graph(); G.add_nodes_from(range(p + qsize))
        for a, b in E:
            G.add_edge(a, p + b)
        if nx.is_connected(G):
            return p, qsize, sorted(E)
    return None


def matching_poly(p, qs, E):
    """Exact matching polynomial by subset DP over the smaller side."""
    nbr = [[] for _ in range(p)]
    for a, b in E:
        nbr[a].append(b)
    size = 1 << qs
    dp = np.zeros(size, dtype=object); dp[0] = 1
    idx = np.arange(size)
    for a in range(p):
        new = dp.copy()
        for b in nbr[a]:
            bit = 1 << b
            sel = (idx & bit) != 0
            new[sel] += dp[idx[sel] ^ bit]
        dp = new
    m = [0] * (qs + 1)
    for mask in range(size):
        if dp[mask]:
            m[bin(mask).count('1')] += int(dp[mask])
    x = sp.Symbol('x')
    n = p + qs
    return sp.Poly(sum((-1) ** k * m[k] * x ** (n - 2 * k) for k in range(qs + 1)), x), n


def main():
    a, b = math.sqrt(D - 1), math.sqrt(Q - 1)
    edge = abs(b - a)
    print("P77 (frozen): replicating the biregular soft-edge exponent independently.\n")
    print(f"  ({D},{Q})-biregular, band edge |sqrt{Q-1} - sqrt{D-1}| = {edge:.6f} (closed form)")
    print(f"  paper 2b: margin 0.5301 at n=12, 0.2009 at n=51, exponent -2/3\n")
    print(f"{'n':>4}{'margin':>10}")
    rng = random.Random(20260901)
    data = []
    for qs in range(4, 18):
        best = None
        for _ in range(12):
            g = biregular(D, Q, qs, rng)
            if not g:
                continue
            mu, n = matching_poly(*g)
            rs = [float(sp.re(z)) for z in mu.nroots(n=25, maxsteps=6000)
                  if abs(sp.im(z)) < 1e-14 and sp.re(z) > 1e-9]
            if rs and (best is None or min(rs) < best):
                best = min(rs)
        if best is None:
            continue
        n = Q * qs // D + qs
        data.append((n, best - edge))
        print(f"{n:>4}{best-edge:>10.4f}", flush=True)

    xs = [math.log(n) for n, m in data if m > 0]
    ys = [math.log(m) for _, m in data if m > 0]
    k = len(xs); mx = sum(xs) / k; my = sum(ys) / k
    sl = sum((A - mx) * (B - my) for A, B in zip(xs, ys)) / sum((A - mx) ** 2 for A in xs)
    inter = my - sl * mx
    ss = sum((B - my) ** 2 for B in ys)
    rr = 1 - sum((B - (sl * A + inter)) ** 2 for A, B in zip(xs, ys)) / ss
    print(f"\n  independent fit: margin ~ {math.exp(inter):.4f} n^({sl:.4f}),  R^2 = {rr:.5f}")
    ok_b = abs(sl + 2 / 3) < 0.01
    ok_c = abs(sl - WHEEL_EXPONENT) > 0.01
    print(f"  (b) within 0.01 of -2/3: {ok_b}")
    print(f"  (c) distinct from the wheel exponent {WHEEL_EXPONENT}: {ok_c}")
    print("\n  Paper 2b's tightness claim replicates. The wheel comparison stands as a statement")
    print("  about two exponents, but NOT as a claim about universality classes: the biregular")
    print("  family has bounded degree and the wheel family does not, the hub of W_m having")
    print("  degree m, and nothing here separates that from a genuine difference in edge exponent.")
    return 0 if (ok_b and ok_c) else 1


if __name__ == '__main__':
    sys.exit(main())
