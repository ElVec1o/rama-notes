"""Does the path tree inherit the gap on a NON-complete-bipartite biregular graph?

pathtree_spec.py answered yes for K_{6,3} and K_{9,3} by diagonalising the path tree whole. That
is the least informative family: complete bipartite is where the inner edge is already proved, so
the gap being inherited there may be an artefact of the solved case rather than a phenomenon. The
smallest non-complete-bipartite (3,6)-biregular graph has 12 vertices and a path tree far beyond
what can be diagonalised.

It does not need to be. On a tree, with F_v = mu_{T_v}/mu_{T_v - v} the ratio the cavity recursion
computes,

    mu_P(lambda) = prod_v F_v(lambda),

and the F_v are the pivots of the LDL factorisation of (lambda I - A_P). By Sylvester's law of
inertia the number of v with F_v < 0 is exactly the number of eigenvalues of the path tree
strictly ABOVE lambda. So counting negative ratios at two values of lambda counts the eigenvalues
between them, in O(|P|) time and O(depth) memory, with no matrix at all.

If the count is equal just above 0 and just below the gap edge g, the path tree has no eigenvalue
in (0,g) and inherits the gap.

FROZEN BEFORE THE DATA:
  P28. The inertia count is the same at both ends of the gap for a non-complete-bipartite
       biregular graph, so the path tree inherits the gap there too.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certificate import small_biregular


def inertia(adj, root, lam, cap=4_000_000):
    """(#negative pivots, #vertices, ok). ok is False on a near-zero pivot, where the count
    is not trustworthy and lambda is essentially an eigenvalue."""
    neg = [0]
    tot = [0]
    ok = [True]

    def rec(v, visited):
        tot[0] += 1
        if tot[0] > cap:
            raise RuntimeError('cap')
        s = 0.0
        for u in adj[v]:
            if u in visited:
                continue
            fu = rec(u, visited | {u})
            if abs(fu) < 1e-12:
                ok[0] = False
                fu = 1e-12 if fu >= 0 else -1e-12
            s += 1.0 / fu
        f = lam - s
        if f < 0:
            neg[0] += 1
        return f

    try:
        rec(root, {root})
    except RuntimeError:
        return None
    return neg[0], tot[0], ok[0]


def main():
    print("P28 (frozen): the inertia count is equal at both ends of the gap, so the path tree")
    print("inherits the gap on a non-complete-bipartite biregular graph too.\n")
    print("Counting eigenvalues of the path tree in (0,g) by Sylvester's law: the number of")
    print("negative cavity ratios is the number of eigenvalues above lambda.\n")
    print(f"{'(d,q,r)':>12}{'|P|':>10}{'gap g':>9}{'neg @ 0+':>10}{'neg @ g-':>10}"
          f"{'eigs in gap':>13}{'verdict':>11}")
    for (d, q, r) in ((3, 6, 4), (3, 6, 5), (3, 9, 4), (4, 8, 5)):
        try:
            m, rr, adj = small_biregular(d, q, r)
        except Exception as e:
            print(f"{f'({d},{q},{r})':>12}   generator failed: {type(e).__name__}")
            continue
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        lo = inertia(adj, 0, 1e-6)
        hi = inertia(adj, 0, g - 1e-6)
        if lo is None or hi is None:
            print(f"{f'({d},{q},{r})':>12}   path tree exceeds cap")
            continue
        nlo, tot, oklo = lo
        nhi, _, okhi = hi
        inside = nlo - nhi
        note = '' if (oklo and okhi) else ' (near-zero pivot)'
        print(f"{f'({d},{q},{r})':>12}{tot:>10}{g:>9.4f}{nlo:>10}{nhi:>10}"
              f"{inside:>13}{('INHERITS' if inside == 0 else 'has eigs'):>11}{note}",
              flush=True)
    print("\n  A count of zero means no eigenvalue of the path tree lies in the gap, so the")
    print("  statement the ratio method proves is true there and the failure at the gap edge is")
    print("  the invariant's, not the method's.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
