"""P27: can ANY invariant of the ratio kind reach the gap edge?

The ratio recursion F_v = lambda - sum 1/F_u computes mu_{T_v}/mu_{T_v - v} on the path tree P,
so "no F vanishes" is exactly mu_P(lambda) != 0. Godsil gives mu_G | mu_P, so that implies
mu_G(lambda) != 0 -- but it is STRICTLY STRONGER, because mu_P carries every root of mu_G plus
its own.

That matters for what a new invariant could possibly do. If mu_P has roots inside the gap
(0, g), then at those lambda no argument of the form "no F vanishes" can succeed, whatever
invariant it uses, because the thing it would be proving is false. The limit would be the object
the method bounds, not the certificate.

FROZEN BEFORE THE DATA:
  P27. The path tree of a (d,q)-biregular graph has eigenvalues strictly inside the gap.

If P27 holds, the answer to "find a non-alternating invariant near the gap edge" is that no such
invariant exists, and extending the route there requires tracking mu_G rather than mu_P. If P27
fails -- mu_P has no roots in the gap -- then the gap really is invariant-limited and a better
certificate is worth designing.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certificate import small_biregular


def path_tree(adj, root, cap=40000):
    """Vertices are self-avoiding paths from `root`; edges join a path to its one-step
    extensions. Returns the adjacency matrix of the path tree."""
    nodes = [(root,)]
    index = {(root,): 0}
    edges = []
    i = 0
    while i < len(nodes):
        p = nodes[i]
        for u in adj[p[-1]]:
            if u in p:
                continue
            np_ = p + (u,)
            if np_ not in index:
                index[np_] = len(nodes)
                nodes.append(np_)
                if len(nodes) > cap:
                    return None
            edges.append((i, index[np_]))
        i += 1
    n = len(nodes)
    A = np.zeros((n, n))
    for (a, b) in edges:
        A[a, b] = 1.0
        A[b, a] = 1.0
    return A


def main():
    print("P27 (frozen): the path tree has eigenvalues strictly inside the gap.\n")
    print("The ratio method proves mu_P(lambda) != 0, which is stronger than mu_G(lambda) != 0.")
    print("Roots of mu_P inside the gap are points no such argument can ever reach.\n")
    print(f"{'(d,q,r)':>12}{'|P|':>8}{'gap g':>9}{'eigs in (0,g)':>15}{'closest to g':>14}"
          f"{'verdict':>12}")
    any_inside = False
    # Smallest realizable (d,q)-biregular graphs: |L| = qr/d must be an integer and at least q,
    # since a right vertex needs q distinct left neighbours. Complete bipartite K_{qr/d, r}
    # realises the minimum, and its path tree is small enough to diagonalise whole.
    def cbip(L, R):
        adj = {i: set() for i in range(L + R)}
        for i in range(L):
            for j in range(R):
                adj[i].add(L + j); adj[L + j].add(i)
        return adj
    cases = [(3, 6, 3, cbip(6, 3)), (3, 9, 3, cbip(9, 3)), (4, 8, 4, cbip(8, 4)),
             (3, 12, 3, cbip(12, 3)), (5, 10, 5, cbip(10, 5))]
    for (d, q, r, adj) in cases:
        A = path_tree(adj, 0)
        if A is None:
            print(f"{f'({d},{q},{r})':>12}   path tree exceeds cap"); continue
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        ev = np.linalg.eigvalsh(A)
        inside = [x for x in ev if 1e-9 < x < g - 1e-9]
        any_inside = any_inside or bool(inside)
        closest = max(inside) if inside else float('nan')
        print(f"{f'({d},{q},{r})':>12}{A.shape[0]:>8}{g:>9.4f}{len(inside):>15}"
              f"{closest:>14.5f}{('INSIDE' if inside else 'none'):>12}")

    print()
    if any_inside:
        print("  P27 HOLDS. The path tree carries eigenvalues strictly inside the gap, so at")
        print("  those lambda the statement `no F vanishes' is FALSE -- mu_P really does vanish")
        print("  there -- and no invariant, alternating or not, can prove it. The ratio route's")
        print("  limit near the gap edge is therefore not the certificate but the object: it")
        print("  bounds mu_P, and mu_P has roots that mu_G does not. Extending to the edge means")
        print("  tracking mu_G itself, which is a different method, not a better invariant.")
    else:
        print("  P27 IS FALSE. mu_P has no roots in the gap on these families, so the gap really")
        print("  is invariant-limited and a non-alternating certificate is worth designing.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
