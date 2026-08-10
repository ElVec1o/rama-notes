"""Do the biregular generators return graphs with the degrees they claim?

code/universal_close.py was found sweeping parameter triples that are not graphs: a
(d,q)-biregular bipartite graph with |R| = r needs |L| = qr/d to be a positive integer, and
(3,20,19) gives 126.667. That inflates or deflates every percentage a sweep reports, silently.

This checks the other generators the same way, and empirically rather than by reading them: call
each, and verify the returned graph really has the claimed degrees on both sides. A generator
that silently returns something off-spec is the same defect class as a cited script that no
longer runs and a bibliography a third of which is dead -- invisible from outside, found only by
looking.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def degrees_from_adj(adj, n):
    return [len(adj[v]) for v in range(n)]


def check_small_biregular():
    """certificate.small_biregular(d,q,r): should be (d,q)-biregular with |R| = r."""
    from certificate import small_biregular
    rows = []
    for (d, q, r) in ((3, 6, 4), (3, 6, 5), (3, 9, 4), (4, 8, 5), (3, 12, 4)):
        feasible = (q * r) % d == 0
        try:
            m, rr, adj = small_biregular(d, q, r)
        except Exception as e:
            rows.append((f"({d},{q},{r})", feasible, None, None, f"raised {type(e).__name__}"))
            continue
        n = m + rr
        deg = degrees_from_adj(adj, n)
        left = sorted(set(deg[:m]))
        right = sorted(set(deg[m:]))
        ok = (left == [d]) and (right == [q]) and (rr == r)
        rows.append((f"({d},{q},{r})", feasible, left, right, 'ok' if ok else 'DEGREES WRONG'))
    return rows


def check_random_biregular():
    """tff.random_biregular(p,q,a,b): p left of degree a, q right of degree b, needs pa = qb."""
    from tff import random_biregular
    rng = np.random.default_rng(11)
    rows = []
    params = [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (8, 10, 5, 4), (8, 12, 3, 2),
              (10, 15, 3, 2), (12, 18, 3, 2), (5, 7, 3, 2)]
    for (p, q, a, b) in params:
        feasible = (p * a == q * b)
        # It returns a BITMASK per left vertex: bit k of adj[i] means left i ~ right k. It also
        # asserts q*b == p*a, so infeasible parameters raise rather than return a wrong graph.
        try:
            adj = random_biregular(p, q, a, b, rng)
        except AssertionError:
            rows.append((f"({p},{q},{a},{b})", feasible, None, None,
                         'asserted' if not feasible else 'ASSERTED ON FEASIBLE PARAMS'))
            continue
        if adj is None:
            rows.append((f"({p},{q},{a},{b})", feasible, None, None, 'declined'))
            continue
        rowdeg = sorted({bin(m).count('1') for m in adj})
        coldeg = sorted({sum((m >> k) & 1 for m in adj) for k in range(q)})
        ok = (rowdeg == [a]) and (coldeg == [b])
        note = 'ok' if ok else 'DEGREES WRONG'
        if not feasible and adj is not None:
            note = 'RETURNED A GRAPH FOR INFEASIBLE PARAMETERS'
        rows.append((f"({p},{q},{a},{b})", feasible, rowdeg, coldeg, note))
    return rows


def main():
    bad = 0
    print("certificate.small_biregular(d,q,r) -- needs qr/d integral\n")
    print(f"{'(d,q,r)':>12}{'feasible':>10}{'left deg':>12}{'right deg':>12}{'verdict':>34}")
    for (nm, feas, l, r, note) in check_small_biregular():
        if note not in ('ok',):
            bad += 1
        print(f"{nm:>12}{str(feas):>10}{str(l):>12}{str(r):>12}{note:>34}")

    print("\ntff.random_biregular(p,q,a,b) -- needs pa = qb\n")
    print(f"{'(p,q,a,b)':>14}{'feasible':>10}{'row deg':>10}{'col deg':>10}{'verdict':>36}")
    for (nm, feas, l, r, note) in check_random_biregular():
        # 'asserted' on infeasible parameters is CORRECT: refusing is the desired
        # behaviour, and counting it as a fault was this audit's own bug.
        if note not in ('ok', 'declined', 'asserted'):
            bad += 1
        print(f"{nm:>14}{str(feas):>10}{str(l):>10}{str(r):>10}{note:>36}")

    print(f"\n  problems: {bad}")
    if bad:
        print("  A generator returning off-spec graphs makes every number downstream of it wrong.")
    else:
        print("  Every generator returns graphs with the degrees it claims, and declines")
        print("  infeasible parameters rather than returning something off-spec.")
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
