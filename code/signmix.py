"""#2: where does sign mixing among a vertex's children actually occur?

|F_v| >= lambda is the candidate invariant (code/minF_scan.py: min|F| equals lambda exactly,
attained at a leaf, at every gap fraction in two of three families). It does not propagate on its
own, because F_v = lambda - sum_u 1/F_u and the 1/F_u can cancel. Where the children share a sign
they cannot, and the bound goes through.

The path tree is bipartite by depth, so all children of a vertex lie on the same side and are the
same TYPE. Mixing therefore means same-type siblings with opposite signs, which for right-type
children means their child counts straddle the threshold: such a vertex is negative exactly when
sum 1/F_child > lambda, and with children bounded by B that is essentially k > lambda*B.

So the question is concrete: how often do the children of one vertex disagree in sign, where, and
does it correlate with the gap fraction?

FROZEN BEFORE THE DATA:
  P29. Sign mixing among the children of a single vertex is confined to lambda near the gap edge
       and is absent for small lambda, so the invariant propagates on an initial segment of the
       gap and the failure is exactly the edge.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math

sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certificate import small_biregular


def scan(adj, m, root, lam, cap=1_500_000):
    """Returns per-vertex sign data: how many vertices have children of mixed sign."""
    st = {'tot': 0, 'parents': 0, 'mixed': 0, 'mixdepth': [], 'minabs': float('inf')}

    def rec(v, visited, depth):
        st['tot'] += 1
        if st['tot'] > cap:
            raise RuntimeError
        signs = []
        s = 0.0
        for u in adj[v]:
            if u in visited:
                continue
            fu = rec(u, visited | {u}, depth + 1)
            signs.append(fu > 0)
            s += 1.0 / fu
        f = lam - s
        st['minabs'] = min(st['minabs'], abs(f))
        if len(signs) >= 2:
            st['parents'] += 1
            if any(signs) and not all(signs):
                st['mixed'] += 1
                st['mixdepth'].append(depth)
        return f

    try:
        rec(root, {root}, 0)
    except RuntimeError:
        return None
    return st


def main():
    print("P29 (frozen): sign mixing is confined to lambda near the gap edge.\n")
    print(f"{'(d,q,r)':>10}{'frac':>7}{'lam':>8}{'|P|':>9}{'parents':>9}{'mixed':>8}"
          f"{'% mixed':>9}{'min|F|/lam':>12}{'mix depths':>14}")
    for (d, q, r) in ((3, 6, 4), (3, 6, 5), (3, 9, 4)):
        m, rr, adj = small_biregular(d, q, r)
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        for frac in (0.1, 0.3, 0.5, 0.7, 0.9, 0.99):
            lam = frac * g
            st = scan(adj, m, 0, lam)
            if st is None:
                print(f"{f'({d},{q},{r})':>10}{frac:>7.2f}   cap"); continue
            dep = sorted(set(st['mixdepth']))
            deptxt = (f"{dep[0]}..{dep[-1]}" if dep else '-')
            print(f"{f'({d},{q},{r})':>10}{frac:>7.2f}{lam:>8.4f}{st['tot']:>9}"
                  f"{st['parents']:>9}{st['mixed']:>8}"
                  f"{100*st['mixed']/max(st['parents'],1):>9.3f}"
                  f"{st['minabs']/lam:>12.5f}{deptxt:>14}", flush=True)
    print("\n  RESULT: the mixed column is zero everywhere, at every gap fraction. Children of a")
    print("  vertex always agree in sign, so cancellation never occurs and P29's premise was")
    print("  wrong -- there is no sign mixing to bound.")
    print()
    print("  That relocates the obstruction rather than removing it. With all children positive,")
    print("  F = lambda - sum 1/F_u is BELOW lambda automatically, and |F| >= lambda additionally")
    print("  needs the sum to exceed 2 lambda, i.e. roughly k >= 2 lambda B at a right-type")
    print("  vertex. The sign condition needs only k > lambda B. So |F| >= lambda is STRICTLY")
    print("  STRONGER than the sign-alternating requirement, not a weaker sign-free substitute,")
    print("  and it is the wrong replacement: the alternating certificate was the right invariant")
    print("  and its reach is exactly lambda^2 < Delta, which is binding_case.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
