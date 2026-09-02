"""Exhaustive test of the two claims behind the refined degree bound.

  C1 (combinatorial, exact integers): over trees of order 2m the maximum of m_(nu-1)/m_nu is
     binom(m+1,2), attained by the path; over trees of order 2m+1 it is m^2/2.
  C2 (spectral, floating point): the minimum of |theta| over nowhere-vanishing eigenpairs of trees
     of order at most n equals 2 cos(m pi/(2m+1)) for the largest even 2m <= n.

C1 is what the matching bound theta^2 >= m_nu/m_(nu-1) needs in order to become a bound on
kappa(theta), and it is decided here in exact arithmetic. C2 is the sharp statement.

FROZEN BEFORE THE DATA:
  P84. (a) C1 holds at every order reached, with the path the unique even-order maximiser.
       (b) C2 holds at every order reached.
       (c) The order-9 minimum is unchanged by the two trees the old Prufer script lost to
           cospectral dedup, i.e. it is still 0.390181.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
from fractions import Fraction
import numpy as np
from freetrees import free_trees, matching_counts

BUDGET = float(os.environ.get('BUDGET', 1800))
NMAX = int(os.environ.get('NMAX', 16))
TOL = 1e-7


def qualifying(A):
    """Eigenvalues with an eigenvector that is nonzero at every vertex.

    Coordinate i vanishes on the whole eigenspace exactly when row i of an orthonormal basis of
    that eigenspace is zero, so the eigenspace contains a nowhere-vanishing vector iff every row
    of the basis is nonzero."""
    w, V = np.linalg.eigh(A)
    out, i, n = [], 0, len(w)
    while i < n:
        j = i
        while j + 1 < n and w[j + 1] - w[i] < 1e-8:
            j += 1
        B = V[:, i:j + 1]
        if np.linalg.norm(B, axis=1).min() > TOL:
            out.append(w[i])
        i = j + 1
    return out


def main():
    t0 = time.time()
    print("P84 (frozen): the exact combinatorial claim C1 and the spectral claim C2 both hold.\n")
    print(f"{'n':>3}{'trees':>8}{'max m(v-1)/m(v)':>17}{'predicted':>11}{'path?':>7}"
          f"{'min|th| qualifying':>20}{'path value':>12}{'ok':>4}", flush=True)
    running = None
    ok1 = ok2 = True
    for n in range(2, NMAX + 1):
        if time.time() - t0 > BUDGET:
            print(f"\n  budget reached before n={n}", flush=True)
            break
        m = n // 2
        pred = Fraction(m * (m + 1), 2) if n % 2 == 0 else Fraction(m * m, 2)
        best = Fraction(-1)
        best_is_path = False
        minq = None
        cnt = 0
        for adj in free_trees(n):
            cnt += 1
            mc = matching_counts(n, adj)
            nu = len(mc) - 1
            r = Fraction(mc[nu - 1], mc[nu])
            ispath = max(len(a) for a in adj) <= 2
            if r > best:
                best, best_is_path = r, ispath
            elif r == best and ispath:
                best_is_path = True
            A = np.zeros((n, n))
            for v in range(n):
                for u in adj[v]:
                    A[v][u] = 1.0
            q = [abs(l) for l in qualifying(A) if abs(l) > TOL]
            if q:
                lo = min(q)
                if minq is None or lo < minq:
                    minq = lo
        running = minq if running is None else min(running, minq)
        pv = 2 * math.cos(m * math.pi / (2 * m + 1))
        c1 = (best == pred) and (n % 2 == 1 or best_is_path)
        c2 = abs(running - pv) < 1e-7
        ok1 &= c1
        ok2 &= c2
        print(f"{n:>3}{cnt:>8}{str(best):>17}{str(pred):>11}{str(best_is_path):>7}"
              f"{running:>20.9f}{pv:>12.9f}{('OK' if (c1 and c2) else 'FAIL'):>4}", flush=True)

    print(f"\n{time.time() - t0:.0f}s")
    print(f"  C1 (exact, max m_(nu-1)/m_nu): {'HOLDS' if ok1 else 'FAILS'} at every order reached.")
    print(f"  C2 (spectral, running minimum): {'HOLDS' if ok2 else 'FAILS'} at every order reached.")
    if ok1:
        print("  So the matching bound theta^2 >= m_nu/m_(nu-1) yields kappa(theta) >= ~2 sqrt2/|theta|")
        print("  unconditionally in the verified range, and only the combinatorial maximum is open.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
