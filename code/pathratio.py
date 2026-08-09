"""The ratio route: what do the cavity ratios actually do on a path tree inside a gap?

CRUX (ledger entry, Rule I1). For G a (d,q)-biregular graph and lambda in (0, g) a gap point of
spec(T), show mu_G(lambda) != 0.  Blocks: the biregular case of Conjecture 10, equivalently
Song-Fan-Miao Problem 1.  Smallest instance: any connected (3,6)-biregular graph with lambda in
(0, sqrt5 - sqrt2).  Unblocking criterion: the statement above at PROVED.

WHY THIS ROUTE.  Compression arguments are barred (SoftEdge.rayleigh_in_gap): a quadratic form
cannot separate a gap point from a spectral point.  The ratio recursion is not barred, because
it bounds ratios of matching polynomials rather than Rayleigh quotients.  By Godsil, mu_G
divides mu_P for the path tree P, and on a tree the deletion recurrence is exact and local:

    F_v = lambda - sum over children u of 1/F_u,      F_leaf = lambda.

So mu_G(lambda) != 0 follows if no F vanishes anywhere on P.

THE OBSTRUCTION TO THE OBVIOUS CERTIFICATE.  If every child ratio lies in [a,b] with a > 0 then
the parent lies in [lambda - k/a, lambda - k/b], so invariance needs a <= lambda - k/a, that is
a^2 - lambda a + k <= 0, which has a positive solution only when lambda >= 2 sqrt(k).  That is
the Heilmann-Lieb bound: a POSITIVE invariant interval exists only above the band, never inside
the gap.  Consistent with the tree fixed point, which for (3,6) at lambda = 0.5 is
F_d = 0.8915 > 0 and F_q = -5.109 < 0.  Any certificate valid in the gap must therefore be
sign-alternating, and the leaves, where F = lambda > 0 regardless of type, are where that
structure is under strain.

THIS FILE MEASURES, IT DOES NOT ASSUME.  It builds the path tree explicitly, computes every
cavity ratio bottom-up, and reports what a certificate would have to cover: the sign pattern by
type and depth, how close to zero the ratios come, and whether the values cluster near the tree
fixed point.  Design of the certificate waits on that.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import cmath
from collections import defaultdict


def small_biregular(d, q, r):
    """left i joined to right (i*d+j) mod r; exactly biregular."""
    m = (r * q) // d
    nbr = [sorted({(i * d + j) % r for j in range(d)}) for i in range(m)]
    adj = {i: set() for i in range(m + r)}
    for i, s in enumerate(nbr):
        for j in s:
            adj[i].add(m + j); adj[m + j].add(i)
    return m, r, adj


def tree_fixed_point(d, q, lam):
    """F_d = lam - (d-1)/F_q, F_q = lam - (q-1)/F_d, real branches."""
    A1, B1 = d - 1, q - 1
    # lam*u^2 - (A1 + B1 - ... ) : derive by substitution, solve the quadratic in F_d
    # u = lam - A1/(lam - B1/u)  =>  lam*u^2 - (A1 + B1 + lam^2 ... ) handled numerically
    sols = []
    for guess in (0.1, 1.0, 5.0, -1.0, -5.0):
        u = guess
        ok = True
        for _ in range(20000):
            den = lam - B1 / u if abs(u) > 1e-14 else None
            if den is None or abs(den) < 1e-14:
                ok = False; break
            nu = lam - A1 / den
            if abs(nu - u) < 1e-14:
                u = nu; break
            u = nu
        if ok and abs(u) > 1e-9:
            fq = lam - B1 / u
            sols.append((u, fq))
    out = []
    for s in sols:
        if not any(abs(s[0] - t[0]) < 1e-7 for t in out):
            out.append(s)
    return out


def path_ratios(adj, m, root, lam, maxpaths=400000):
    """Every cavity ratio on the path tree rooted at `root`, computed bottom-up.

    A path-tree vertex is a self-avoiding walk; its children are the extensions.  Returns a
    list of (depth, is_left_type, F) and the root ratio."""
    out = []
    count = [0]

    def rec(v, visited, depth):
        count[0] += 1
        if count[0] > maxpaths:
            raise RuntimeError('path tree too large')
        tot = lam
        for u in sorted(adj[v]):
            if u in visited:
                continue
            fu = rec(u, visited | {u}, depth + 1)
            if abs(fu) < 1e-13:
                raise ZeroDivisionError(f'ratio vanished at depth {depth+1}')
            tot -= 1.0 / fu
        out.append((depth, v < m, tot))
        return tot

    rootF = rec(root, {root}, 0)
    return out, rootF


def main():
    print("Cavity ratios on path trees, at gap points.  Measurement, not assumption.\n")
    for (d, q, r) in ((3, 6, 4), (3, 6, 5), (3, 9, 4)):
        m, rr, adj = small_biregular(d, q, r)
        n = m + rr
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        print(f"=== ({d},{q})-biregular, n={n} (left {m}, right {rr}), gap (0, {g:.4f})")
        for frac in (0.25, 0.5, 0.75, 0.95):
            lam = frac * g
            fps = tree_fixed_point(d, q, lam)
            fpstr = "  ".join(f"({a:.3f},{b:.3f})" for a, b in fps[:2]) if fps else "none found"
            try:
                vals, rootF = path_ratios(adj, m, 0, lam)
            except ZeroDivisionError as e:
                print(f"  lam={lam:.4f}: RATIO VANISHED -- {e}")
                continue
            except RuntimeError:
                print(f"  lam={lam:.4f}: path tree too large")
                continue
            pos = [t for t in vals if t[2] > 0]
            neg = [t for t in vals if t[2] < 0]
            mn = min(abs(t[2]) for t in vals)
            bytype = defaultdict(list)
            for dep, isleft, F in vals:
                bytype[isleft].append(F)
            print(f"  lam={lam:.4f}  paths={len(vals):>6}  min|F|={mn:.4f}  "
                  f"pos={len(pos)} neg={len(neg)}  rootF={rootF:.4f}")
            for isleft in (True, False):
                v = bytype[isleft]
                if not v:
                    continue
                print(f"      {'left (deg %d)' % d if isleft else 'right (deg %d)' % q:>14}: "
                      f"n={len(v):>6}  range [{min(v):.4f}, {max(v):.4f}]  "
                      f"neg {sum(1 for t in v if t < 0)}")
            print(f"      tree fixed points (F_d, F_q): {fpstr}")
        print()
    print("What a certificate must cover: the observed sign pattern and the distance of the")
    print("ratios from zero.  If the positive and negative ratios separate cleanly by vertex")
    print("type, a two-interval invariant is the right shape; if the leaves sit on the wrong")
    print("side, the certificate must treat depth explicitly.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
