"""Does refuting P16 close the moment ladder, or only raise its required input?

P16 (p_k <= (m/2) W_2k for the plane class) is refuted: code/p16verify.py finds noncommuting
families exceeding it, by 1.0079 at m=6, 1.1336 at m=8 and 1.3145 at m=10, all at a=3, under
two independent power-sum routes and machine-exact tightness. The coordinate case obeys it,
with equality at k=1,2.

That does NOT by itself close the ladder. The ladder never needed the tree count; it needs the
GROWTH RATE. Writing p_k = (m/2)c_k^k, the band y_max <= 4a follows for dimension

    m <= 2 (4a / c_k)^k,

which is unbounded in k exactly when lim c_k < 4a. The tree count has W_2k^(1/k) -> 4(a-1),
the square of the a-regular tree's spectral radius, comfortably below 4a. So an excess

    p_k <= (m/2) R^k W_2k

still gives unbounded reach provided 4(a-1)R < 4a, that is

    R < a/(a-1),

which is 1.5 at a=3 and 1.333 at a=4. The measured k-th roots of the excess ratios at m=10,
a=3 are 1.031, 1.046, 1.053, 1.056: far below 1.5. The refutation therefore raises the required
input rather than destroying it, UNLESS the rate itself grows with the dimension.

FROZEN BEFORE THE DATA:
  P17. R_m = max_k r_k(m)^(1/k) stays below a/(a-1) as m grows, so the ladder survives with
       the weaker input p_k <= (m/2) R^k W_2k.

If P17 holds the dimension restriction is still removable and the target statement is merely
weaker. If R_m crosses a/(a-1) the ladder is closed for the plane class and the two
unconditional bounds are the end of the method, which would be a genuine no-go.

COST. p_k needs only M_1..M_k, not all M_r, so the subset sums stop at size k. The Gram matrix
of a subset is the corresponding block submatrix of one fixed 2q x 2q Gram, so the subsets are
assembled by index rather than rebuilt, and the determinants run batched.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import itertools
import numpy as np
from scipy.optimize import nnls
import quickmode

rng = np.random.default_rng(20260821)

TOL_TIGHT = 1e-9
CHUNK = 150_000
# The wall clock is a SAFETY NET, not a knob: its value is the same in both modes, so it
# never binds under --quick and the short run's output is a function of the code alone.
# --quick truncates the CONFIGURATION below instead. Shrinking the clock is how a snapshot
# becomes load-dependent, which this repository has already had to fix seven times.
BUDGET_S = 2400.0


def tree_walks(a, kmax):
    """W_2k: closed walks of length 2k from the root of the a-regular tree."""
    W = []
    for k in range(1, kmax + 1):
        v = np.zeros(2 * k + 2); v[0] = 1.0
        for _ in range(2 * k):
            nv = np.zeros_like(v)
            nv[1] += a * v[0]
            for j in range(1, len(v) - 1):
                if v[j] == 0.0:
                    continue
                nv[j - 1] += v[j]
                nv[j + 1] += (a - 1) * v[j]
            v = nv
        W.append(float(v[0]))
    return W


def tight_family(m, q, a):
    """Random 2-planes, nonnegative weights by NNLS against aI, pruned to the support."""
    frames = [np.linalg.qr(rng.standard_normal((m, 2)))[0] for _ in range(q)]
    iu = np.triu_indices(m)
    w = np.array([1.0 if i == j else math.sqrt(2.0) for i, j in zip(*iu)])
    A = np.stack([(B @ B.T)[iu] for B in frames], axis=1)
    c, _ = nnls(A * w[:, None], (a * np.eye(m))[iu] * w)
    keep = [k for k in range(len(c)) if c[k] > 1e-10]
    frames = [frames[k] for k in keep]; c = c[keep]
    S = sum(ci * (B @ B.T) for ci, B in zip(c, frames))
    if float(np.abs(S - a * np.eye(m)).max()) > TOL_TIGHT:
        return None
    return frames, c


def elementary_upto(frames, c, kmax, t0):
    """M_1..M_kmax by batched block-submatrix determinants of one fixed Gram."""
    q = len(frames)
    C = np.hstack(frames)                 # m x 2q
    Gfull = C.T @ C                       # 2q x 2q
    logc = np.log(c)
    M = [1.0]
    for r in range(1, kmax + 1):
        if r > q:
            M.append(0.0); continue
        tot = 0.0
        it = itertools.combinations(range(q), r)
        while True:
            if time.time() - t0 > BUDGET_S:
                return None
            block = list(itertools.islice(it, CHUNK))
            if not block:
                break
            T = np.array(block, dtype=np.int64)                    # N x r
            cols = (2 * T[:, :, None] + np.arange(2)[None, None, :]).reshape(len(T), 2 * r)
            sub = Gfull[cols[:, :, None], cols[:, None, :]]        # N x 2r x 2r
            sgn, ld = np.linalg.slogdet(sub)
            wt = logc[T].sum(axis=1)
            ok = sgn > 0
            tot += float(np.exp(ld[ok] + wt[ok]).sum())
        M.append(tot)
    return M


def p_newton(M, kmax):
    p = []
    for k in range(1, kmax + 1):
        s = 0.0
        for i in range(1, k):
            s += (-1) ** (i - 1) * M[i] * p[k - i - 1]
        s += (-1) ** (k - 1) * k * (M[k] if k < len(M) else 0.0)
        p.append(s)
    return p


def main():
    print("P17 (frozen): R_m = max_k r_k^(1/k) stays below a/(a-1), so the ladder survives")
    print("the refutation of P16 with the weaker input p_k <= (m/2) R^k W_2k.\n")
    t0 = time.time()

    for a in (3, 4):
        thr = a / (a - 1)
        print(f"a = {a}:  ladder needs R < a/(a-1) = {thr:.4f}")
        print(f"{'m':>4}{'|supp|':>8}{'kmax':>6}"
              + "".join(f"{f'r{k}^(1/{k})':>12}" for k in (2, 3, 4, 5))
              + f"{'R_m':>9}{'verdict':>12}")
        prev = None
        for m in quickmode.few((6, 8, 10, 12, 14), 3):
            if time.time() - t0 > BUDGET_S:
                print("  [budget reached]")
                break
            kmax = min(5, m // 2)
            fam = None
            for _ in range(6 if quickmode.QUICK else 25):
                fam = tight_family(m, 4 * m * (m + 1) // 2, a)
                if fam is not None:
                    break
            if fam is None:
                print(f"{m:>4}   no tight family"); continue
            frames, c = fam
            W = tree_walks(a, kmax)
            M = elementary_upto(frames, c, kmax, t0)
            if M is None:
                print(f"{m:>4}{len(frames):>8}   [budget reached mid-computation]")
                break
            p = p_newton(M, kmax)
            r = [p[k - 1] / ((m / 2) * W[k - 1]) for k in range(1, kmax + 1)]
            roots = [r[k - 1] ** (1.0 / k) for k in range(2, kmax + 1)]
            R = max(roots) if roots else float('nan')
            print(f"{m:>4}{len(frames):>8}{kmax:>6}"
                  + "".join(f"{(roots[i] if i < len(roots) else float('nan')):>12.4f}"
                            for i in range(4))
                  + f"{R:>9.4f}"
                  + f"{('BELOW' if R < thr else 'CROSSED'):>12}")
            prev = (m, R)
        print()

    print("  A rate below the threshold at every m means the refutation of P16 costs the")
    print("  ladder a constant, not the method: the reachable dimension is still unbounded in")
    print("  k, at the reduced base 4a/(R*4(a-1)). A rate crossing it closes the ladder.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
