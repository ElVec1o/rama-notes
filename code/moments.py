"""Do higher moments extend the dimension-restricted bounds for the plane class?

The two unconditional bounds in the note come from the first two power sums. Writing
F_A(x) = x^m - M_1 x^{m-2} + M_2 x^{m-4} - ... and y = x^2, the M_r are the elementary
symmetric functions of the y-roots, so with p_k the power sums,

    y_max^k <= p_k,

and the band |x| <= 2 sqrt(a), that is y_max <= 4a, follows from any a-priori bound
p_k <= B_k with B_k <= (4a)^k. The note uses

    k=1:  p_1 = M_1 = (1/2) tr Adj(A) <= a m / 2      giving  m <= 8
    k=2:  p_2 = M_1^2 - 2 M_2 <= tr Adj(A)^2 - sum c_k^2 <= a^2 m - sum c_k^2
                                                     giving  m <= 16 + (sum c_k^2)/a^2

and stops there. If p_k <= a^k m held for every k, the third and fourth moments would give
m <= 64 and m <= 256, roughly a factor of four per moment.

FROZEN BEFORE THE DATA:
  P14. p_k <= a^k m for k = 3 and k = 4 on weighted 2-plane families with Adj(A) <= aI, so the
       higher moments extend the provable range as above.

If P14 fails the ratio p_k / (a^k m) is what a bound would have to be, and measuring it says
which k are worth pursuing and what constant is available.

COMPUTATION. A wedge of decomposable bivectors is decomposable, so for T a set of planes
omega_T = (prod_{k in T} c_k)^{1/2} u_{k1} ^ v_{k1} ^ ... and

    ||omega_T||^2 = (prod_{k in T} c_k) * det Gram(u_k, v_k : k in T),

which gives M_r = sum over |T| = r exactly. Families are generated as random 2-planes with
nonnegative weights, rescaled so that the largest eigenvalue of sum c_k P_k is exactly a, which
is the extreme case of the constraint.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import itertools
import numpy as np

rng = np.random.default_rng(20260819)


def random_family(m, q, a, kind='general'):
    """q weighted 2-planes in R^m with sum c_k P_k EXACTLY aI, the extremal case of the
    constraint.  Coordinate families come from regular graphs, where unit weights already give
    the degree matrix aI; general families solve for nonnegative weights by NNLS against the
    target aI, and are rejected unless the residual is negligible."""
    from scipy.optimize import nnls
    if kind == 'coordinate':
        # a random a-regular graph on m vertices, unit weights: sum P_e = D = aI
        import networkx as nx
        try:
            G = nx.random_regular_graph(a_int := int(round(a)), m, seed=int(rng.integers(1 << 30)))
        except Exception:
            return None
        frames = []
        for (u, v) in G.edges():
            B = np.zeros((m, 2)); B[u, 0] = 1.0; B[v, 1] = 1.0
            frames.append(B)
        return frames, np.ones(len(frames))
    frames = []
    for _ in range(q):
        B = rng.standard_normal((m, 2))
        B, _ = np.linalg.qr(B)
        frames.append(B)
    iu = np.triu_indices(m)
    Acols = np.stack([(B @ B.T)[iu] for B in frames], axis=1)
    target = (a * np.eye(m))[iu]
    w = np.array([1.0 if i == j else math.sqrt(2.0) for i, j in zip(*iu)])
    c, res = nnls(Acols * w[:, None], target * w)
    S = sum(ci * (B @ B.T) for ci, B in zip(c, frames))
    if np.abs(S - a * np.eye(m)).max() > 1e-8:
        return None
    return frames, c


def moments(frames, c, m):
    """M_r for r = 0 .. floor(m/2), by Gram determinants over subsets."""
    q = len(frames)
    rmax = m // 2
    M = [0.0] * (rmax + 1)
    M[0] = 1.0
    for r in range(1, rmax + 1):
        if r > q:
            break
        tot = 0.0
        for T in itertools.combinations(range(q), r):
            C = np.hstack([frames[k] for k in T])
            G = C.T @ C
            d = np.linalg.det(G)
            if d > 0:
                tot += float(np.prod([c[k] for k in T])) * d
        M[r] = tot
    return M


def power_sums(M, kmax):
    """p_k from e_r = M_r by Newton's identities."""
    p = []
    for k in range(1, kmax + 1):
        s = 0.0
        for i in range(1, k):
            s += (-1) ** (i - 1) * M[i] * p[k - i - 1]
        s += (-1) ** (k - 1) * k * (M[k] if k < len(M) else 0.0)
        p.append(s)
    return p


def main():
    print("P14 (frozen): p_k <= a^k m for k = 3, 4, so higher moments extend the range.\n")
    print(f"{'kind':>11}{'m':>4}{'q':>4}{'a':>5}"
          + "".join(f"{f'p{k}/(a^{k} m)':>15}" for k in (1, 2, 3, 4))
          + f"{'y_max/(4a)':>12}")
    worst = {1: 0.0, 2: 0.0, 3: 0.0, 4: 0.0}
    for kind in ('coordinate', 'general'):
        for (m, q, a) in ((6, 20, 3.0), (8, 26, 3.0), (8, 26, 4.0), (10, 34, 3.0),
                          (10, 34, 5.0), (12, 40, 4.0)):
            best = None
            for _ in range(8):
                fam = random_family(m, q, a, kind)
                if fam is None: continue
                frames, c = fam
                M = moments(frames, c, m)
                p = power_sums(M, 4)
                coef = [((-1) ** r) * M[r] for r in range(len(M))]
                roots = np.roots(coef)
                ry = [t.real for t in roots if abs(t.imag) < 1e-8 and t.real > 0]
                ymax = max(ry) if ry else 0.0
                ratios = [p[k - 1] / (a ** k * m) for k in (1, 2, 3, 4)]
                if best is None or ratios[2] > best[0][2]:
                    best = (ratios, ymax)
            if best is None:
                print(f"{kind:>11}{m:>4}{q:>4}{a:>5.1f}   no exact tight frame found"); continue
            ratios, ymax = best
            for k in (1, 2, 3, 4):
                worst[k] = max(worst[k], ratios[k - 1])
            print(f"{kind:>11}{m:>4}{q:>4}{a:>5.1f}"
                  + "".join(f"{ratios[k-1]:>15.4f}" for k in (1, 2, 3, 4))
                  + f"{ymax/(4*a):>12.4f}")
    print(f"\n  worst p_k/(a^k m) seen: "
          + ", ".join(f"k={k}: {worst[k]:.4f}" for k in (1, 2, 3, 4)))
    print("\n  If a ratio stays below 1, the bound p_k <= a^k m is available at that k, and the")
    print("  provable range is m <= 4^k. Ratios far below 1 mean a better constant, and hence a")
    print("  larger range, is on the table.")
    for k in (1, 2, 3, 4):
        if worst[k] > 0:
            reach = (4 ** k) / worst[k]
            print(f"    k={k}: with constant {worst[k]:.4f} the range is m <= {reach:.0f}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
