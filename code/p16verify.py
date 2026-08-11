"""Verify the refutation of P16, and ask whether the excess also breaks the band.

P16 was frozen before the data as

    p_k <= (m/2) W_{2k}   for every weighted 2-plane family with Adj(A) = aI,

with W_{2k} the number of closed walks of length 2k from a root of the a-regular tree. It is
the a-priori input that would remove the dimension restriction from every rung of the moment
ladder at once (RamaLean/MomentLadder.lean). A first run (code/momentbound.py) found one
noncommuting family at m=8, a=3 exceeding it, rising to 1.1173 at k=4. One family is not
enough to act on, so this script re-tests it under three independent controls.

CONTROL 1 -- p_k computed twice, by routes that share no code. Newton's identities from the
elementary symmetric functions M_r, and directly as sum y_i^k over the roots of F_A. The
deletion recursion returns SIGNED coefficients, and feeding those to Newton negates the odd
power sums while leaving the even ones right, which is exactly the bug that would fake an
excess at even k. Disagreement between the two routes rejects the family.

CONTROL 2 -- the frame is tight to machine precision. The whole statement is conditioned on
Adj(A) = aI, so the NNLS residual is reported and anything above 1e-9 is discarded. The
support is pruned first: an NNLS solution against the m(m+1)/2 dimensional target has at most
that many nonzero weights, so the subset sums run over the support, not over all q planes.
That is what makes the check cheap enough to repeat.

CONTROL 3 -- volume. The first run tested one family per configuration. Here every
configuration is sampled many times and the worst case is kept, so a single unlucky draw
cannot decide the question either way.

The band y_max <= 4a is tracked throughout. Exceeding the tree MOMENT bound does not by itself
exceed the band -- the bound is sufficient, not necessary -- so the two questions are separate
and both are reported.
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

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import quickmode

rng = np.random.default_rng(20260820)

TOL_TIGHT = 1e-9      # max entry of |sum c_k P_k - aI| allowed
TOL_AGREE = 1e-6      # relative disagreement allowed between the two p_k routes
BUDGET_S = 900.0      # wall clock ceiling; --quick truncates the configuration, not this


def tree_walks(a, kmax):
    """W_{2k}: closed walks of length 2k from the root of the a-regular tree.

    DP on distance from the root. A walk at distance 0 has a neighbours, all at distance 1;
    at distance j >= 1 it has one neighbour at distance j-1 and a-1 at distance j+1.
    """
    W = []
    for k in range(1, kmax + 1):
        v = np.zeros(2 * k + 2)
        v[0] = 1.0
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


def elementary(frames, c, m):
    """M_r for r = 0..floor(m/2) by Gram determinants over subsets of the support.

    A wedge of decomposable bivectors is decomposable, so for a set T of planes
    ||omega_T||^2 = (prod_{k in T} c_k) det Gram(u_k, v_k : k in T), and M_r is the sum over
    all |T| = r.
    """
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
            d = float(np.linalg.det(C.T @ C))
            if d > 0.0:
                tot += float(np.prod([c[k] for k in T])) * d
        M[r] = tot
    return M


def p_newton(M, kmax):
    """Power sums from e_r = M_r by Newton's identities. Route A."""
    p = []
    for k in range(1, kmax + 1):
        s = 0.0
        for i in range(1, k):
            s += (-1) ** (i - 1) * M[i] * p[k - i - 1]
        s += (-1) ** (k - 1) * k * (M[k] if k < len(M) else 0.0)
        p.append(s)
    return p


def p_roots(M, kmax, m):
    """Power sums as sum y_i^k over the roots of the y-polynomial. Route B.

    F_A(x) = x^m - M_1 x^{m-2} + M_2 x^{m-4} - ..., so with y = x^2 the M_r are the elementary
    symmetric functions of the y-roots and the y-polynomial has coefficients (-1)^r M_r. This
    shares no code with route A.
    """
    coef = [((-1) ** r) * M[r] for r in range(len(M))]
    y = np.roots(coef)
    return [float(np.sum(y ** k).real) for k in range(1, kmax + 1)], y


def y_max_of(M, m):
    coef = [((-1) ** r) * M[r] for r in range(len(M))]
    y = np.roots(coef)
    ry = [t.real for t in y if abs(t.imag) < 1e-8 and t.real > 0]
    return max(ry) if ry else 0.0


def coordinate_family(m, a):
    """A random a-regular graph: unit weights on the edge planes give sum P_e = D = aI."""
    import networkx as nx
    try:
        G = nx.random_regular_graph(a, m, seed=int(rng.integers(1 << 30)))
    except Exception:
        return None
    frames = []
    for (u, v) in G.edges():
        B = np.zeros((m, 2)); B[u, 0] = 1.0; B[v, 1] = 1.0
        frames.append(B)
    return frames, np.ones(len(frames))


def general_family(m, q, a):
    """q random 2-planes, nonnegative weights solved by NNLS against aI, pruned to support."""
    frames = [np.linalg.qr(rng.standard_normal((m, 2)))[0] for _ in range(q)]
    iu = np.triu_indices(m)
    w = np.array([1.0 if i == j else math.sqrt(2.0) for i, j in zip(*iu)])
    A = np.stack([(B @ B.T)[iu] for B in frames], axis=1)
    c, _ = nnls(A * w[:, None], (a * np.eye(m))[iu] * w)
    keep = [k for k in range(len(c)) if c[k] > 1e-10]        # CONTROL 2: prune to support
    frames = [frames[k] for k in keep]
    c = c[keep]
    S = sum(ci * (B @ B.T) for ci, B in zip(c, frames))
    resid = float(np.abs(S - a * np.eye(m)).max())
    if resid > TOL_TIGHT:
        return None
    return frames, c, resid


def main():
    print(__doc__.split('\n\n')[1].strip() + '\n')
    print("Re-testing under three controls: two independent p_k routes, exact tightness,")
    print("and many samples per configuration.\n")

    t0 = time.time()
    configs = [('coordinate', 8, 3), ('coordinate', 10, 3), ('coordinate', 12, 3),
               ('general', 6, 3), ('general', 8, 3), ('general', 10, 3),
               ('coordinate', 8, 4), ('coordinate', 10, 4),
               ('general', 6, 4), ('general', 8, 4), ('general', 10, 4)]

    print(f"{'kind':>11}{'m':>4}{'a':>3}{'n':>4}{'|supp|':>7}{'resid':>9}"
          + "".join(f"{f'k={k}':>9}" for k in (1, 2, 3, 4, 5))
          + f"{'worst':>8}{'ymax/4a':>9}")

    worst_moment = 0.0
    worst_band = 0.0
    worst_witness = None
    disagreements = 0
    checked = 0

    for (kind, m, a) in quickmode.few(configs, 3):
        if time.time() - t0 > BUDGET_S:
            print("  [wall clock budget reached; remaining configurations skipped]")
            break
        W = tree_walks(a, m // 2)
        kk = min(5, m // 2)
        best = None
        nsamp = 0
        ntry = (4 if quickmode.QUICK else 40) if kind == 'general' else (3 if quickmode.QUICK else 12)
        for _ in range(ntry):
            if time.time() - t0 > BUDGET_S:
                break
            if kind == 'coordinate':
                fam = coordinate_family(m, a)
                if fam is None:
                    continue
                frames, c = fam
                resid = 0.0
            else:
                fam = general_family(m, 4 * m * (m + 1) // 2, a)
                if fam is None:
                    continue
                frames, c, resid = fam
            nsamp += 1
            M = elementary(frames, c, m)
            pA = p_newton(M, kk)                              # CONTROL 1: route A
            pB, _ = p_roots(M, kk, m)                         # CONTROL 1: route B
            checked += 1
            scale = max(1.0, max(abs(v) for v in pA))
            if max(abs(x - y) for x, y in zip(pA, pB)) / scale > TOL_AGREE:
                disagreements += 1
                continue
            rat = [pA[k - 1] / ((m / 2) * W[k - 1]) for k in range(1, kk + 1)]
            ymax = y_max_of(M, m)
            band = ymax / (4 * a)
            worst_band = max(worst_band, band)
            if best is None or max(rat) > max(best[0]):
                best = (rat, resid, len(frames), band)
        if best is None:
            print(f"{kind:>11}{m:>4}{a:>3}{nsamp:>4}   no admissible family")
            continue
        rat, resid, supp, band = best
        w = max(rat)
        if w > worst_moment:
            worst_moment = w
            worst_witness = (kind, m, a, w, band)
        print(f"{kind:>11}{m:>4}{a:>3}{nsamp:>4}{supp:>7}{resid:>9.1e}"
              + "".join(f"{(rat[k-1] if k <= len(rat) else float('nan')):>9.4f}"
                        for k in (1, 2, 3, 4, 5))
              + f"{w:>8.4f}{band:>9.4f}")

    print(f"\n  families checked: {checked}   route A / route B disagreements: {disagreements}")
    print(f"  worst p_k / ((m/2)W_2k): {worst_moment:.4f}", end='')
    if worst_witness:
        kind, m, a, w, band = worst_witness
        print(f"   (witness: {kind}, m={m}, a={a})")
    else:
        print()
    print(f"  worst y_max / (4a):      {worst_band:.4f}")
    print()
    if worst_moment > 1.0 + 1e-6:
        print("  P16 IS FALSE, confirmed under all three controls. The tree walk count is not")
        print("  an upper bound for the plane class, so it cannot serve as the a-priori input")
        print("  that removes the dimension restriction.")
    else:
        print("  No excess survives the controls. The earlier violation was an artefact.")
    if worst_band > 1.0:
        print("  AND THE BAND IS FALSE for the plane class.")
    else:
        print(f"  The band is untouched: every family stayed at {worst_band:.4f} of the")
        print("  threshold. Exceeding the tree moment bound is not the same as exceeding the")
        print("  band, the moment bound being sufficient and not necessary.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
