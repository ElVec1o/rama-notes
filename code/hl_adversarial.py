r"""hl_adversarial.py -- REGRESSION: try to break the ceiling 2 sqrt(a).

Hill-climb over plane families in P(a) with Adj = a I exactly, maximising the
largest root of F.  The claim under test is that 2 sqrt(a) is an upper bound that
is approached only in the weighted-K_m limit; the search must never exceed it.
"""
import sys
import numpy as np
import hl_planes as H


def build(Zs, m, a):
    """orthonormalise the planes, then solve for weights with sum c_k P_k = a I.
    Returns blocks or None if some weight is negative."""
    idx = [(i, j) for i in range(m) for j in range(i, m)]
    b = np.array([a if i == j else 0.0 for (i, j) in idx])
    Us = []
    for Z in Zs:
        Qz, _ = np.linalg.qr(Z)
        Us.append(Qz)
    q = len(Us)
    A = np.zeros((len(idx), q))
    for k in range(q):
        P = Us[k] @ Us[k].T
        for t, (i, j) in enumerate(idx):
            A[t, k] = P[i, j] * (1.0 if i == j else np.sqrt(2.0))
    c0 = np.full(q, a * m / (2.0 * q))
    dc, *_ = np.linalg.lstsq(A, b - A @ c0, rcond=None)
    c = c0 + dc
    if c.min() <= 1e-9 or np.abs(A @ c - b).max() > 1e-8:
        return None
    return [Us[k] * c[k] ** 0.25 for k in range(q)]


def maxroot(Bs, m):
    F = H.F_dense(Bs, m)
    return float(np.abs(np.roots(F)).max())


def hill(m, a, q, iters=400, seed=0, step0=0.6):
    rng = np.random.default_rng(seed)
    Zs = None
    for _ in range(400):
        cand = [rng.standard_normal((m, 2)) for _ in range(q)]
        if build(cand, m, a) is not None:
            Zs = cand
            break
    if Zs is None:
        return None, None
    cur = maxroot(build(Zs, m, a), m)
    step = step0
    for it in range(iters):
        k = int(rng.integers(q))
        Z2 = [Z.copy() for Z in Zs]
        Z2[k] = Z2[k] + step * rng.standard_normal((m, 2))
        Bs = build(Z2, m, a)
        if Bs is None:
            continue
        v = maxroot(Bs, m)
        if v > cur:
            cur, Zs = v, Z2
        if (it + 1) % 120 == 0:
            step *= 0.6
    return cur, Zs


if __name__ == '__main__':
    print("=" * 100)
    print("ADVERSARIAL search for a family in P(a) with max root > 2 sqrt(a)")
    print("=" * 100)
    for (m, a) in [(4, 3), (5, 3), (6, 3), (6, 2), (4, 6), (6, 5)]:
        base = m * (m + 1) // 2
        best = -np.inf
        for q, sd in [(base, 1), (base, 2), (2 * base, 3), (m * a // 2 if (m * a) % 2 == 0 else base, 4)]:
            v, _ = hill(m, a, q, iters=300, seed=sd)
            if v is not None:
                best = max(best, v)
        # weighted K_m reference (commuting, the known extremiser)
        lam = a / (m - 1)
        wk = maxroot(H.graph_blocks(H.Kn_edges(m), m, [lam] * (m * (m - 1) // 2)), m)
        print(f"  m={m:2d} a={a:4.1f}  best found = {best:9.5f}   "
              f"weighted K_m = {wk:9.5f}   2 sqrt(a) = {2*np.sqrt(a):9.5f}   "
              f"{'OK (ceiling holds)' if best <= 2*np.sqrt(a) + 1e-8 else '*** CEILING BROKEN ***'}")
        sys.stdout.flush()
