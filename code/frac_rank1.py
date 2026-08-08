"""Class (D) at its extreme: A_k = b v_k v_k^T, {v_k} a unit-norm tight frame
in R^p with sum_k v_k v_k^T = (a/b) I.

These satisfy EVERY hypothesis the MSS barrier method uses --
   A_k PSD,  rank(A_k) <= b,  tr A_k = b,  sum_k A_k = a I
-- and are maximally far from idempotent (eigenvalues (b,0,...,0) instead of
(1,..,1,0,..,0)).  In Naimark language they are the rank-p projections Pi with
constant diagonal 1/a whose diagonal b x b blocks are (1/a) J_b instead of
(1/a) I_b: the block condition fails as badly as possible.

If the tree band fails here, then no theorem with those hypotheses -- in
particular nothing the barrier method can prove -- implies the tree band.
"""
import sys
import numpy as np
from mcp2 import mcp
from mixed_char_poly import band


def tight_frame(p, q, rng, iters=4000):
    """q unit vectors in R^p with sum v_k v_k^T = (q/p) I  (Parseval up to
    scale).  Alternating projections: normalise rows, then whiten."""
    V = rng.standard_normal((q, p))
    for _ in range(iters):
        V /= np.linalg.norm(V, axis=1, keepdims=True)
        S = V.T @ V
        w, U = np.linalg.eigh(S)
        V = V @ (U * (w ** -0.5)) @ U.T * np.sqrt(q / p)
    V /= np.linalg.norm(V, axis=1, keepdims=True)
    return V


def frame_resid(V, p, q):
    S = V.T @ V
    return max(np.abs(np.linalg.norm(V, axis=1) - 1).max(),
               np.abs(S - (q / p) * np.eye(p)).max())


def harmonic_frame(p, q):
    """deterministic unit-norm tight frame: rows of a q x p real 'harmonic'
    matrix (works for even p)."""
    assert p % 2 == 0
    V = np.zeros((q, p))
    for k in range(q):
        for m in range(p // 2):
            ang = 2 * np.pi * (m + 1) * k / q
            V[k, 2 * m] = np.cos(ang)
            V[k, 2 * m + 1] = np.sin(ang)
    V /= np.linalg.norm(V, axis=1, keepdims=True)
    return V


def run(p, q, a, b, rng, ntry=40):
    lo, hi = band(a, b)
    assert p * a == q * b
    best_lo, best_hi, wim = np.inf, np.inf, 0.0
    rows = []
    cands = [('harmonic', harmonic_frame(p, q))] if p % 2 == 0 else []
    for _ in range(ntry):
        cands.append(('random', tight_frame(p, q, rng)))
    for name, V in cands:
        res = frame_resid(V, p, q)
        if res > 1e-8:
            continue
        A = b * np.einsum('ki,kj->kij', V, V)
        assert np.abs(A.sum(0) - a * np.eye(p)).max() < 1e-8, np.abs(A.sum(0) - a * np.eye(p)).max()
        c = mcp(A)
        r = np.roots(c)
        wim = max(wim, np.abs(r.imag).max())
        rr = np.sort(r.real)
        best_lo = min(best_lo, rr.min() - lo)
        best_hi = min(best_hi, hi - rr.max())
        rows.append((name, rr))
    print(f"  p={p} q={q} (a,b)=({a},{b})  tree band [{lo:.6f}, {hi:.6f}]  "
          f"MP band [{(np.sqrt(a)-np.sqrt(b))**2:.4f}, {(np.sqrt(a)+np.sqrt(b))**2:.4f}]")
    print(f"      worst lower margin {best_lo:+.6f}   worst upper margin "
          f"{best_hi:+.6f}   max|Im| {wim:.1e}   "
          f"{'*** VIOLATION ***' if min(best_lo, best_hi) < -1e-9 else 'inside'}")
    for name, rr in rows[:2]:
        print(f"      {name:9s} roots {np.array2string(rr, precision=5)}")
    sys.stdout.flush()


if __name__ == '__main__':
    rng = np.random.default_rng(31415)
    print("class (D) extreme point: A_k = b v_k v_k^T, unit-norm tight frame")
    for (p, q, a, b) in [(4, 6, 3, 2), (3, 6, 4, 2), (4, 8, 4, 2), (6, 9, 3, 2),
                         (6, 8, 4, 3), (2, 7, 7, 2), (4, 14, 7, 2), (5, 10, 4, 2)]:
        run(p, q, a, b, rng)
