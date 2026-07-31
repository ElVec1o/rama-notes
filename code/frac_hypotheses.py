"""Which of {PSD, rank<=b, tr=b, sum=aI, idempotent} is load-bearing for the
TREE band [(s-t)^2,(s+t)^2] (as opposed to the Marchenko-Pastur band
[(sqrt a - sqrt b)^2,(sqrt a + sqrt b)^2] that the MSS barrier method gives)?

Classes tested, all with sum_k A_k = a I and A_k PSD:
   PROJ    rank-b orthogonal projections           (= conjecture X)
   TRACEB  rank <= b, tr = b                       (idempotency dropped)
   RANK1   A_k = b v_k v_k^T, tight frame          (extreme point of TRACEB)
   TRB     tr = b, rank FREE                       (rank bound dropped too)
   SCALAR  A_k = (b/p) I_p                         (extreme point of TRB)
"""
import sys
import numpy as np
from mcp2 import mcp, restore_proj, proj_from_X, rand_X
from mixed_char_poly import band
from traceb import restore_traceb, res_traceb


def mp_band(a, b):
    return (np.sqrt(a) - np.sqrt(b)) ** 2, (np.sqrt(a) + np.sqrt(b)) ** 2


def scalar_family(p, q, a, b):
    return np.array([(b / p) * np.eye(p) for _ in range(q)])


def proj_trb(A, b, a):
    """PSD with trace b (rank free), then rebalance the sum."""
    A = 0.5 * (A + np.swapaxes(A, 1, 2))
    w, V = np.linalg.eigh(A)
    w = np.clip(w, 0.0, None)
    s = w.sum(axis=1, keepdims=True)
    w = w * (b / np.maximum(s, 1e-300))
    return (V * w[:, None, :]) @ np.swapaxes(V, 1, 2)


def restore_trb(A, q, p, a, b, iters=1200, tol=1e-13):
    I = np.eye(p)
    for it in range(iters):
        A = proj_trb(A + (a * I - A.sum(axis=0)) / q, b, a)
        if it % 50 == 49:
            r = res_trb(A, a, b)
            if r < tol:
                break
    return A, res_trb(A, a, b)


def res_trb(A, a, b):
    p = A.shape[1]
    r1 = np.linalg.norm(A.sum(axis=0) - a * np.eye(p))
    r2 = np.max(np.abs(np.trace(A, axis1=1, axis2=2) - b))
    r3 = max(0.0, -np.linalg.eigvalsh(A).min())
    return max(r1, r2, r3)


def search(p, q, a, b, rng, kind, mode, n_restart=6, n_step=250, eps0=0.5):
    lo, hi = band(a, b)
    best, bestA = 1e18, None
    for rs in range(n_restart):
        X = rand_X(q, p, b, rng)
        if kind == 'TRB':
            A0 = X @ np.swapaxes(X, 1, 2)
            A, r = restore_trb(A0, q, p, a, b)
        else:
            A, r = restore_proj(proj_from_X(X), q, p, a, b)
        if r > 1e-8:
            continue
        rt = np.sort(np.roots(mcp(A)).real)
        val = rt.min() if mode == 'lo' else -rt.max()
        eps, stall = eps0, 0
        for step in range(n_step):
            H = rng.standard_normal((q, p, p))
            B = A + eps * 0.5 * (H + np.swapaxes(H, 1, 2))
            if kind == 'TRB':
                B, r2 = restore_trb(B, q, p, a, b, iters=600)
            else:
                B, r2 = restore_proj(B, q, p, a, b)
            if r2 > 1e-8:
                stall += 1
                continue
            rt = np.sort(np.roots(mcp(B)).real)
            v2 = rt.min() if mode == 'lo' else -rt.max()
            if v2 < val - 1e-13:
                A, val = B, v2
                stall = 0
            else:
                stall += 1
                if stall > 15:
                    eps *= 0.6
                    stall = 0
                    if eps < 1e-7:
                        break
        if val < best:
            best, bestA = val, A.copy()
    return best, bestA


if __name__ == '__main__':
    rng = np.random.default_rng(2718)
    CASES = [(4, 6, 3, 2), (3, 6, 4, 2), (4, 8, 4, 2), (6, 8, 4, 3)]
    for (p, q, a, b) in CASES:
        lo, hi = band(a, b)
        mlo, mhi = mp_band(a, b)
        print("=" * 78)
        print(f"p={p} q={q} (a,b)=({a},{b})   tree band [{lo:.6f},{hi:.6f}]   "
              f"MP band [{mlo:.6f},{mhi:.6f}]")
        # SCALAR extreme of TRB
        A = scalar_family(p, q, a, b)
        r = np.sort(np.roots(mcp(A)).real)
        print(f"  SCALAR A_k=(b/p)I : roots {np.array2string(r, precision=5)}")
        print(f"                      tree-band margins lo {r.min()-lo:+.6f} "
              f"hi {hi-r.max():+.6f}   MP margins lo {r.min()-mlo:+.6f} "
              f"hi {mhi-r.max():+.6f}"
              f"   {'*** TREE BAND VIOLATED ***' if (r.min()<lo-1e-9 or r.max()>hi+1e-9) else ''}")
        # adversarial over TRB (trace b, rank free)
        vlo, _ = search(p, q, a, b, rng, 'TRB', 'lo')
        vhi, _ = search(p, q, a, b, rng, 'TRB', 'hi')
        print(f"  TRB (tr=b, rank free)  r_min {vlo:.6f} (tree margin "
              f"{vlo-lo:+.6f})   r_max {-vhi:.6f} (tree margin {hi+vhi:+.6f})"
              f"   {'*** TREE BAND VIOLATED ***' if (vlo<lo-1e-9 or -vhi>hi+1e-9) else ''}")
        sys.stdout.flush()
