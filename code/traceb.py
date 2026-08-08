"""The intermediate class TRACEB:
      A_k PSD, rank(A_k) <= b, tr(A_k) = b, sum_k A_k = a I.
Projections are exactly the members with A_k^2 = A_k.  Does the tree band
survive when idempotency is dropped but the trace is kept?

Also: exact range of the single free coefficient E_4 when p = 4
(E_0..E_3 are universal for projections)."""
import sys
import numpy as np
from mcp2 import mcp, roots
from mixed_char_poly import band
from tff import random_biregular, graph_to_projections


def simplex_proj(v, s):
    """Euclidean projection of v onto {d >= 0, sum d = s}."""
    u = np.sort(v)[::-1]
    css = np.cumsum(u) - s
    ind = np.arange(1, len(v) + 1)
    cond = u - css / ind > 0
    rho = ind[cond][-1]
    theta = css[rho - 1] / rho
    return np.maximum(v - theta, 0.0)


def proj_traceb(A, b):
    """Batched projection onto {PSD, rank<=b, trace=b} (approximate: keep top-b
    eigenvalues then simplex-project them)."""
    A = 0.5 * (A + np.swapaxes(A, 1, 2))
    w, V = np.linalg.eigh(A)
    q, p, _ = A.shape
    U = V[:, :, -b:]
    d = w[:, -b:]
    out = np.empty_like(A)
    for k in range(q):
        dk = simplex_proj(d[k], b)
        out[k] = (U[k] * dk) @ U[k].T
    return out


def restore_traceb(A, q, p, a, b, iters=1500, tol=1e-13):
    I = np.eye(p)
    for it in range(iters):
        A = proj_traceb(A + (a * I - A.sum(axis=0)) / q, b)
        if it % 50 == 49 and res_traceb(A, a, b) < tol:
            break
    return A, res_traceb(A, a, b)


def res_traceb(A, a, b):
    p = A.shape[1]
    r1 = np.linalg.norm(A.sum(axis=0) - a * np.eye(p))
    tr = np.trace(A, axis1=1, axis2=2)
    r2 = np.max(np.abs(tr - b))
    w = np.linalg.eigvalsh(A)
    r3 = max(0.0, -w.min())
    r4 = np.max(np.abs(w[:, :A.shape[1] - b])) if A.shape[1] > b else 0.0
    return max(r1, r2, r3, r4)


def rand_traceb(p, q, a, b, rng):
    X = rng.standard_normal((q, p, b))
    A = X @ np.swapaxes(X, 1, 2)
    return restore_traceb(A, q, p, a, b)


def search_traceb(p, q, a, b, rng, mode, n_restart=8, n_step=350, eps0=0.5):
    best, bestA = 1e18, None
    for rs in range(n_restart):
        A, r = rand_traceb(p, q, a, b, rng)
        if r > 1e-8:
            continue
        rt = roots(A)
        val = rt.min() if mode == 'lo' else -rt.max()
        eps, stall = eps0, 0
        for step in range(n_step):
            B = A + eps * np.array([rng.standard_normal((p, p)) for _ in range(q)])
            B = 0.5 * (B + np.swapaxes(B, 1, 2))
            B, r2 = restore_traceb(B, q, p, a, b, iters=800)
            if r2 > 1e-8:
                stall += 1
                continue
            rt = roots(B)
            v2 = rt.min() if mode == 'lo' else -rt.max()
            if v2 < val - 1e-13:
                A, val = B, v2
                stall = 0
            else:
                stall += 1
                if stall > 18:
                    eps *= 0.62
                    stall = 0
                    if eps < 1e-6:
                        break
        if val < best:
            best, bestA = val, A.copy()
    return best, bestA


PARAMS = [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (4, 8, 4, 2), (6, 10, 5, 3)]

if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(PARAMS)))
    rng = np.random.default_rng(777)
    for idx in sel:
        p, q, a, b = PARAMS[idx]
        lo, hi = band(a, b)
        print("=" * 78)
        print(f"[{idx}] TRACEB p={p} q={q} (a,b)=({a},{b})  band=[{lo:.8f},{hi:.8f}]",
              flush=True)
        gmin, gmax = 1e9, -1e9
        for _ in range(300):
            adj = random_biregular(p, q, a, b, rng)
            if adj is None:
                continue
            r = roots(graph_to_projections(adj, p, q))
            gmin, gmax = min(gmin, r.min()), max(gmax, r.max())
        print(f"   GRAPH : r_min={gmin:.9f} margin {gmin-lo:+.9f} | "
              f"r_max={gmax:.9f} margin {hi-gmax:+.9f}", flush=True)
        vlo, Alo = search_traceb(p, q, a, b, rng, 'lo')
        vhi, Ahi = search_traceb(p, q, a, b, rng, 'hi')
        flag = '   <<<<<< VIOLATION' if (vlo < lo - 1e-9 or -vhi > hi + 1e-9) else ''
        print(f"   TRACEB: r_min={vlo:.9f} margin {vlo-lo:+.9f} | "
              f"r_max={-vhi:.9f} margin {hi+vhi:+.9f}{flag}", flush=True)
        # how far from idempotent are the optimisers?
        for nm, A in (('lo', Alo), ('hi', Ahi)):
            if A is None:
                continue
            w = np.sort(np.linalg.eigvalsh(A)[:, -b:], axis=1)
            print(f"      {nm}-optimum: nonzero eigenvalues of A_k range "
                  f"[{w.min():.4f},{w.max():.4f}]  (1.0 == projection); "
                  f"||A^2-A||_max={np.max(np.abs(A@A-A)):.3e}", flush=True)
