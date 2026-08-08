"""Does allowing COMPLEX Hermitian rank-b projections (a strictly larger
manifold) get below the real projection optimum?  Tested on the p=4 cases,
where the whole question is the single free coefficient E_4."""
import sys
import numpy as np
from mcp2 import mcp, restore_proj, proj_from_X, rand_X
from mixed_char_poly import band
from p4_exact import all_graphs

CASES = [(4, 6, 3, 2), (4, 8, 4, 2), (4, 10, 5, 2), (4, 12, 6, 2)]


def opt(p, q, a, b, rng, cx, n_restart=12, n_step=500, eps0=0.6):
    best, bc = 1e18, None
    for rs in range(n_restart):
        X = rand_X(q, p, b, rng, cx)
        A, r = restore_proj(proj_from_X(X), q, p, a, b)
        if r > 1e-9:
            continue
        c = mcp(A)
        val = c[p]
        eps, stall = eps0, 0
        for step in range(n_step):
            Y = X + eps * rand_X(q, p, b, rng, cx)
            B, r2 = restore_proj(proj_from_X(Y), q, p, a, b)
            if r2 > 1e-9:
                continue
            c2 = mcp(B)
            if c2[p] < val - 1e-13:
                X, val, c = Y, c2[p], c2
                stall = 0
            else:
                stall += 1
                if stall > 18:
                    eps *= 0.6
                    stall = 0
                    if eps < 1e-7:
                        break
        if val < best:
            best, bc = val, c
    return best, bc


if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(CASES)))
    rng = np.random.default_rng(31)
    for idx in sel:
        p, q, a, b = CASES[idx]
        lo, hi = band(a, b)
        gl, _ = all_graphs(p, q, a, b)
        gE = np.array([mcp(A)[p] for _, A in gl])
        f = np.poly1d(np.concatenate([mcp(gl[0][1])[:p], [0.0]]))
        thr = -f(lo)
        out = [f"p={p} q={q} (a,b)=({a},{b})  graph min E_4={gE.min():.6f}  "
               f"violation needs E_4 < {thr:.6f}"]
        for cx, nm in ((False, 'REAL '), (True, 'CPLX ')):
            v, c = opt(p, q, a, b, rng, cx)
            r = np.sort(np.roots(c).real)
            out.append(f"   {nm}projections: min E_4={v:.8f}  r_min={r.min():.9f} "
                       f"(margin {r.min()-lo:+.9f})  r_max={r.max():.9f} "
                       f"(margin {hi-r.max():+.9f})")
        print("\n".join(out), flush=True)
