"""Where should projections beat graphs the most?

For p = 4 the whole question is the single free coefficient E_4, and on the
graph side E_4 = m(G,4) is pushed DOWN by having few 4-cycles.  When
q > C(p,b) the pigeonhole forces every biregular graph to repeat neighbourhoods,
i.e. to contain 4-cycles, while a projection family can 'smear'.  So the
q >> C(p,b) regime is where a projection family has the best chance of
beating every graph -- and of reaching the band edge.
"""
import sys
import numpy as np
from mcp2 import mcp, restore_proj, proj_from_X, rand_X
from mixed_char_poly import band
from p4_exact import all_graphs

CASES = [(4, 6, 3, 2), (4, 8, 4, 2), (4, 10, 5, 2), (4, 12, 6, 2), (4, 14, 7, 2),
         (5, 10, 4, 2), (5, 15, 6, 2), (6, 9, 3, 2), (6, 12, 4, 2)]


def opt_edge(p, q, a, b, rng, n_restart=10, n_step=400, eps0=0.6):
    """minimise mu(lo) over rank-b projections (== minimise E_p when p=4)."""
    lo, hi = band(a, b)
    best, bestc = 1e18, None
    for rs in range(n_restart):
        X = rand_X(q, p, b, rng)
        A, r = restore_proj(proj_from_X(X), q, p, a, b)
        if r > 1e-9:
            continue
        c = mcp(A)
        val = np.polyval(c, lo)
        eps, stall = eps0, 0
        for step in range(n_step):
            Y = X + eps * rand_X(q, p, b, rng)
            B, r2 = restore_proj(proj_from_X(Y), q, p, a, b)
            if r2 > 1e-9:
                continue
            c2 = mcp(B)
            v2 = np.polyval(c2, lo)
            if v2 < val - 1e-13:
                X, val, c = Y, v2, c2
                stall = 0
            else:
                stall += 1
                if stall > 18:
                    eps *= 0.6
                    stall = 0
                    if eps < 1e-7:
                        break
        if val < best:
            best, bestc = val, c
    return best, bestc


if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(CASES)))
    rng = np.random.default_rng(8888)
    for idx in sel:
        p, q, a, b = CASES[idx]
        lo, hi = band(a, b)
        line = f"p={p} q={q} (a,b)=({a},{b}) C(p,b)={int(__import__("math").comb(p,b))}"
        if p == 4:
            gl, subs = all_graphs(p, q, a, b)
            C = np.array([mcp(A) for _, A in gl])
            gmu = np.array([np.polyval(c, lo) for c in C])
            gE = C[:, p]
            line += (f"  | {len(gl)} graphs: E_4 in [{gE.min():.4f},{gE.max():.4f}], "
                     f"min mu(lo)={gmu.min():.6f}")
        v, c = opt_edge(p, q, a, b, rng)
        r = np.sort(np.roots(c).real)
        line += (f"\n     PROJ min mu(lo)={v:.6f}  E_4={c[p]:.6f}  "
                 f"r_min={r.min():.9f} (margin {r.min()-lo:+.9f})")
        if v < -1e-9:
            line += "  <<<<<< VIOLATION"
        print(line, flush=True)
