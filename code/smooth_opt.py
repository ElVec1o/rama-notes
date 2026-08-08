"""Smooth adversarial optimisation.

mu[A] is real-rooted with mu(0) = E_p >= 0.  Hence

    mu[A](lo) < 0   <=>   some root is < lo   (lower-band violation)
    mu[A](hi) < 0   <=>   some root is > hi   (upper-band violation)

so instead of the nonsmooth min/max root we minimise the SMOOTH functions
mu(lo) and mu(hi) over the family manifold, using L-BFGS on the free
parametrisation P_k = Q(X_k)Q(X_k)^T with a quadratic penalty for sum = aI.
The reported number is min mu(edge) / (normalising scale); negative == violation.
"""
import sys
import time
import numpy as np
from scipy.optimize import minimize
from mcp2 import mcp, restore_proj, proj_from_X, rand_X, psd_from_X
from mixed_char_poly import band
from tff import random_biregular, graph_to_projections


def poly_at(c, y):
    return float(np.polyval(c, y))


def make_obj(p, q, a, b, edge, pen, cls='RPROJ', sgn=1.0):
    """sgn must be (-1)^p at the LOWER edge (mu(y) = prod(y-r_i), so for
    y below every root the sign of mu is (-1)^p) and +1 at the UPPER edge."""
    I = np.eye(p)

    def f(x):
        X = x.reshape(q, p, b)
        if cls == 'RPROJ':
            Qm, _ = np.linalg.qr(X)
            P = Qm @ np.swapaxes(Qm, 1, 2)
            viol = np.linalg.norm(P.sum(axis=0) - a * I) ** 2
        else:                       # RPSD, full class, constraint automatic
            P = psd_from_X(X, a)
            viol = 0.0
        return sgn * poly_at(mcp(P), edge) + pen * viol
    return f


def run(p, q, a, b, edge, cls, rng, sgn=1.0, n_restart=6, maxiter=250,
        pens=(50., 400., 3000.)):
    best, bestx = 1e18, None
    for rs in range(n_restart):
        x = rand_X(q, p, b, rng).ravel()
        for pen in pens:
            f = make_obj(p, q, a, b, edge, pen, cls, sgn)
            r = minimize(f, x, method='L-BFGS-B',
                         options=dict(maxiter=maxiter, maxfun=200000))
            x = r.x
        # evaluate exactly on the manifold
        X = x.reshape(q, p, b)
        if cls == 'RPROJ':
            P, res = restore_proj(proj_from_X(X), q, p, a, b)
        else:
            P, res = psd_from_X(X, a), 0.0
        if res > 1e-9:
            continue
        v = sgn * poly_at(mcp(P), edge)
        if v < best:
            best, bestx = v, P.copy()
    return best, bestx


CASES = [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (4, 8, 4, 2), (5, 10, 4, 2),
         (6, 10, 5, 3), (8, 10, 5, 4), (9, 12, 4, 3)]

if __name__ == '__main__':
    sel = [int(x) for x in sys.argv[1:]] or list(range(len(CASES)))
    rng = np.random.default_rng(555)
    for idx in sel:
        p, q, a, b = CASES[idx]
        lo, hi = band(a, b)
        t0 = time.time()
        print("=" * 78)
        print(f"[{idx}] p={p} q={q} (a,b)=({a},{b})  band=[{lo:.8f},{hi:.8f}]", flush=True)
        slo = 1.0 if p % 2 == 0 else -1.0
        gl, gh = 1e18, 1e18
        for _ in range(300):
            adj = random_biregular(p, q, a, b, rng)
            if adj is None:
                continue
            c = mcp(graph_to_projections(adj, p, q))
            gl = min(gl, slo * poly_at(c, lo))
            gh = min(gh, poly_at(c, hi))
        print(f"   GRAPH : min mu(lo)={gl:.6f}   min mu(hi)={gh:.6f}", flush=True)
        for cls in ('RPROJ',):
            vl, _ = run(p, q, a, b, lo, cls, rng, slo)
            vh, _ = run(p, q, a, b, hi, cls, rng, 1.0)
            tag = '  <<<< VIOLATION' if min(vl, vh) < -1e-8 else ''
            print(f"   {cls} : min mu(lo)={vl:.9f}   min mu(hi)={vh:.9f}{tag}",
                  flush=True)
        print(f"   ({time.time()-t0:.0f}s)", flush=True)
