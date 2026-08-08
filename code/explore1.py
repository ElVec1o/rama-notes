"""First exploration: random tight fusion frames vs the tree band."""
import numpy as np
from mixed_char_poly import mixed_char_poly, band, roots_of
from tff import build_tff, build_psd_family, random_biregular, graph_to_projections

PARAMS = [
    (4, 6, 3, 2),
    (3, 6, 4, 2),
    (6, 9, 3, 2),
    (6, 8, 4, 3),
    (4, 8, 4, 2),
]

rng = np.random.default_rng(2024)
for (p, q, a, b) in PARAMS:
    lo, hi = band(a, b)
    print("=" * 74)
    print(f"p={p} q={q} (a,b)=({a},{b})   band = [{lo:.6f}, {hi:.6f}]  "
          f"(MP band = [{(np.sqrt(a)-np.sqrt(b))**2:.4f}, {(np.sqrt(a)+np.sqrt(b))**2:.4f}])")
    # --- diagonal / graph reference
    best_g = None
    for _ in range(60):
        adj = random_biregular(p, q, a, b, rng)
        if adj is None:
            continue
        Ps = graph_to_projections(adj, p, q)
        c = mixed_char_poly(Ps)
        r, im = roots_of(c)
        if best_g is None or r.min() < best_g[0]:
            best_g = (r.min(), r.max(), im)
    if best_g:
        print(f"  graphs   : min r_min = {best_g[0]:.6f}  (margin_lo {best_g[0]-lo:+.6f}), "
              f"r_max = {best_g[1]:.6f} (margin_hi {hi-best_g[1]:+.6f})")

    # --- projections
    worst_lo, worst_hi, maxim, badres = 1e9, 1e9, 0.0, 0.0
    nfail = 0
    for trial in range(40):
        As, res = build_tff(p, q, a, b, rng)
        if res > 1e-10:
            nfail += 1
            continue
        badres = max(badres, res)
        c = mixed_char_poly(As)
        r, im = roots_of(c)
        maxim = max(maxim, im)
        worst_lo = min(worst_lo, r.min() - lo)
        worst_hi = min(worst_hi, hi - r.max())
    print(f"  projections: {40-nfail} feasible (max residual {badres:.2e}) "
          f"worst margin_lo = {worst_lo:+.6f}   worst margin_hi = {worst_hi:+.6f}  "
          f"max|Im root| = {maxim:.2e}")

    # --- general PSD rank b
    worst_lo, worst_hi, maxim = 1e9, 1e9, 0.0
    for trial in range(40):
        As = build_psd_family(p, q, a, b, rng)
        c = mixed_char_poly(As)
        r, im = roots_of(c)
        maxim = max(maxim, im)
        worst_lo = min(worst_lo, r.min() - lo)
        worst_hi = min(worst_hi, hi - r.max())
    print(f"  PSD rank-b : worst margin_lo = {worst_lo:+.6f}   "
          f"worst margin_hi = {worst_hi:+.6f}  max|Im root| = {maxim:.2e}")
