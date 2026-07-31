"""Which coefficients of mu[A_1..A_q] are FORCED by (p,q,a,b) alone?

mu(y) = sum_m (-1)^m E_m y^(p-m).  For rank-b orthogonal projections with
sum A_k = aI, idempotency collapses every trace of a word in the A_k that has
a repeated letter, so E_0..E_3 should be universal and E_4 the first free one.
This script measures the observed spread of each E_m."""
import numpy as np
from mixed_char_poly import mixed_char_poly
from tff import build_tff, build_psd_family, random_biregular, graph_to_projections

PARAMS = [(4, 6, 3, 2), (3, 6, 4, 2), (6, 9, 3, 2), (6, 8, 4, 3), (4, 8, 4, 2),
          (5, 10, 4, 2), (6, 10, 5, 3)]
rng = np.random.default_rng(99)
for (p, q, a, b) in PARAMS:
    Cs, Cg, Cpsd = [], [], []
    for _ in range(25):
        A, res = build_tff(p, q, a, b, rng)
        if res < 1e-10:
            Cs.append(mixed_char_poly(A))
        Cpsd.append(mixed_char_poly(build_psd_family(p, q, a, b, rng)))
    for _ in range(25):
        adj = random_biregular(p, q, a, b, rng)
        if adj is not None:
            Cg.append(mixed_char_poly(graph_to_projections(adj, p, q)))
    Cs, Cg, Cpsd = np.array(Cs), np.array(Cg), np.array(Cpsd)
    print(f"p={p} q={q} (a,b)=({a},{b})   [{len(Cs)} proj fams, {len(Cg)} graphs, "
          f"{len(Cpsd)} psd fams]")
    for m in range(p + 1):
        sp_ = np.ptp(Cs[:, m]) if len(Cs) else np.nan
        gp = np.ptp(Cg[:, m]) if len(Cg) else np.nan
        pp = np.ptp(Cpsd[:, m])
        print(f"   E_{m}: mean_proj={abs(Cs[:,m]).mean():14.6f}  "
              f"spread_proj={sp_:.3e}  spread_graph={gp:.3e}  spread_psd={pp:.3e}")
    print()
