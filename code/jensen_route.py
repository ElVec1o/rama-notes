"""Is there a non-circular lower bound on the right-parity integral?

Two things are checked here.

FIRST, that the obvious route is circular. The decomposition is
mu_G/mu_F = I_0 - I_1 + I_2, so I_right - I_wrong equals |mu_G/mu_F| identically. Bounding
I_right below by |mu_G/mu_F| therefore assumes exactly what the domination criterion is
trying to establish, and no independent lower bound on |mu_G(x)| is available inside a gap:
Heilmann-Lieb gives root-free intervals only outside [-rho, rho], which is the easy region.
The script verifies the identity numerically as a check on the bookkeeping.

SECOND, a substitute that is not circular. Jensen (equivalently AM-GM for integrals) gives

    I_total = integral |det S| dz  >=  exp( integral log|det S| dz )  =:  Delta,

the geometric mean, which is a spectral quantity of the abelian cover and owes nothing to
the sign of mu_G. Since I_total = I_right + I_wrong and the upper half already gives
I_wrong <= C m^{3/2} unconditionally,

    I_right >= Delta - C m^{3/2},   so domination holds as soon as Delta > 2 C m^{3/2}.

The geometric mean was named in G29 as the source of the obstruction. It reappears here as
the tool. The script measures Delta against I_wrong across a gap and reports the ratio
Delta / (2 I_wrong), which must exceed 1 for the route to close.
"""

import sys
import math
import cmath
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

GRAPHS = {
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (0, 3)),
}
STEPS = 64


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    for name, (n, edges, W) in GRAPHS.items():
        nF, eF = delete(n, edges, set(W))
        cF = matching_coeffs(nF, eF)
        cG = matching_coeffs(n, edges)
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        grid = [2 * math.pi * k / STEPS for k in range(STEPS)]

        R = 5.0
        got = None
        for eta in (1e-6, 1e-4, 1e-3, 1e-2):
            es, ds, bad = scan(n, edges, -R, R, 3000, eta=eta)
            if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.02:
                got = (es, ds); break
        if got is None:
            print(f"{name}: gated"); continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.06]

        for lo, hi in internal:
            print(f"\n{name}  gap ({lo:.4f}, {hi:.4f})  grid {STEPS}^{b}")
            print(f"{'x':>9}{'I_wrong':>10}{'I_right':>10}{'mu_G/mu_F':>12}"
                  f"{'identity':>10}{'Delta':>10}{'D/2Iw':>9}")
            for frac in (0.08, 0.25, 0.5, 0.75, 0.92):
                x = lo + frac * (hi - lo)
                k = kappa_above(es, ds, n, x)
                delta = round(k) - roots_above(cF, x)
                tot = STEPS ** b
                I = [0.0, 0.0, 0.0]
                logsum = 0.0
                for t in range(tot):
                    th, r = [], t
                    for _ in range(b):
                        th.append(grid[r % STEPS]); r //= STEPS
                    S = schur_2x2(magnetic(n, edges, cot, th), x, list(W))
                    S = 0.5 * (S + S.conj().T)
                    w = np.linalg.eigvalsh(S)
                    d = np.real(np.linalg.det(S))
                    I[int(np.sum(w < 0))] += abs(d)
                    logsum += math.log(max(abs(d), 1e-300))
                I = [v / tot for v in I]
                if delta % 2 == 1:
                    Ir, Iw = I[1], I[0] + I[2]
                else:
                    Ir, Iw = I[0] + I[2], I[1]
                Delta = math.exp(logsum / tot)
                # mu_G/mu_F evaluated directly from the matching polynomials
                def ev(c, t):
                    a = 0.0
                    for j in range(len(c) - 1, -1, -1):
                        a = a * t + c[j]
                    return a
                q = ev(cG, x) / ev(cF, x)
                ident = abs(abs(q) - (Ir - Iw))
                print(f"{x:>9.4f}{Iw:>10.5f}{Ir:>10.5f}{q:>12.5f}"
                      f"{ident:>10.2e}{Delta:>10.5f}{Delta / (2 * Iw):>9.2f}")
    print("\nidentity is | |mu_G/mu_F| - (I_right - I_wrong) |, which must be zero:")
    print("that is why bounding I_right by |mu_G/mu_F| is circular.")
    print("D/2Iw is the Jensen route's margin and must exceed 1 for it to close.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
