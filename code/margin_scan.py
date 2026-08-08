"""Does the quadratic suppression hold across a whole gap, or only at its middle?

G36 observed at one point per gap that the wrong-parity class contributes an integral of
order the square of its measure. G37 would turn that into an estimate. Before attempting
one, this scans a whole gap of spec(T) and reports, at each x,

    m_wrong  the measure of the parity class disagreeing with delta,
    I_wrong  the integral of |det S(x,z)| over it,
    I_right  the same over the class agreeing with delta,
    ratio    I_wrong / m_wrong^2, which G37 asserts is bounded,
    margin   (I_right - I_wrong) / (I_right + I_wrong), which must stay positive.

The gap edges are where an estimate is most likely to fail: approaching them, the universal
cover is about to acquire spectrum, delta is about to change, and the wrong-parity class
grows. If the ratio blows up there, G37 is false as stated and needs a different exponent.

delta is taken from the cavity solver as kappa - N_F. Near a gap edge kappa is least
reliable, so rows where kappa is further than 0.25 from an integer are marked rather than
silently used.
"""

import sys
import math
import cmath
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

GRAPHS = {
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (0, 3)),
    'theta': (5, [(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4)], (0, 4)),
}


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    for name, (n, edges, W) in GRAPHS.items():
        nF, eF = delete(n, edges, set(W))
        cF = matching_coeffs(nF, eF)
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        steps = 40
        grid = [2 * math.pi * k / steps for k in range(steps)]

        R = 5.0
        got = None
        for eta in (1e-6, 1e-4, 1e-3, 1e-2):
            es, ds, bad = scan(n, edges, -R, R, 3000, eta=eta)
            if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.02:
                got = (es, ds)
                break
        if got is None:
            print(f"{name}: solver gated"); continue
        es, ds = got
        bs = bands(es, ds, 1e-3)

        # the internal gaps, i.e. those with a band on both sides
        internal = []
        for i in range(len(bs) - 1):
            lo, hi = bs[i][1], bs[i + 1][0]
            if hi - lo > 0.06:
                internal.append((lo, hi))
        if not internal:
            print(f"\n{name}: no internal gap"); continue

        for lo, hi in internal:
            print(f"\n{name}  internal gap ({lo:.4f}, {hi:.4f})  b={b}")
            print(f"{'x':>9}{'delta':>6}{'m_wrong':>10}{'I_wrong':>11}"
                  f"{'I_right':>11}{'ratio':>10}{'margin':>9}  note")
            for frac in (0.06, 0.15, 0.3, 0.5, 0.7, 0.85, 0.94):
                x = lo + frac * (hi - lo)
                k = kappa_above(es, ds, n, x)
                NF = roots_above(cF, x)
                delta = round(k) - NF
                note = "" if abs(k - round(k)) <= 0.25 else "kappa unreliable"
                tot = steps ** b
                cnt = [0, 0, 0]
                I = [0.0, 0.0, 0.0]
                for t in range(tot):
                    th, r = [], t
                    for _ in range(b):
                        th.append(grid[r % steps]); r //= steps
                    S = schur_2x2(magnetic(n, edges, cot, th), x, list(W))
                    S = 0.5 * (S + S.conj().T)
                    w = np.linalg.eigvalsh(S)
                    j = int(np.sum(w < 0))
                    d = abs(np.real(np.linalg.det(S)))
                    if 0 <= j <= 2:
                        cnt[j] += 1
                        I[j] += d
                m = [c / tot for c in cnt]
                I = [v / tot for v in I]
                if delta % 2 == 1:
                    mr, Ir, Iw = m[1], I[1], I[0] + I[2]
                    mw = m[0] + m[2]
                else:
                    mr, Ir, Iw = m[0] + m[2], I[0] + I[2], I[1]
                    mw = m[1]
                ratio = Iw / mw ** 2 if mw > 1e-12 else 0.0
                margin = (Ir - Iw) / max(Ir + Iw, 1e-300)
                print(f"{x:>9.4f}{delta:>6}{mw:>10.4f}{Iw:>11.5f}"
                      f"{Ir:>11.5f}{ratio:>10.3f}{margin:>9.4f}  {note}")
    print("\nG37 asserts the ratio column is bounded. A blow-up near a gap edge would")
    print("mean the exponent 2 is wrong there and the estimate needs restating.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
