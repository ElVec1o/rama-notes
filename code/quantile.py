"""Settling the exponent: the analytic quantile prediction, which needs no density estimate.

The tension. A derivation says the exponent is -2/3 universally, because the biregular tree's
spectral density vanishes like sqrt(x-g) at the inner edge. The measurement says -2/3 at
q = 2d but about -0.62 for q >= 3d. An attempt to arbitrate by estimating the density from the
roots failed, and failed circularly: each graph has only about r positive roots, so a window
narrow enough to probe the edge holds about one root, which IS the margin.

The way out is to use the density we can WRITE DOWN rather than one estimated from the same
data. The predicted margin is the quantile

    delta_pred  solving   n * integral from g to g+delta of rho  =  1,

that is, the point at which the expected root count reaches one. No fitting, no estimation, no
circularity. Comparing delta_pred with the measured margin then answers the question directly:

  * if delta_pred reproduces the measured exponents INCLUDING their aspect-ratio dependence,
    then that dependence is a finite-size effect of integrating over a window that is not yet
    in the pure square-root regime, the families with q >= 3d are pre-asymptotic, and the true
    exponent is the universal -2/3;
  * if delta_pred has exponent -2/3 in every family while the measurement does not, then the
    soft-edge quantile is not what sets the scale and the whole reading is wrong.

THE DENSITY, derived rather than recalled. On the (d,q)-biregular tree write A1 = d-1,
B1 = q-1. The cavity resolvents X (from a d-vertex) and Y (from a q-vertex) satisfy
X = 1/(z - A1 Y) and Y = 1/(z - B1 X), so their product P = XY satisfies

    A1 B1 P^2 + (A1 + B1 - z^2) P + 1 = 0,

whose discriminant (z^2 - A1 - B1)^2 - 4 A1 B1 vanishes exactly at z^2 = (sqrt(A1) +- sqrt(B1))^2,
which are the band edges g = sqrt(B1) - sqrt(A1) and S = sqrt(A1) + sqrt(B1). Then
X = (1 + A1 P)/z, Y = (1 + B1 P)/z, and the resolvents at the two kinds of vertex are
G_d = 1/(z - d Y) and G_q = 1/(z - q X). The matching measure of a (d,q)-biregular graph with m
vertices of degree d and r of degree q is the vertex-count average, so

    rho(x) = -(1/pi) Im [ (m G_d + r G_q) / (m + r) ]   at z = x + i0+.

SELF-CHECK, and it is a sharp one. The graph has exactly r positive roots, so the identity
n * integral from g to S of rho = r must hold exactly. Nothing below is trusted unless it does.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import json
import cmath
import numpy as np

ETA = 1e-10


def rho_vec(d, q, xs):
    """analytic density on an array of points; vertex-count weights depend only on (d,q),
    since m/n = q/(d+q) and r/n = d/(d+q), so one evaluation serves every size."""
    A1, B1 = d - 1.0, q - 1.0
    wm, wr = q / (d + q), d / (d + q)
    z = xs.astype(np.complex128) + 1j * ETA
    z2 = z * z
    disc = np.sqrt((z2 - A1 - B1) ** 2 - 4 * A1 * B1)
    best = np.zeros(len(xs))
    for sgn in (1, -1):
        P = ((z2 - A1 - B1) + sgn * disc) / (2 * A1 * B1)
        X = (1 + A1 * P) / z
        Y = (1 + B1 * P) / z
        G = wm / (z - d * Y) + wr / (z - q * X)
        v = -G.imag / math.pi
        best = np.maximum(best, v)
    return best


def cumulative(d, q, g, S, N=200000):
    """CDF of the positive band, as a fraction of total measure, on a sqrt-graded grid.

    The substitution x = g + (S-g) u^2 absorbs the square-root vanishing at the inner edge, so
    the integrand is smooth there and the grid resolves the region that sets the quantile."""
    u = np.linspace(0.0, 1.0, N)
    xs = g + (S - g) * u ** 2
    jac = (S - g) * 2 * u
    f = rho_vec(d, q, xs) * jac
    c = np.concatenate([[0.0], np.cumsum(0.5 * (f[1:] + f[:-1]) * np.diff(u))])
    return xs, c


def quantile_from_cdf(xs, c, g, n, target=1.0):
    """delta with n * (mass in [g, g+delta]) = target."""
    want = target / n
    if c[-1] < want:
        return None
    i = int(np.searchsorted(c, want))
    if i <= 0:
        return None
    lo, hi = c[i - 1], c[i]
    t = 0.0 if hi == lo else (want - lo) / (hi - lo)
    return float(xs[i - 1] + t * (xs[i] - xs[i - 1])) - g


def main():
    print("Analytic quantile prediction against the measured margin.\n")
    # data/ ships; private/ does not. This script is cited by the paper for a load-bearing
    # sentence, so its input has to be in the repository or a clean clone cannot reproduce it.
    try:
        D = json.load(open('data/softedge3_data.json'))
    except Exception:
        try:
            D = json.load(open('private/softedge3_data.json'))
        except Exception:
            print("input missing: run code/softedge3.py, which writes data/softedge3_data.json")
            return 1

    print("self-check: n * integral of rho over the positive band must equal r exactly\n")
    print(f"{'family':>9}{'r':>4}{'n':>5}{'n*int(rho)':>13}{'r':>6}{'rel err':>11}")
    ok = True
    for k in sorted(D):
        d, q = map(int, k.split(','))
        r = D[k][-1][0]; m = (r * q) // d; n = m + r
        g = math.sqrt(q - 1) - math.sqrt(d - 1); S = math.sqrt(q - 1) + math.sqrt(d - 1)
        _, c = cumulative(d, q, g, S)
        tot = n * c[-1]
        err = abs(tot - r) / r
        ok = ok and err < 0.02
        print(f"{'(' + k + ')':>9}{r:>4}{n:>5}{tot:>13.4f}{r:>6}{err:>11.2e}")
    if not ok:
        print("\nNORMALISATION FAILS: the density is wrong, nothing below is meaningful.")
        return 1
    print("\nnormalisation holds.\n")

    print(f"{'family':>9}{'q/d':>5}{'r':>4}{'n':>5}{'measured':>11}{'predicted':>11}"
          f"{'ratio':>8}")
    out = {}
    for k in sorted(D, key=lambda t: (int(t.split(',')[1]) // int(t.split(',')[0]), t)):
        d, q = map(int, k.split(','))
        g = math.sqrt(q - 1) - math.sqrt(d - 1); S = math.sqrt(q - 1) + math.sqrt(d - 1)
        xs, c = cumulative(d, q, g, S)
        rows = []
        for (r, n, meas) in D[k]:
            pred = quantile_from_cdf(xs, c, g, n)
            if pred is None:
                continue
            rows.append((r, n, meas, pred))
            if r in (D[k][0][0], D[k][len(D[k]) // 2][0], D[k][-1][0]):
                print(f"{'(' + k + ')':>9}{q // d:>5}{r:>4}{n:>5}{meas:>11.6f}"
                      f"{pred:>11.6f}{meas / pred:>8.3f}", flush=True)
        if len(rows) >= 6:
            out[k] = rows
        print()

    print(f"{'family':>9}{'q/d':>5}{'exp measured':>14}{'exp predicted':>15}{'diff':>9}"
          f"{'ratio drift':>13}")
    dm, dp = [], []
    for k, rows in sorted(out.items(),
                          key=lambda t: int(t[0].split(',')[1]) // int(t[0].split(',')[0])):
        d, q = map(int, k.split(','))
        ln = np.log([t[1] for t in rows])
        em = float(np.polyfit(ln, np.log([t[2] for t in rows]), 1)[0])
        ep = float(np.polyfit(ln, np.log([t[3] for t in rows]), 1)[0])
        rat = [t[2] / t[3] for t in rows]
        print(f"{'(' + k + ')':>9}{q // d:>5}{em:>14.4f}{ep:>15.4f}{ep - em:>+9.4f}"
              f"{rat[-1] / rat[0]:>13.3f}")
        dm.append((q // d, em)); dp.append((q // d, ep))

    print()
    bym, byp = {}, {}
    for (c, e) in dm:
        bym.setdefault(c, []).append(e)
    for (c, e) in dp:
        byp.setdefault(c, []).append(e)
    print(f"{'q/d':>5}{'measured':>12}{'predicted':>12}")
    for c in sorted(bym):
        print(f"{c:>5}{np.mean(bym[c]):>12.4f}{np.mean(byp[c]):>12.4f}")
    spread_m = float(np.std([np.mean(v) for v in bym.values()]))
    spread_p = float(np.std([np.mean(v) for v in byp.values()]))
    errs = [abs(a[1] - b[1]) for a, b in zip(dm, dp)]
    print(f"\n  spread across aspect ratios: measured {spread_m:.4f}, predicted {spread_p:.4f}")
    print(f"  |predicted - measured| exponent: mean {np.mean(errs):.4f}, max {max(errs):.4f}")
    if spread_p > 0.6 * spread_m and max(errs) < 0.035:
        print("\n  RESOLVED. The analytic quantile reproduces the aspect-ratio dependence, so it")
        print("  is a finite-size effect of the window, the q >= 3d families are pre-asymptotic,")
        print("  and the asymptotic exponent is the universal -2/3.")
    elif spread_p < 0.3 * spread_m:
        print("\n  RESOLVED THE OTHER WAY. The quantile prediction is flat across aspect ratios")
        print("  while the measurement is not, so the soft-edge quantile does NOT set the scale")
        print("  and the reading of the exponent as an edge effect is wrong.")
    else:
        print("\n  INCONCLUSIVE: the prediction neither reproduces the dependence nor is flat.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
