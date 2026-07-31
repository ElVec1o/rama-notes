"""ff_step5.py -- the free bound for box_p, verified, then applied.

THE TOOL (Marcus-Spielman-Srivastava; VERIFIED numerically here, not assumed):
for real-rooted monic f_1..f_m of degree d, with
    G_i(x) = (1/d) f_i'(x)/f_i(x),   K_i = G_i^{-1} on the outer branch,

    lambda_max(f_1 box_d ... box_d f_m)  <=  min_{w>0}  [ sum_i K_i(w) - (m-1)/w ]
    lambda_min(f_1 box_d ... box_d f_m)  >=  max_{w<0}  [ sum_i K_i(w) - (m-1)/w ]

and the right-hand sides are exactly the edges of the support of the FREE
convolution of the root measures.

CONSEQUENCE 1 (proved).   Psi := psi_0^{box_p a},  psi_0 = x^{p-p/b}(x-b)^{p/b}.
The root measure of psi_0 is EXACTLY chi = (1-1/b)delta_0 + (1/b)delta_b for
every p, so the bound gives, for every p divisible by b,

    spec(Psi) subset [ (sqrt(a-1)-sqrt(b-1))^2 , (sqrt(a-1)+sqrt(b-1))^2 ] .

CONSEQUENCE 2 (what this file measures).  Numerically mu is always box_p
divisible by psi_0^{box j} for some 1 <= j < a with a real-rooted quotient
rho_j.  Applying the bound to that splitting gives a CERTIFIED lower bound on
lambda_min(mu).  How far does it get?
"""
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
from ff_step1 import band, graph_fams, rand_fams                               # noqa
from ff_step4 import psi0, deconv, realrooted                                  # noqa


# --------------------------------------------------------------- K transform
def Kfun(roots, d, w, iters=80):
    """inverse Cauchy transform on the outer branch (Newton + safeguard).
    w<0 -> x below min root;  w>0 -> x above max root."""
    r = np.asarray(roots, dtype=float)
    n = len(r)
    if w < 0:
        x = r.min() - max(1.0, 1.0 / abs(w))
        lo, hi = -np.inf, r.min()
    else:
        x = r.max() + max(1.0, 1.0 / abs(w))
        lo, hi = r.max(), np.inf
    for _ in range(iters):
        g = np.mean(1.0 / (x - r))
        if g > w:
            lo = max(lo, x)
        else:
            hi = min(hi, x)
        gp = -np.mean(1.0 / (x - r) ** 2)
        step = (g - w) / gp
        xn = x - step
        if not (lo < xn < hi) or not np.isfinite(xn):
            xn = 0.5 * (lo + hi) if np.isfinite(lo) and np.isfinite(hi) else \
                (x - 1.0 if w < 0 else x + 1.0)
        if abs(xn - x) < 1e-14 * max(1.0, abs(x)):
            x = xn
            break
        x = xn
    return x


def free_edge(root_lists, d, side='min', ngrid=1200):
    """max_{w<0} [ sum K_i(w) - (m-1)/w ]  (side='min'), or the min over w>0."""
    m = len(root_lists)
    ws = -np.exp(np.linspace(np.log(1e-6), np.log(3e3), ngrid))
    if side == 'max':
        ws = -ws
    best = None
    for w in ws:
        try:
            v = sum(Kfun(r, d, w) for r in root_lists) - (m - 1) / w
        except Exception:
            continue
        if best is None or (side == 'min' and v > best) or (side == 'max' and v < best):
            best = v
    return best


def roots_of(e, d):
    return np.sort(np.roots(F.poly_from_signed_e(e, d)).real)


# ------------------------------------------------------------- verify the tool
def verify_tool(trials=40, seed=0):
    print("=" * 88)
    print("VERIFY the MSS free bound on random real-rooted pairs and triples")
    print("=" * 88)
    rng = np.random.default_rng(seed)
    worst_lo, worst_hi = 1e9, 1e9
    fails = 0
    for t in range(trials):
        d = int(rng.integers(3, 9))
        m = int(rng.integers(2, 4))
        Rs, es = [], []
        for _ in range(m):
            r = np.sort(rng.normal(0, 1, d) * rng.uniform(0.5, 3))
            Rs.append(r)
            es.append(F.signed_e_from_roots([Fraction(x).limit_denominator(10 ** 8)
                                             for x in r]))
        conv = es[0]
        for e in es[1:]:
            conv = F.boxp(conv, e, d)
        rc = roots_of(conv, d)
        lo_b = free_edge(Rs, d, 'min')
        hi_b = free_edge(Rs, d, 'max')
        ok = (rc.min() >= lo_b - 1e-7) and (rc.max() <= hi_b + 1e-7)
        if not ok:
            fails += 1
            print("   FAIL d=%d m=%d  roots=[%.6f,%.6f] bound=[%.6f,%.6f]"
                  % (d, m, rc.min(), rc.max(), lo_b, hi_b))
        worst_lo = min(worst_lo, rc.min() - lo_b)
        worst_hi = min(worst_hi, hi_b - rc.max())
    print("   trials=%d  failures=%d   min slack lower=%.3e  upper=%.3e"
          % (trials, fails, worst_lo, worst_hi))
    print()


# ------------------------------------------------- consequence 1: Psi
def check_Psi():
    print("=" * 88)
    print("CONSEQUENCE 1: Psi = psi_0^{box_p a} obeys the tree band at every p")
    print("=" * 88)
    for (a, b) in [(3, 2), (4, 2), (4, 3), (5, 3), (6, 4)]:
        lo, hi = band(a, b)
        chi = [0.0] * (b - 1) + [float(b)]         # root measure of psi_0, any p
        pred_lo = free_edge([chi] * a, b, 'min')
        pred_hi = free_edge([chi] * a, b, 'max')
        row = "  a=%d b=%d  free bound [%.6f,%.6f]  tree [%.6f,%.6f]  " \
              % (a, b, pred_lo, pred_hi, lo, hi)
        row += " exact roots of Psi:"
        for p in [b * mm for mm in (1, 2, 4, 8)]:
            e = F.boxp_power(psi0(p, b), p, a)
            row += " p=%d:[%.4f,%.4f]" % (p, F.minroot_exact(e, p, iters=40),
                                          F.maxroot_exact(e, p, iters=40))
        print(row)
    print()


# ---------------------------------- consequence 2: what divisibility buys
def check_divisibility_bound():
    print("=" * 88)
    print("CONSEQUENCE 2: certified lower bound from  mu = psi_0^{box j} box rho_j")
    print("=" * 88)
    print("%-24s %-10s %-4s %-11s %-11s %-11s" %
          ("family", "(p,q,a,b)", "jmax", "certified lo", "true lmin", "tree lo"))
    for name, p, q, a, b, e in graph_fams() + rand_fams():
        lo, hi = band(a, b)
        best = None
        for j in range(1, a + 1):
            f = F.boxp_power(psi0(p, b), p, j)
            rho = deconv(e, f, p)
            rr, rts, _ = realrooted(rho, p)
            if not rr:
                continue
            chi = [0.0] * (p - p // b) + [float(b)] * (p // b)
            cand = free_edge([chi] * j + [list(rts)], p, 'min')
            if best is None or cand > best[1]:
                best = (j, cand)
        true_lo = F.minroot_exact(e, p, iters=45)
        if best is None:
            print("  %-24s (%d,%d,%d,%d)  none" % (name, p, q, a, b))
            continue
        print("  %-24s (%d,%d,%d,%d) j=%d  %11.6f %11.6f %11.6f   reaches tree edge=%s"
              % (name, p, q, a, b, best[0], best[1], true_lo, lo, best[1] >= lo - 1e-9))
    print()


if __name__ == '__main__':
    import sys as _s
    w = _s.argv[1] if len(_s.argv) > 1 else 'all'
    if w in ('all', 'v'):
        verify_tool()
    if w in ('all', '1'):
        check_Psi()
    if w in ('all', '2'):
        check_divisibility_bound()
