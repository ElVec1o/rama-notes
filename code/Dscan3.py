"""Dscan3.py -- (a) how much divisibility is actually there, (b) the scalar-family
regression, (c) the b>=3 audit with certified arithmetic.

(a) For divisor  g_{m,t}(x) = x^{p-m}(x-t)^m  we find
        t*(m) = sup { t >= 0 : mu deconv g_{m,t} is real-rooted }.
    (D) is the statement  t*(p/b) >= b.  Reporting t*(p/b)/b says how close.

(b) The scalar family A_k = (b/p) I_p is NOT a projection family and violates the
    tree band.  Where does IT sit on the same scale?

(c) The b>=3 families -- commuting designs exactly, random tight fusion frames
    with a sign-alternation certificate that tolerates the float error in mu.
"""
from fractions import Fraction
from math import comb
import sys

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from Dclaim import (boxp, boxp_pow, deconv, poly_from_roots, psi0,            # noqa
                    is_real_rooted_exact, maximag_float)
from Dscan import (mu_from_blocks, edges_to_blocks, check_biregular,          # noqa
                   has_parallel_class, complete_graph, complete_bipartite,
                   hypercube, petersen, cycle_prism, moebius_ladder, gp,
                   circulant)


# ------------------------------------------------------------------ (a)
def rr_at(mu, p, b, m, t):
    g = poly_from_roots([Fraction(0)] * (p - m) + [Fraction(t)] * m)
    rho = deconv(mu, g, p)
    return is_real_rooted_exact(rho)[0]


def tstar(mu, p, b, m, tmax=None, iters=13):
    """sup{t>=0 : real-rooted}, by bisection on the exact predicate, restricted
    to DYADIC t with denominator <= 2^iters.  (Unbounded bisection makes the
    Fraction denominators blow up and the exact Sturm test intractable; 2^-13
    resolution is far finer than anything we conclude from.)"""
    if tmax is None:
        tmax = Fraction(4 * b)
    tmax = Fraction(tmax)
    if rr_at(mu, p, b, m, tmax):
        return float(tmax), True          # saturated
    lo, hi = 0, 1 << iters                # integer grid, t = tmax * k / 2^iters
    for _ in range(iters):
        mid = (lo + hi) // 2
        if mid == lo:
            break
        if rr_at(mu, p, b, m, tmax * Fraction(mid, 1 << iters)):
            lo = mid
        else:
            hi = mid
    return float(tmax * Fraction(lo, 1 << iters)), False


def interval_check(mu, p, b, m, tmax, n=25):
    """is {t : real-rooted} an initial interval?  coarse grid check."""
    vals = [rr_at(mu, p, b, m, Fraction(i, n) * Fraction(tmax)) for i in range(n + 1)]
    flips = sum(1 for i in range(n) if vals[i] != vals[i + 1])
    return flips <= 1, vals


# ------------------------------------------------------------------ (b)
def scalar_mu(p, q, a, b):
    """EXACT mu for A_k = (b/p) I_p:  e_m = C(q,m) (b/p)^m p!/(p-m)!,
    mu = sum_m (-1)^m e_m x^{p-m}."""
    c = Fraction(b, p)
    out = []
    ff = Fraction(1)
    for m in range(p + 1):
        if m > 0:
            ff *= (p - m + 1)
        out.append(Fraction((-1) ** m) * comb(q, m) * c ** m * ff)
    return out


# ------------------------------------------------------------------ (c)
def alternation_certificate(rho, p, eps):
    """Certify real-rootedness of every polynomial within absolute coefficient
    error eps of rho (coefficients highest-power-first, monic).
    Strategy: find p+1 sample points where rho alternates in sign, and check the
    margin |rho(t)| exceeds the worst-case perturbation sum eps*|t|^{p-i}."""
    r = np.roots([float(x) for x in rho])
    if np.max(np.abs(r.imag)) > 1e-9 * max(1.0, np.max(np.abs(r.real))):
        return False, 0.0
    rr = np.sort(r.real)
    pts = [rr[0] - 1.0]
    for i in range(len(rr) - 1):
        pts.append(0.5 * (rr[i] + rr[i + 1]))
    pts.append(rr[-1] + 1.0)
    worst = np.inf
    for i, t in enumerate(pts):
        val = float(np.polyval([float(x) for x in rho], t))
        want = (-1.0) ** (p - i)
        if val * want <= 0:
            return False, 0.0
        pert = eps * sum(abs(t) ** (p - j) for j in range(1, p + 1))
        worst = min(worst, abs(val) / max(pert, 1e-300))
    return True, float(worst)


def designs():
    """commuting families with b >= 3: block designs / hypergraphs."""
    out = []
    # K_{m,n}: p = m, q = n, a = n, b = m
    for (m, n) in [(3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (4, 3), (5, 6), (6, 7)]:
        out.append(('K_{%d,%d}' % (m, n), [tuple(range(m))] * n, m, n, n, m))
    # cube (4,3)-design: p=6 faces, q=8 vertices
    from itertools import product as ip
    verts = list(ip((0, 1), repeat=3))
    faces = [(c, v) for c in range(3) for v in (0, 1)]
    blk = [tuple(i for i, (c, v) in enumerate(faces) if x[c] == v) for x in verts]
    out.append(('cube (4,3)-design', blk, 6, 8, 4, 3))
    # Fano plane (Heawood): p=7 points, q=7 lines, a=3, b=3
    lines = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6),
             (4, 5, 0), (5, 6, 1), (6, 0, 2)]
    out.append(('Fano/Heawood (3,3)', lines, 7, 7, 3, 3))
    # AG(2,3): 9 points, 12 lines, a=4, b=3  (resolvable!)
    pts = [(i, j) for i in range(3) for j in range(3)]
    pidx = {v: i for i, v in enumerate(pts)}
    L = []
    for (dx, dy) in [(0, 1), (1, 0), (1, 1), (1, 2)]:
        for s in range(3):
            base = (0, s) if (dx, dy) == (0, 1) else (s, 0)
            if (dx, dy) == (0, 1):
                line = [((0 + k * dx) % 3, (s + k * dy) % 3) for k in range(3)]
            else:
                line = [((base[0] + k * dx) % 3, (base[1] + k * dy) % 3)
                        for k in range(3)]
            L.append(tuple(sorted(pidx[v] for v in line)))
    L = sorted(set(L))
    out.append(('AG(2,3) 9pt 12line', L, 9, 12, 4, 3))
    # 2-(7,3,1) doubled -> a=6
    out.append(('Fano doubled (6,3)', lines * 2, 7, 14, 6, 3))
    # complete 3-uniform on 6 points: p=6, q=20, a=10, b=3
    from itertools import combinations as ic
    out.append(('K_6^{(3)} all triples', list(ic(range(6), 3)), 6, 20, 10, 3))
    # complete 4-uniform on 8: p=8, q=70, a=35, b=4  (too big -> skip)
    out.append(('K_6^{(2)} = K_6 b=2', list(ic(range(6), 2)), 6, 15, 5, 2))
    # 4-uniform: 2-(8,4,3) = AG(3,2) planes: 14 blocks, a=7, b=4
    V = list(ip((0, 1), repeat=3))
    vidx = {v: i for i, v in enumerate(V)}
    planes = set()
    for a1 in range(1, 8):
        for c in (0, 1):
            pl = tuple(sorted(vidx[v] for v in V
                              if (sum(((a1 >> k) & 1) * v[k] for k in range(3)) % 2) == c))
            planes.add(pl)
    out.append(('AG(3,2) planes (7,4)', sorted(planes), 8, 14, 7, 4))
    return out


def main_a():
    print("=" * 118)
    print("(a) HOW MUCH DIVISIBILITY:  t*(m) = sup{t : mu deconv x^{p-m}(x-t)^m real-rooted}")
    print("    (D) needs t*(p/b) >= b.   ratio = t*/b.")
    print("=" * 118)
    fams = [('K_4', *complete_graph(4)), ('K_{3,3}', *complete_bipartite(3)),
            ('prism C_3xK_2', *cycle_prism(3)), ('Q_3 cube', *hypercube(3)),
            ('Wagner M_4', *moebius_ladder(4)), ('Petersen', *petersen()),
            ('C_5xK_2', *cycle_prism(5)), ('Moebius M_5', *moebius_ladder(5)),
            ('C_6xK_2', *cycle_prism(6)), ('Moebius M_6', *moebius_ladder(6)),
            ('GP(6,2)', *gp(6, 2)), ('GP(7,2)', *gp(7, 2)),
            ('K_{4,4} a=4', *complete_bipartite(4)),
            ('circ(12,[1,2]) a=4', *circulant(12, [1, 2])),
            ('K_6 a=5', *complete_graph(6))]
    print("%-20s %3s %3s %3s | %-6s %-9s %-7s | %-10s" %
          ("family", "p", "q", "a", "(D)", "t*(p/2)", "t*/b", "interval?"))
    for name, E, p in fams:
        blocks = edges_to_blocks(E)
        q = len(blocks)
        if (2 * q) % p or p % 2:
            continue
        a = 2 * q // p
        mu = mu_from_blocks(blocks, p)
        m = p // 2
        ts, sat = tstar(mu, p, 2, m)
        iv, _ = interval_check(mu, p, 2, m, 4)
        D = rr_at(mu, p, 2, m, Fraction(2))
        print("  %-20s %3d %3d %3d | %-6s %9.5f %7.4f | %-10s%s"
              % (name, p, q, a, D, ts, ts / 2.0, iv, "  (saturated)" if sat else ""))
    print()


def main_b():
    print("=" * 118)
    print("(b) REGRESSION: the scalar family A_k = (b/p) I_p  (NOT projections; "
          "violates the tree band)")
    print("=" * 118)
    print("%-24s %3s %4s %3s %3s | %-6s %-9s %-8s" %
          ("family", "p", "q", "a", "b", "(D)", "t*(p/b)", "t*/b"))
    for (p, a, b) in [(4, 3, 2), (6, 3, 2), (8, 3, 2), (10, 3, 2), (12, 3, 2),
                      (14, 3, 2), (16, 3, 2), (8, 4, 2), (12, 4, 2),
                      (6, 4, 3), (9, 4, 3), (12, 4, 3)]:
        q = p * a // b
        mu = scalar_mu(p, q, a, b)
        m = p // b
        D = rr_at(mu, p, b, m, Fraction(b))
        ts, sat = tstar(mu, p, b, m)
        print("  %-24s %3d %4d %3d %3d | %-6s %9.5f %8.4f%s"
              % ('scalar (b/p)I', p, q, a, b, D, ts, ts / b,
                 "  (saturated)" if sat else ""))
    print()


def main_c():
    print("=" * 118)
    print("(c) b >= 3 COMMUTING DESIGNS -- exact, Sturm-certified")
    print("=" * 118)
    print("%-22s %3s %4s %3s %3s | %-7s %-6s | %-8s %-10s %-9s" %
          ("design", "p", "q", "a", "b", "par.cl", "(D)", "#real", "t*(p/b)", "t*/b"))
    nD = nT = 0
    for name, blocks, p, q, a, b in designs():
        blocks = [tuple(sorted(B)) for B in blocks]
        if not check_biregular(blocks, p, a, b):
            print("  %-22s SKIP (not biregular)" % name)
            continue
        if p % b:
            print("  %-22s %3d %4d %3d %3d | b does not divide p -- psi_0 undefined"
                  % (name, p, q, a, b))
            continue
        if p > 14:
            print("  %-22s SKIP (p too large for the DP)" % name)
            continue
        mu = mu_from_blocks(blocks, p)
        m = p // b
        rho = deconv(mu, psi0(p, b), p)
        rr, nreal, nsq = is_real_rooted_exact(rho)
        pc = has_parallel_class(blocks, p, b)
        ts, sat = tstar(mu, p, b, m, tmax=Fraction(4 * b))
        nT += 1
        nD += int(rr)
        print("  %-22s %3d %4d %3d %3d | %-7s %-6s | %d/%-6d %10.5f %9.4f%s"
              % (name, p, q, a, b, pc, rr, nreal, nsq, ts, ts / b,
                 "  (sat)" if sat else ""))
    print("  --> (D) holds in %d / %d commuting b>=3 designs tested" % (nD, nT))
    print()


if __name__ == '__main__':
    w = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if w in ('all', 'a'):
        main_a()
    if w in ('all', 'b'):
        main_b()
    if w in ('all', 'c'):
        main_c()
