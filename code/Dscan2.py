"""Dscan2.py -- the divisor landscape.  What survives of (D)?

For each family we compute EXACTLY (Fractions + Sturm):
  * G(m)  = { m : mu deconv x^{p-m}(x-b)^m is real-rooted },  m = 0..p
  * J     = { j : mu deconv (x^{p-1}(x-b))^{box j} is real-rooted }
  * lambda_min(mu), the tree band, the cumulants of rho
so we can see what the real invariant is.
"""
from fractions import Fraction
import sys

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from Dclaim import (boxp, boxp_pow, deconv, poly_from_roots, psi0,            # noqa
                    is_real_rooted_exact, maximag_float)
from Dscan import (mu_from_blocks, edges_to_blocks, check_biregular,          # noqa
                   has_parallel_class, has_resolution, complete_graph,
                   complete_bipartite, hypercube, petersen, cycle_prism,
                   moebius_ladder, gp, circulant)


def good_m_set(mu, p, b):
    out = []
    for m in range(0, p + 1):
        rho = deconv(mu, psi0(p, b, m), p)
        rr, _, _ = is_real_rooted_exact(rho)
        if rr:
            out.append(m)
    return out


def good_j_set(mu, p, b, jmax):
    """divisor (x^{p-1}(x-b))^{box j} -- the 'free slots' divisor."""
    phi = poly_from_roots([Fraction(0)] * (p - 1) + [Fraction(b)])
    out = []
    for j in range(0, jmax + 1):
        f = boxp_pow(phi, p, j)
        rho = deconv(mu, f, p)
        rr, _, _ = is_real_rooted_exact(rho)
        if rr:
            out.append(j)
    return out


def kappas(c, p, n=6):
    """finite free cumulants kappa_1..kappa_n from coefficients (h.p. first)."""
    from math import comb, factorial
    E = [Fraction(c[i]) * Fraction((-1) ** i) / comb(p, i) for i in range(p + 1)]
    kh = [Fraction(0)] * (p + 1)
    for k in range(0, p):
        acc = Fraction(0)
        for i in range(1, k + 1):
            acc += comb(k, i - 1) * kh[i] * E[k + 1 - i]
        kh[k + 1] = E[k + 1] - acc
    return [Fraction(0)] + [(-1) ** (k - 1) * Fraction(p) ** (k - 1) * kh[k]
                            / factorial(k - 1) for k in range(1, min(n, p) + 1)]


def minroot(c, p):
    r = np.roots([float(x) for x in c])
    return float(np.min(r.real)), float(np.max(r.real))


FAMS = [('K_4', *complete_graph(4)),
        ('K_{3,3}', *complete_bipartite(3)),
        ('prism C_3xK_2', *cycle_prism(3)),
        ('Q_3 = C_4xK_2', *hypercube(3)),
        ('Wagner M_4 (V_8)', *moebius_ladder(4)),
        ('Petersen', *petersen()),
        ('C_5xK_2 = GP(5,1)', *cycle_prism(5)),
        ('Moebius M_5', *moebius_ladder(5)),
        ('GP(5,2)=Petersen', *gp(5, 2)),
        ('C_6xK_2', *cycle_prism(6)),
        ('Moebius M_6', *moebius_ladder(6)),
        ('GP(6,2)', *gp(6, 2)),
        ('GP(7,2)', *gp(7, 2)),
        ('Heawood GP(7,3)?', *gp(7, 3)),
        ('K_{4,4} (a=4)', *complete_bipartite(4)),
        ('K_6 (a=5)', *complete_graph(6)),
        ('circ(6,[1,2]) a=4', *circulant(6, [1, 2])),
        ('circ(8,[1,2]) a=4', *circulant(8, [1, 2])),
        ('circ(8,[1,3]) a=4', *circulant(8, [1, 3])),
        ('circ(10,[1,2]) a=4', *circulant(10, [1, 2])),
        ('circ(12,[1,2]) a=4', *circulant(12, [1, 2])),
        ('circ(10,[1,2,3]) a=6', *circulant(10, [1, 2, 3])),
        ('circ(8,[1,2,3]) a=6', *circulant(8, [1, 2, 3])),
        ('K_8 (a=7)', *complete_graph(8)),
        ('K_{5,5} (a=5)', *complete_bipartite(5)),
        ('K_{6,6} (a=6)', *complete_bipartite(6)),
        ]


def main():
    print("=" * 122)
    print("DIVISOR LANDSCAPE, b = 2 commuting families.  psi_0 = x^{p/2}(x-2)^{p/2}")
    print("  (D) <=> (p/2) in G(m).   band lo = (sqrt(a-1)-1)^2")
    print("=" * 122)
    hdr = ("%-20s %3s %3s %3s | %-5s %-6s | %-22s %-14s | %-8s %-8s %-8s"
           % ("graph M", "p", "q", "a", "(D)", "par.cl", "G(m)={m: rr}",
              "J(free slots)", "lmin(mu)", "band lo", "k4(rho)"))
    print(hdr)
    rows = []
    for name, E, p in FAMS:
        blocks = edges_to_blocks(E)
        q = len(blocks)
        if (2 * q) % p:
            continue
        a = 2 * q // p
        if not check_biregular(blocks, p, a, 2) or p % 2:
            continue
        mu = mu_from_blocks(blocks, p)
        G = good_m_set(mu, p, 2)
        J = good_j_set(mu, p, 2, min(q, 8))
        D = (p // 2) in G
        pc = has_parallel_class(blocks, p, 2)
        lo, hi = minroot(mu, p)
        bandlo = (np.sqrt(a - 1.0) - 1.0) ** 2
        rho = deconv(mu, psi0(p, 2), p)
        k = kappas(rho, p, 4)
        print("  %-20s %3d %3d %3d | %-5s %-6s | %-22s %-14s | %8.5f %8.5f %8.4f"
              % (name, p, q, a, D, pc, str(G), str(J), lo, bandlo,
                 float(k[4]) if len(k) > 4 else float('nan')))
        rows.append(dict(name=name, p=p, q=q, a=a, D=D, G=G, J=J, lmin=lo,
                         bandlo=bandlo, k4=float(k[4]) if len(k) > 4 else None))
    return rows


if __name__ == '__main__':
    main()
