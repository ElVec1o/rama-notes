"""An EXACT rational member of class (C) violating the tree band at (a,b)=(3,2).

Class (C) = {K : 0 <= K <= I, diagonal b x b blocks all equal (1/a) I_b}
          = determinantal measures on the slot set with the same 1-point
            marginals (1/a) and the same within-block 2-point marginals
            (1/a^2, i.e. within-block decorrelation) as a graph.

Every such K is strongly Rayleigh (Borcea-Branden-Liggett) and N_K is
real rooted (bridge identity + MSS).  We look for one whose smallest root
falls below (sqrt(a-1)-sqrt(b-1))^2, using rational convex combinations
      K = (1-l) Pi_G + l Pi_H,      l in Q,
of two graph kernels on the SAME slot labelling (so the block condition is
automatic and K is rational).
"""
import sys
from fractions import Fraction
from itertools import combinations
import numpy as np
import mpmath as mp
from frac_naimark import det_frac, sub, N_transversal, matching_counts
from frac_classes import band, all_biregular, N_K


def graph_kernel_slots(adj, p, q, a, b):
    """Pi for G, on the FIXED slot labelling slot(k,j) = j-th smallest
    P-neighbour of Q-vertex k.  (Different graphs give different kernels on
    the same index set, so convex combinations make sense.)"""
    slots = []
    for k in range(q):
        nb = [i for i in range(p) if (adj[i] >> k) & 1]
        assert len(nb) == b
        slots += [(k, i) for i in nb]
    n = len(slots)
    return [[Fraction(1, a) if slots[x][1] == slots[y][1] else Fraction(0)
             for y in range(n)] for x in range(n)], slots


def to_np(M):
    return np.array([[float(x) for x in row] for row in M])


def scan(p, q, a, b, lams, cap=300):
    lo, hi = band(a, b)
    Gs = all_biregular(p, q, a, b, cap=cap)
    print(f"p={p} q={q} (a,b)=({a},{b})  band [{lo:.6f},{hi:.6f}]  "
          f"{len(Gs)} labelled graphs")
    ker = [graph_kernel_slots(g, p, q, a, b)[0] for g in Gs]
    best = None
    for i in range(len(Gs)):
        Ki = to_np(ker[i])
        for j in range(i + 1, len(Gs)):
            Kj = to_np(ker[j])
            for l in lams:
                Kx = (1 - float(l)) * Ki + float(l) * Kj
                c = N_K(Kx, q, b, a)
                r = np.roots(c)
                rr = np.sort(r.real)
                nz = rr[np.abs(rr) > 1e-9]
                if not len(nz):
                    continue
                v = nz.min()
                if best is None or v < best[0]:
                    best = (v, i, j, l, np.abs(r.imag).max())
    v, i, j, l, im = best
    print(f"  best convex combination: lambda={l}  smallest nonzero root "
          f"{v:.8f}  (max|Im| {im:.1e})  "
          f"{'*** VIOLATION ***' if v < lo - 1e-9 else 'inside'}")
    return Gs[i], Gs[j], l, best


def verify_exact(adjG, adjH, l, p, q, a, b):
    """exact rational N_K and high-precision roots."""
    KG, _ = graph_kernel_slots(adjG, p, q, a, b)
    KH, _ = graph_kernel_slots(adjH, p, q, a, b)
    n = q * b
    Kx = [[(1 - l) * KG[x][y] + l * KH[x][y] for y in range(n)]
          for x in range(n)]
    # class membership: blocks and 0 <= K <= I
    blk_ok = all(Kx[k * b + u][k * b + v] == (Fraction(1, a) if u == v else 0)
                 for k in range(q) for u in range(b) for v in range(b))
    w = np.linalg.eigvalsh(to_np(Kx))
    c = N_transversal(Kx, q, b, a, exact=True)      # c[j] = coeff of y^j
    mp.mp.dps = 60
    poly = [mp.mpf(x.numerator) / mp.mpf(x.denominator) for x in c[::-1]]
    while poly and poly[0] == 0:
        poly = poly[1:]
    r = mp.polyroots(poly, maxsteps=300, extraprec=300)
    rr = sorted([mp.re(x) for x in r])
    im = max(abs(mp.im(x)) for x in r)
    lo, hi = band(a, b)
    nz = [x for x in rr if abs(x) > mp.mpf('1e-40')]
    print("  EXACT verification")
    print(f"    block condition holds exactly : {blk_ok}")
    print(f"    spectrum of K in [{w.min():.6f},{w.max():.6f}]  "
          f"(needs [0,1]) : {w.min() > -1e-12 and w.max() < 1 + 1e-12}")
    print(f"    N_K coefficients (y^0..y^q)   : {[str(x) for x in c]}")
    print(f"    roots (60 digits, max|Im| {float(im):.1e}) :")
    for x in nz:
        print(f"        {mp.nstr(x, 25)}")
    print(f"    smallest nonzero root {mp.nstr(nz[0], 20)}  vs lower edge "
          f"{lo:.15f}   ->  {'VIOLATION' if float(nz[0]) < lo else 'inside'}")


if __name__ == '__main__':
    p, q, a, b = 4, 6, 3, 2
    lams = [Fraction(k, 12) for k in range(1, 12)]
    G, H, l, best = scan(p, q, a, b, lams, cap=60)
    print(f"  G = {[bin(x) for x in G]}")
    print(f"  H = {[bin(x) for x in H]}")
    verify_exact(G, H, l, p, q, a, b)
