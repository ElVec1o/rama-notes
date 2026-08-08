"""Dasym.py -- the p -> infinity limit of (D), at FIXED root measure.

If M = M_0 disjoint-union k times, the incidence bipartite graph is the k-fold
disjoint union too, so the matching generating polynomial MULTIPLIES:
    mu_{kM_0} = (mu_{M_0})^k ,   p = k p_0 ,  same (a,b), same root MEASURE.
So this sweeps p -> infinity with the empirical root measure of mu held exactly
fixed: it is precisely the finite-p approach to the free deconvolution
    nu_0  boxminus  chi ,      chi = (1-1/b) delta_0 + (1/b) delta_b .
If (D) were an asymptotic truth for these (a,b), t*/b must stay >= 1 as k grows.
"""
from fractions import Fraction
import sys
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import numpy as np
from Dclaim import deconv, psi0, poly_from_roots, maximag_float
from Dscan import (mu_from_blocks, edges_to_blocks, complete_graph,
                   complete_bipartite, circulant, hypercube, moebius_ladder)

def polymul(f, g):
    out = [Fraction(0)] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            out[i + j] += Fraction(x) * Fraction(y)
    return out

def rr_hp(c, p, tol=1e-7):
    mi, rts = maximag_float(c, dps=max(60, 3 * p))
    return mi < tol, mi

def tstar_hp(mu, p, b, m, tmax, iters=6):
    def ok(t):
        g = poly_from_roots([Fraction(0)] * (p - m) + [Fraction(t)] * m)
        return rr_hp(deconv(mu, g, p), p)[0]
    if ok(Fraction(tmax)):
        return float(tmax), True
    lo, hi = 0, 1 << iters
    for _ in range(iters):
        mid = (lo + hi) // 2
        if mid == lo: break
        if ok(Fraction(tmax) * Fraction(mid, 1 << iters)): lo = mid
        else: hi = mid
    return float(Fraction(tmax) * Fraction(lo, 1 << iters)), False

BASES = [('K_4        (a=3,b=2)', *complete_graph(4), 3, 2),
         ('circ(6,[1,2])(a=4,b=2)', *circulant(6, [1, 2]), 4, 2),
         ('K_{4,4}    (a=4,b=2)', *complete_bipartite(4), 4, 2),
         ('K_6        (a=5,b=2)', *complete_graph(6), 5, 2),
         ('circ(8,[1,2,3])(a=6,b=2)', *circulant(8, [1, 2, 3]), 6, 2)]

print("%-26s %-4s %-4s | %-8s %-10s %-9s %-10s" %
      ("base graph M_0", "k", "p", "(D)", "max|Im|", "t*/b", "verdict"))
for name, E, p0, a, b in BASES:
    mu0 = mu_from_blocks(edges_to_blocks(E), p0)
    mu = [Fraction(1)]
    for k in range(1, 9):
        mu = polymul(mu, mu0)
        p = k * p0
        if p % b or p > 36: continue
        rho = deconv(mu, psi0(p, b), p)
        rr, mi = rr_hp(rho, p)
        ts, sat = tstar_hp(mu, p, b, p // b, 3 * b)
        print("  %-26s %-4d %-4d | %-8s %10.3e %9.4f %s" %
              (name, k, p, rr, mi, ts / b, "(sat)" if sat else ""))
        sys.stdout.flush()
    print()
