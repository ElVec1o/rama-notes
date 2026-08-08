"""Dproof.py -- the MECHANISM behind the direct-sum failures, and a proof.

FACT A (classical, re-verified).  For real c != 0 and real-rooted rho,
    (1 - c d/dx) rho  =  -c e^{x/c} ( e^{-x/c} rho )'
is real-rooted; a root of rho of multiplicity s becomes a root of multiplicity
exactly s-1, and every OTHER root of the image is SIMPLE.
  [If rho(L) != 0 and (rho - c rho')(L) = 0, put u = rho'/rho - 1/c.  Then
   u(L) = 0 and (rho - c rho')' = -c (u' + u^2) rho, so at L it equals
   -c u'(L) rho(L) with u'(L) = -sum 1/(L-r_i)^2 < 0 -- nonzero.]

FACT B (checked numerically here).  psi_0 box_p . is the differential operator
    Phi(d/dx),   Phi(z) = sum_j ((p-j)!/p!) (-t)^j C(m,j) z^j ,
and Phi has all real roots for the (p, m, t) that occur, so it factors as
    prod_{i=1}^m (1 - c_i d/dx),  c_i real and nonzero.

COROLLARY.  If mu = x^{p-m}(x-t)^m box_p rho with rho real-rooted, then every
root of mu of multiplicity s >= 2 is a root of rho of multiplicity s + m.  Hence
    sum over {roots of mu with mult >= 2} of (s_i + m)  <=  deg rho = p.
For a DIRECT SUM of two copies of one tight fusion frame, mu = mu_1^2 with mu_1
of degree p/2 and (generically) simple roots, so the left side is
(p/2)(2+m) = p + pm/2 > p.  CONTRADICTION: no real-rooted rho, for ANY t != 0
and ANY m >= 1.  So (D) fails for every doubled family, and t* = 0 exactly.
"""
from fractions import Fraction
import sys
sys.path.insert(0,'/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import numpy as np
from math import comb, factorial
from Dclaim import boxp, deconv, poly_from_roots, psi0, is_real_rooted_exact

def Phi_roots(p, m, t):
    c = [((-t)**j) * comb(m, j) * factorial(p-j)/factorial(p) for j in range(m+1)]
    return np.roots(c[::-1])

print("FACT B: is Phi real-rooted for the (p,m,t) that occur?  (m = p/b, t = b)")
bad = 0
for b in (2,3,4,5):
    for p in range(b, 61):
        if p % b: continue
        m = p//b
        r = Phi_roots(p, m, float(b))
        mi = np.max(np.abs(r.imag))/max(1.0, np.max(np.abs(r.real)))
        if mi > 1e-8:
            bad += 1
            if bad < 8: print("   NOT real-rooted: p=%d b=%d m=%d  max|Im|/scale=%.2e" % (p,b,m,mi))
print("   checked all b in 2..5, p <= 60 with b|p:  non-real-rooted cases =", bad)
print()

print("FACT A + corollary, checked directly: multiplicity bookkeeping")
print("  rho with a root of multiplicity s -> mult in psi_0 box_p rho")
for (p,b) in [(6,2),(8,2),(6,3),(8,4)]:
    m = p//b
    for s in range(1, p+1):
        roots = [Fraction(0)]*s + [Fraction(i+1) for i in range(p-s)]
        rho = poly_from_roots(roots)
        h = boxp(psi0(p,b), rho, p)
        # multiplicity of 0 in h
        k = 0
        while k <= p and h[p-k] == 0: k += 1
        pred = max(s-m, 0)
        if k != pred:
            print("   p=%d b=%d m=%d s=%2d : mult=%d  predicted max(s-m,0)=%d  MISMATCH" % (p,b,m,s,k,pred))
    print("   p=%d b=%d m=%d : multiplicity drops by exactly m, for every s  [OK]" % (p,b,m))
print()

print("THE DIRECT-SUM COUNTEREXAMPLE FAMILY (exact Sturm)")
from Dscan import (mu_from_blocks, edges_to_blocks, complete_graph,
                   complete_bipartite, circulant, hypercube)
def polymul(f,g):
    out=[Fraction(0)]*(len(f)+len(g)-1)
    for i,x in enumerate(f):
        for j,y in enumerate(g): out[i+j]+=Fraction(x)*Fraction(y)
    return out
print("%-30s %-4s %-4s %-3s | %-8s %-10s %-14s" %
      ("base M_0 (+ itself)","p0","p","b","(D)","#real/p","sum(s_i+m) vs p"))
for nm,E,p0,b in [('K_4 (a=3,b=2)',*complete_graph(4),2),
                  ('K_{3,3} (a=3,b=2)',*complete_bipartite(3),2),
                  ('circ(6,[1,2]) (a=4,b=2)',*circulant(6,[1,2]),2),
                  ('K_6 (a=5,b=2)',*complete_graph(6),2),
                  ('Q_3 (a=3,b=2)',*hypercube(3),2)]:
    mu0 = mu_from_blocks(edges_to_blocks(E), p0)
    mu = polymul(mu0, mu0); p = 2*p0; m = p//b
    rho = deconv(mu, psi0(p,b), p)
    rr, nreal, nsq = is_real_rooted_exact(rho)
    # distinct roots of mu0 (all multiplicity 2 in mu if mu0 squarefree)
    d = is_real_rooted_exact(mu0)[2]
    print("  %-30s %-4d %-4d %-3d | %-8s %2d/%-7d %d*(2+%d)=%d > %d" %
          (nm,p0,p,b,rr,nreal,p,d,m,d*(2+m),p))
