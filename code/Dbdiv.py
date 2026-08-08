"""Dbdiv.py -- question 4: what happens when b does NOT divide p?

psi_0 = x^{p-p/b}(x-b)^{p/b} is undefined.  The construction that motivated it
produces  chi[ b Q ]  with Q = the projection onto the span of one unit vector
from each block of a PARTIAL parallel class; the largest possible such class has
m = floor(p/b) blocks (no full one can exist when b does not divide p).  So the
forced generalisation is
        psi_0^{(m)}(x) = x^{p-m} (x-b)^m ,   m = floor(p/b),
which removes kappa_1 = m b / p < 1 instead of 1.  Reported below together with
t*(m) = sup{t : mu deconv x^{p-m}(x-t)^m real-rooted}, so one can see both
  t*/b            (is the FORCED divisor admissible?)
  t* m / p        (what fraction of one full unit of kappa_1 can be removed?)
"""
from fractions import Fraction
import sys
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import numpy as np
from Dclaim import deconv, psi0, poly_from_roots, is_real_rooted_exact, maximag_float
from Dscan3 import tstar, rr_at
from Dscan import (mu_from_blocks, edges_to_blocks, complete_graph, circulant,
                   check_biregular, petersen)
from mcp2 import mcp

def icosahedral():
    """6 rank-2 projections on R^3 summing to 4 I: complements of the
    icosahedron's 6 diagonal lines.  (p,q,a,b) = (3,6,4,2) -- b does NOT divide p."""
    phi = 0.5 * (1 + np.sqrt(5.0))
    us = [(0,1,phi),(0,1,-phi),(1,phi,0),(1,-phi,0),(phi,0,1),(-phi,0,1)]
    A = np.zeros((6,3,3))
    for k,u in enumerate(us):
        u = np.array(u,float); A[k] = np.eye(3) - np.outer(u,u)/(u@u)
    return A

rows = []
# commuting, b=2, p odd
for nm, E, p in [('K_5 (a=4,b=2)', *complete_graph(5)),
                 ('K_7 (a=6,b=2)', *complete_graph(7)),
                 ('circ(9,[1,2]) a=4', *circulant(9,[1,2])),
                 ('C_9^2? circ(9,[1,3])', *circulant(9,[1,3]))]:
    blocks = edges_to_blocks(E); q=len(blocks); a = 2*q//p
    if not check_biregular(blocks,p,a,2): continue
    rows.append((nm,p,q,a,2,mu_from_blocks(blocks,p)))
# Fano / Heawood, b=3, p=7
lines = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
rows.append(('Fano/Heawood (3,3)',7,7,3,3,mu_from_blocks(lines,7)))
rows.append(('Fano doubled (6,3)',7,14,6,3,mu_from_blocks(lines*2,7)))
# icosahedral noncommuting, p=3 b=2
A = icosahedral()
mu_ico = [Fraction(x).limit_denominator(10**10) for x in mcp(A)]
rows.append(('icosahedral NC (4,2)',3,6,4,2,mu_ico))

print("%-22s %3s %3s %3s %3s | %-3s %-6s | %-8s %-9s %-9s %-9s" %
      ("family","p","q","a","b","m","kap1", "psi0^(m)?","t*(m)","t*/b","t* m/p"))
for nm,p,q,a,b,mu in rows:
    m = p//b
    ok = rr_at(mu,p,b,m,Fraction(b))
    ts,sat = tstar(mu,p,b,m,tmax=Fraction(4*b))
    print("  %-22s %3d %3d %3d %3d | %-3d %6.3f | %-8s %9.5f %9.4f %9.4f%s"
          % (nm,p,q,a,b,m,m*b/p, ok, ts, ts/b, ts*m/p, "  (sat)" if sat else ""))
    sys.stdout.flush()
print()
print("For comparison, the same quantity on b | p families (m = p/b, kap1 = 1):")
for nm, E, p in [('K_4 (a=3,b=2)', *complete_graph(4)),
                 ('K_6 (a=5,b=2)', *complete_graph(6)),
                 ('Petersen (a=3,b=2)', *petersen())]:
    blocks = edges_to_blocks(E); q=len(blocks); a=2*q//p
    mu = mu_from_blocks(blocks,p); m=p//2
    ok = rr_at(mu,p,2,m,Fraction(2)); ts,sat = tstar(mu,p,2,m,tmax=Fraction(8))
    print("  %-22s %3d %3d %3d %3d | %-3d %6.3f | %-8s %9.5f %9.4f %9.4f"
          % (nm,p,q,a,2,m,m*2/p,ok,ts,ts/2,ts*m/p))
