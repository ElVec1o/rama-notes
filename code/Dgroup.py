"""Dgroup.py -- the suggested CONSTRUCTION is invalid.  Explicit counterexample.

The construction claims: if G is a parallel class (sum_{k in G} P_k = I_p, so
|G| = m = p/b), then conditioning on G and averaging the rest gives
        mu[P_1..P_q]  =  psi_0  box_p  mu[{P_k}_{k not in G}]        (*)
because sum_{k in G} w_k w_k^T = b Q deterministically with chi[bQ] = psi_0.

The gap: box_p is  E_{Haar U} chi[A + U B U^T].  Under the randomisation, Q is
the projection onto span(u_1..u_m) with u_k a uniform unit vector of range(P_k);
the ranges are ORTHOGONAL, so that law is supported on an m-dimensional set of
m-planes, not the (m(p-m))-dimensional Grassmannian.  chi[bQ] is deterministic,
but bQ is NOT orthogonally invariant, and box_p needs the latter.

MINIMAL COUNTEREXAMPLE (m >= 2, any b >= 2).  Take the parallel class
P_1..P_m (ranges V_1..V_m) and put Y = c P_1, realised as c times a rank-one
decomposition of P_1.  Then bQ + Y is block diagonal, block 1 has eigenvalues
b+c and c (b-1 times), the others b and 0 (b-1 times) -- DETERMINISTIC:
        LHS of (*)  =  (x-b-c)(x-c)^{b-1} [ (x-b) x^{b-1} ]^{m-1}.
The right side is a genuine Haar average and differs.
"""
from fractions import Fraction
import sys
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import numpy as np
from Dclaim import boxp, poly_from_roots, psi0, mu_multilinear_exact

def blockproj(p, idx):
    M = [[Fraction(0)]*p for _ in range(p)]
    for i in idx: M[i][i] = Fraction(1)
    return M

print("=" * 100)
print("Is  mu[parallel class , rest]  ==  psi_0 box_p mu[rest] ?")
print("=" * 100)
for (b, m, c) in [(2,2,1),(2,2,2),(2,3,1),(3,2,1),(2,2,Fraction(1,2)),(4,2,1)]:
    p = b*m
    G = [blockproj(p, range(k*b,(k+1)*b)) for k in range(m)]     # parallel class
    # Y = c * P_1 as c * (rank-one pieces)
    rest = []
    for i in range(b):
        M = [[Fraction(0)]*p for _ in range(p)]
        M[i][i] = Fraction(c)
        rest.append(M)
    lhs = mu_multilinear_exact(G + rest, p)
    murest = mu_multilinear_exact(rest, p)
    rhs = boxp(psi0(p, b), murest, p)
    pred = poly_from_roots([Fraction(b)+Fraction(c)] + [Fraction(c)]*(b-1)
                           + ([Fraction(b)] + [Fraction(0)]*(b-1))*(m-1))
    print("  b=%d m=%d p=%d c=%s" % (b,m,p,c))
    print("     mu[class,rest]        = %s" % [str(x) for x in lhs])
    print("     closed form predicted = %s   MATCH=%s" %
          ([str(x) for x in pred], pred==lhs))
    print("     psi_0 box_p mu[rest]  = %s" % [str(x) for x in rhs])
    print("     ==> construction VALID: %s\n" % (lhs == rhs))
