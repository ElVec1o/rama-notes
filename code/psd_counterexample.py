"""EXPLICIT counterexample to Conjecture X in the *general PSD* class
(rank exactly b, sum = aI, but NOT projections -- traces are not b).

Take p = 2, q = 3, a = 3, b = 2  (so q*b = 6 = p*a).
   M_1 = M_2 = u/2 * I_2 ,  M_3 = (3-u) * I_2 ,   0 < u < 3.
Each M_k is positive definite, hence has rank exactly b = 2, and
   M_1 + M_2 + M_3 = 3 I_2 = a I.
Then  mu[M_1,M_2,M_3](y) = y^2 - 6 y + E_2  with
   E_2 = sum_{j<k} [ tr M_j tr M_k - tr(M_j M_k) ]
       = u^2/2 + 2 u (3-u)  =  6u - 3u^2/2,
so the roots are 3 +- sqrt(9 - E_2), and they leave the band
   [(sqrt2-1)^2, (sqrt2+1)^2] = 3 +- 2*sqrt(2)
as soon as E_2 < 1, i.e. u < 2 - sqrt(2/3)*... (numerically u < 0.17712).
Direct-summing this 2x2 block with itself gives p=4, q=6, a=3, b=2, etc.
"""
import numpy as np
from fractions import Fraction
from mixed_char_poly import (mixed_char_poly, mixed_char_poly_exact,
                             mixed_char_poly_sympy, band, roots_of)

print("EXACT rational check, p=2 q=3 (a,b)=(3,2), u = 1/10:")
u = Fraction(1, 10)
M = [[[u / 2, 0], [0, u / 2]],
     [[u / 2, 0], [0, u / 2]],
     [[3 - u, 0], [0, 3 - u]]]
c_ex = mixed_char_poly_exact(M)
c_sym = mixed_char_poly_sympy(M)
print("   mu coefficients (subset formula) :", [str(x) for x in c_ex])
print("   mu coefficients (sympy brute)    :", [str(x) for x in c_sym])
lo, hi = band(3, 2)
r, _ = roots_of([float(x) for x in c_ex])
print(f"   roots = {r}   band = [{lo:.9f},{hi:.9f}]")
print(f"   -> lower violation {lo - r.min():+.9f}, upper violation {r.max()-hi:+.9f}")
print(f"   ranks: {[np.linalg.matrix_rank(np.array(Mi,dtype=float)) for Mi in M]}, "
      f"traces: {[float(sum(Mi[i][i] for i in range(2))) for Mi in M]}")

print()
print("sweep in u (p=2,q=3,a=3,b=2):  E_2 = 6u - 3u^2/2, roots 3 +- sqrt(9-E_2)")
for uu in [1.0, 0.5, 0.3, 0.17712, 0.1, 0.01, 0.001]:
    Mf = np.array([np.eye(2) * uu / 2, np.eye(2) * uu / 2, np.eye(2) * (3 - uu)])
    c = mixed_char_poly(Mf)
    r = np.sort(np.roots(c).real)
    print(f"   u={uu:<9g} E_2={c[2]:9.6f}  roots=({r[0]:.6f},{r[1]:.6f})  "
          f"lo-margin {r[0]-lo:+.6f}  hi-margin {hi-r[1]:+.6f}")

print()
print("direct sum of the u=0.1 block with itself -> p=4, q=6, (a,b)=(3,2):")
blk = [np.eye(2) * 0.05, np.eye(2) * 0.05, np.eye(2) * 2.9]
fam = []
for k in range(3):
    Z = np.zeros((4, 4)); Z[:2, :2] = blk[k]; fam.append(Z)
for k in range(3):
    Z = np.zeros((4, 4)); Z[2:, 2:] = blk[k]; fam.append(Z)
fam = np.array(fam)
print("   sum - 3I residual:", np.linalg.norm(fam.sum(0) - 3 * np.eye(4)))
print("   ranks:", [np.linalg.matrix_rank(F) for F in fam])
c = mixed_char_poly(fam)
r = np.sort(np.roots(c).real)
print(f"   roots = {r}")
print(f"   band = [{lo:.6f},{hi:.6f}]  ->  lower violation {lo-r.min():+.6f}, "
      f"upper violation {r.max()-hi:+.6f}")
