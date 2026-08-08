"""ff_L8.py -- does an upper bound on kappa_4(rho) rescue (L)?  (brief candidate a)

LP:  minimise m4(tau) subject to  tau on [c, ab],  m1,m2,m3 forced,
     tau({c}) >= 1/b   (which forces L(tau) = c < tree edge).
Compare with m4 of the genuine rho and of chi^{boxplus(a-1)}.
An upper bound on kappa_4 rescues (L) only if every genuine m4 is strictly
below the LP value.  It is NOT: see (5,4) and (6,5).
NOTE the direction of the logic -- the atom mechanism is only SUFFICIENT for a
violation, so the true threshold is <= the LP value; that can only make the
rescue worse, never better.
"""
import sys, numpy as np
from fractions import Fraction
from scipy.optimize import linprog
sys.path.insert(0,'/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F, ff_L as X, ff_L2 as Y, ff_L4 as V

def min_m4(c, C, a, b, n=8001):
    m1,mu2,mu3 = X.forced_moments(a,b)
    M=[m1, mu2+m1**2, mu3+3*m1*mu2+m1**3]
    xs=np.linspace(c,C,n)
    A=np.vstack([np.ones(n), xs, xs**2, xs**3])
    bv=np.array([1.0]+M)
    # extra inequality:  weight at x=c  >= 1/b
    Aub=np.zeros((1,n)); Aub[0,0]=-1.0
    res=linprog(xs**4, A_eq=A, b_eq=bv, A_ub=Aub, b_ub=np.array([-1.0/b]),
                bounds=[(0,1)]*n, method='highs')
    return (res.fun if res.success else None)

print("="*104)
print("[K4LP] smallest 4th moment compatible with a violation, vs genuine families")
print("="*104)
print("  %-8s %-10s %-13s %-13s %-13s"%("(a,b)","tree lo","m4 needed","m4 of chi^{a-1}","genuine m4 range"))
# genuine families' m4
gen={}
for nm,p,q,a,b,e in Y.families():
    rho=Y.deconv(e,Y.psi0(p,b),p); r=np.roots(F.poly_from_signed_e(rho,p))
    if float(np.max(np.abs(r.imag)))>1e-7: continue
    gen.setdefault((a,b),[]).append(float(np.mean(np.sort(r.real)**4)))
specs=[]
for seed in (1,2,3,4,5,6):
    specs += [(6,8,4,3,seed),(9,12,4,3,seed),(12,16,4,3,seed),(6,10,5,3,seed),
              (9,15,5,3,seed),(6,12,6,3,seed),(8,12,6,4,seed),(8,10,5,4,seed),
              (12,15,5,4,seed),(10,12,6,5,seed),(12,18,6,4,seed),(4,6,3,2,seed),
              (6,9,3,2,seed),(8,12,3,2,seed),(6,12,4,2,seed),(10,15,3,2,seed)]
for nm,p,q,a,b,e,nc in V.rand_families(specs):
    rho=Y.deconv(e,Y.psi0(p,b),p); r=np.roots(F.poly_from_signed_e(rho,p))
    if float(np.max(np.abs(r.imag)))>1e-7: continue
    gen.setdefault((a,b),[]).append(float(np.mean(np.sort(r.real)**4)))
import ff_L5 as Zz
for (a,b) in sorted(gen):
    lo,_=X.tree_band(a,b)
    if lo<=0: continue
    c=max(0.0, lo*0.999)
    need=min_m4(c, float(a*b), a, b)
    tgt=Zz.target_moments(a,b,4)[3]
    g=gen[(a,b)]
    print("  (%2d,%d)   %10.5f %13.4f %13.4f    [%.4f, %.4f]  (n=%d)  separated=%s"
          %(a,b,lo,(need if need else float('nan')),tgt,min(g),max(g),len(g),
            (need is not None and max(g)<need)))
