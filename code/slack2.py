"""(3,6,5) is the only family the depth-indexed recursion does not close.  Where is the slack?

Same diagnostic that decided the last refinement, now against the DEPTH-INDEXED bounds.  For
every path-tree vertex, at a lambda above the 69 percent the recursion reaches, compare

    left-type at path length l:   actual F   against  kappa(l)
    right-type at path length l:  actual |F| against  m(l)

If kappa is still tight and m still slack, more is recoverable.  If both are tight, the
certificate is at its limit for this family and the failure is a property of the route, not of
the bookkeeping.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pathratio import small_biregular

def bounds(d,q,r,lam,n):
    """backward recursion; returns (kappa, m) as dicts on path length, or None if it fails."""
    D=q-r
    kap={n+1:lam}; m={n+1:float('inf')}
    for l in range(n,0,-1):
        half=l//2
        Kl=max(0,min(d-1, r-half)); Kr=min(max(D, q-half), q-1)
        mv=m.get(l+1,float('inf'))
        kap[l]=lam + (Kl/mv if mv!=float('inf') and Kl>0 else 0.0)
        kp=kap.get(l+1,lam)
        if kp<=0: return None
        m[l]= Kr/kp - lam if Kr>0 else -1.0
        if Kr>0 and m[l]<=0: return None
    return kap,m

def scan(d,q,r,lam):
    m_,rr,adj=small_biregular(d,q,r)
    L=[];R=[];cnt=[0]
    def rec(v,vis,l):
        cnt[0]+=1
        if cnt[0]>500000: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        cf=[rec(u,vis|{u},l+1) for u in kids]
        F=lam-sum(1.0/x for x in cf)
        (R if v>=m_ else L).append((l,len(kids),F))
        return F
    rec(0,{0},1)
    return m_+rr,L,R

d,q,r=3,6,5
m_=(r*q)//d; n=m_+r
g=math.sqrt(q-1)-math.sqrt(d-1)
print(f"({d},{q},{r}), n={n}, gap edge g={g:.4f}, depth-indexed recursion closes to 69% of g\n")
print(f"{'lam/g':>7}{'recursion':>12}{'left max F/kappa':>18}{'right min |F|/m':>18}"
      f"{'binding l (left)':>18}{'binding l (right)':>19}")
for frac in (0.60,0.69,0.80,0.95):
    lam=frac*g
    b=bounds(d,q,r,lam,n)
    ok = b is not None
    if not ok:
        print(f"{frac:>7.2f}{'FAILS':>12}{'n/a':>18}{'n/a':>18}{'':>18}{'':>19}")
        continue
    kap,m=b
    try: nn,Lv,Rv=scan(d,q,r,lam)
    except RuntimeError: print("too large"); break
    lr=[(F/kap[l], l) for l,k,F in Lv if l in kap and kap[l]>0]
    rr_=[(abs(F)/m[l], l) for l,k,F in Rv if l in m and m[l]>0]
    lmax=max(lr); rmin=min(rr_)
    print(f"{frac:>7.2f}{('closes' if ok else 'FAILS'):>12}{lmax[0]:>18.4f}{rmin[0]:>18.4f}"
          f"{lmax[1]:>18}{rmin[1]:>19}")
print("\n  Ratios near 1 on both sides mean the certificate is at its limit here.")
print("  A ratio well above 1 on the right means the right bound is still recoverable.")
