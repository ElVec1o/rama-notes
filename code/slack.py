"""Where is the coupled bound lossy?  Measure the slack in each step, do not guess.

The fixed-point condition fails on part of the gap for several families, while the invariant is
measured to hold throughout.  So at least one of the two bounds is slack.  For every path-tree
vertex, at a lambda where the fixed point fails, this compares:

  left-type vertex with k children:  actual F  against  kappa(k) = lam + k/m
  right-type vertex:                 actual |F| against  m

using the largest m for which the closure condition still holds at the largest lambda where it
does.  Whichever comparison carries the bulk of the slack is the step to sharpen; the other is
already tight and sharpening it would gain nothing.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pathratio import small_biregular

def fixed_m(D,K,lam,iters=20000):
    m=1e6
    for _ in range(iters):
        nm=min(j/(lam+(j-D)/m)-lam for j in range(D,K+1))
        if nm<=1e-12: return None
        if abs(nm-m)<1e-14: return nm
        m=nm
    return m

def scan(d,q,r,lam):
    m_,rr,adj=small_biregular(d,q,r)
    L=[];R=[];cnt=[0]
    def rec(v,vis):
        cnt[0]+=1
        if cnt[0]>400000: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        cf=[rec(u,vis|{u}) for u in kids]
        F=lam-sum(1.0/x for x in cf)
        (R if v>=m_ else L).append((len(kids),F))
        return F
    rec(0,{0})
    return m_+rr,L,R

print("Slack in each half of the coupled bound, at a lambda where the fixed point FAILS\n")
print(f"{'(d,q,r)':>11}{'lam/g':>7}{'m used':>9}{'left: max F/kappa':>19}"
      f"{'right: min |F|/m':>18}")
for (d,q,r) in ((3,6,4),(3,9,4),(3,12,4)):
    g=math.sqrt(q-1)-math.sqrt(d-1); D=q-r; K=q-1
    # largest lambda where the fixed point still exists, then push past it
    lo=0.0
    for i in range(1,1001):
        if fixed_m(D,K,i/1000*g) is not None: lo=i/1000
        else: break
    for frac in (lo, min(0.99, lo+0.2)):
        lam=frac*g
        m=fixed_m(D,K,lam)
        if m is None:
            m=fixed_m(D,K,lo*g)          # reuse the last admissible m
        try: n,Lv,Rv=scan(d,q,r,lam)
        except RuntimeError: print(f"{f'({d},{q},{r})':>11} too large"); continue
        kap=lambda k: lam+k/m
        lratio=max(F/kap(k) for k,F in Lv)
        rratio=min(abs(F)/m for k,F in Rv)
        print(f"{f'({d},{q},{r})':>11}{frac:>7.2f}{m:>9.4f}{lratio:>19.4f}{rratio:>18.4f}")
print("\n  A left ratio near 1 means kappa is tight; well below 1 means the LEFT bound is slack.")
print("  A right ratio near 1 means m is tight; well above 1 means the RIGHT bound is slack.")
