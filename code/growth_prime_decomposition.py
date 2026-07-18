#!/usr/bin/env python3
"""C''': c=infinity reduced to independent single-prime problems.
a(n) >= perm(gcd_P) (monotonicity); gcd_P = P-smooth part of gcd. The entropy
lower bound for gcd_P is ADDITIVE over primes -- prime p contributes ~ (log2)/p
to the log-rate -- so the rate ~ (log2) sum_{p<=P} 1/p diverges (Mertens)."""
import math, numpy as np
from sympy import primerange
def vp(x,p):
    v=0
    while x%p==0: x//=p; v+=1
    return v
def gcdP(n,P):
    M=np.ones((n,n))
    for pi in primerange(2,P+1):
        vv=np.array([vp(i+1,pi) for i in range(n)])
        M*=pi**np.minimum.outer(vv,vv)
    return M
def rate(M,it=4000):
    n=len(M); x=y=np.ones(n)
    for _ in range(it): x=1.0/(M@y); y=1.0/(M.T@x)
    w=x[:,None]*M*y[None,:]
    with np.errstate(divide='ignore'):
        F=np.sum(w*np.log(M))-np.sum(np.where(w>0,w*np.log(w),0.0))
    return math.exp(F/n)/n
if __name__=="__main__":
    n=600; prev=0.0
    print("P | entropy-bound rate | log-rate increment (per new prime) | increment*p")
    for P in [1,2,3,5,7,11,13,30,100,600]:
        r=rate(gcdP(n,P)); lr=math.log(r)
        ps=list(primerange(2,P+1))
        print(f"{P:4d} | {r:.4f} | {lr-prev:.4f} | (last p) ")
        prev=lr
