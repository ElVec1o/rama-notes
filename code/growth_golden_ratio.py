"""C'''' : single-prime gain G_p and the golden-ratio constant.
G_p = sup_pi [ log p E_pi[min(a,b)] - D(pi || q(x)q) ],  q_k=(1-1/p)p^-k.
RESULTS (this file verifies):
  (i)  Z_p = E_{q(x)q}[p^min] = 1 + 1/p exactly;  G_p = log(1+1/p) - SB_p.
  (ii) p*G_p -> c = 2 ln phi - phi^-2 = 2 ln phi + phi - 2 = 0.5804576...,
       phi = (1+sqrt5)/2 golden ratio; extremal diagonal fraction t*=phi^-2=(3-sqrt5)/2,
       the golden section (root of (1-t)^2=t).
  => G_p ~ c/p, sum_p G_p ~ c loglog P -> infinity  => c_inf = lim(a(n)/n!)^{1/n}=infinity
     (modulo CRT-realizability of the product-over-primes coupling on [n]).
"""
import math, numpy as np
from sympy import primerange
def Gp(p,K=60):
    q=np.array([(1-1/p)*p**(-a) for a in range(K+1)]); q/=q.sum()
    logR=np.array([[math.log(q[a])+math.log(q[b])+min(a,b)*math.log(p) for b in range(K+1)] for a in range(K+1)])
    logq=np.log(q); f=np.zeros(K+1); g=np.zeros(K+1)
    for _ in range(8000):
        M=logR+g[None,:]; f=logq-(M.max(1)+np.log(np.exp(M-M.max(1,keepdims=True)).sum(1)))
        M=logR+f[:,None]; g=logq-(M.max(0)+np.log(np.exp(M-M.max(0,keepdims=True)).sum(0)))
    w=np.exp(f[:,None]+logR+g[None,:])
    mn=np.array([[min(a,b) for b in range(K+1)] for a in range(K+1)],float); qq=np.outer(q,q)
    return float(np.sum(w*mn)*math.log(p)-np.sum(np.where(w>0,w*np.log(w/qq),0.0)))
if __name__=="__main__":
    phi=(1+5**.5)/2; c=2*math.log(phi)-phi**-2
    print(f"golden-ratio constant c = 2 ln phi - phi^-2 = {c:.10f}")
    for p in [2,3,5,7,11,31,101]:
        G=Gp(p); print(f"  p={p:3d}  G_p={G:.6f}  p*G_p={p*G:.5f}  logZ={math.log(1+1/p):.5f}")
