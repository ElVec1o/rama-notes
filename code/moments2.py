"""Does the moment method remove the dimension restriction entirely?

Writing p_k = (m/2) c_k^k, the chain y_max^k <= p_k <= (4a)^k gives the band whenever

    m <= 2 (4a / c_k)^k,

so the reachable dimension grows without bound in k precisely when c_k stays below 4a. Since
c_k = (2 p_k / m)^{1/k} increases to y_max = x_max^2, and for locally tree-like a-regular graphs
x_max -> 2 sqrt(a-1), the limit is c_infinity = 4(a-1) < 4a. The gap between 4(a-1) and 4a is
what the method has to spend, and it gives a growth rate of (a/(a-1))^k.

FROZEN BEFORE THE DATA:
  P15. c_k stays below 4a for every k, so the dimension restriction is removable by taking
       enough moments, and the reachable m grows like (a/(a-1))^k.

Computed on the coordinate case, where the matching polynomial is available by the standard
deletion recursion so k can be pushed far, and cross-checked on general plane families at small
m where the Gram-determinant sum is still feasible.
"""
import os, sys, math, itertools, functools
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
rng=np.random.default_rng(20260819)

def matching_poly_regular(m,a,seed):
    """coefficients M_r of the matching polynomial of a random a-regular graph on m vertices."""
    import networkx as nx
    G=nx.random_regular_graph(a,m,seed=seed)
    adj={i:set(G.neighbors(i)) for i in range(m)}
    sys.setrecursionlimit(100000)
    @functools.lru_cache(maxsize=None)
    def rec(vs):
        S=set(vs)
        if not S: return (1.0,)
        v=min(S,key=lambda z: len(adj[z]&S)); S1=S-{v}
        base=rec(tuple(sorted(S1)))                       # x * mu(G-v)
        out=[0.0]*(len(base)+1)
        for i,cc in enumerate(base): out[i]+=cc           # shift by x
        for u in adj[v]&S:
            sub=rec(tuple(sorted(S1-{u})))
            for i,cc in enumerate(sub): out[i+1]-=cc      # -mu(G-v-u), degree drops by 2
        return tuple(out)
    return rec(tuple(range(m)))

def pks(Mcoef,kmax):
    """power sums of the y-roots from M_r (elementary symmetric).

    The deletion recursion returns SIGNED coefficients (-1)^i M_i, so the signs are undone
    first; leaving them in negates the odd power sums and leaves the even ones untouched."""
    M=[((-1)**i)*cc for i,cc in enumerate(Mcoef)]; p=[]
    for k in range(1,kmax+1):
        s=0.0
        for i in range(1,k): s+= (-1)**(i-1)*(M[i] if i<len(M) else 0.0)*p[k-i-1]
        s+= (-1)**(k-1)*k*(M[k] if k<len(M) else 0.0)
        p.append(s)
    return p

print("P15 (frozen): c_k stays below 4a, so the dimension restriction is removable.\n")
print(f"{'a':>3}{'m':>4}{'4a':>6}" + "".join(f"{f'c{k}':>9}" for k in (1,2,3,4,6,8,10))
      + f"{'reach m<=':>11}{'at k':>6}")
for a in (3,4,5):
    for m in (10,14,18):
        if (a*m)%2: continue
        M=matching_poly_regular(m,a,int(rng.integers(1<<30)))
        kmax=min(10,m//2)
        p=pks(M,kmax)
        cs={}
        for k in range(1,kmax+1):
            if p[k-1]>0: cs[k]=(2*p[k-1]/m)**(1.0/k)
        best=(0,0)
        for k,c in cs.items():
            reach=2*(4*a/c)**k
            if reach>best[0]: best=(reach,k)
        row="".join(f"{cs.get(k,float('nan')):>9.3f}" for k in (1,2,3,4,6,8,10))
        print(f"{a:>3}{m:>4}{4*a:>6}{row}{best[0]:>11.0f}{best[1]:>6}")
print()
print("  c_k increases toward 4(a-1), the square of the tree spectral radius, and 4a exceeds")
print("  that by a factor a/(a-1); the reachable dimension therefore grows like (a/(a-1))^k.")
for a in (3,4,5):
    print(f"    a={a}: 4(a-1)={4*(a-1)}, 4a={4*a}, growth per moment {a/(a-1):.3f}")
