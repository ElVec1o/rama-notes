"""How small can a nonzero eigenvalue of an Aomoto tree be, given its size?

m(lambda) = min number of vertices of a tree carrying a nowhere-vanishing lambda-eigenvector.
The degree-bound chain 2c(delta-1) <= (delta-2)s + 2c <= e <= Delta*b <= Delta(c-1) used only
s >= 2c. With s >= kappa*c it gives Delta > (delta-2)*kappa + 2.

P83 (frozen):
  (a) min positive qualifying eigenvalue over all trees on n vertices is attained by a PATH.
  (b) it equals 2cos(k pi/(n+1)) for the k coprime to n+1 nearest (n+1)/2, hence is ~ pi/(n+1).
  (c) so m(lambda) >= pi/|lambda| - 1 asymptotically, and kappa grows without bound as lambda->0.
"""
import itertools, math, heapq
import numpy as np

def trees(n):
    seen=set()
    if n==1: yield np.zeros((1,1)); return
    if n==2: yield np.array([[0.,1.],[1.,0.]]); return
    for seq in itertools.product(range(n), repeat=n-2):
        deg=[1]*n
        for x in seq: deg[x]+=1
        d=deg[:]; edges=[]
        leaves=[i for i in range(n) if d[i]==1]; heapq.heapify(leaves)
        for x in seq:
            leaf=heapq.heappop(leaves); edges.append((leaf,x)); d[leaf]-=1; d[x]-=1
            if d[x]==1: heapq.heappush(leaves,x)
        u,v=[i for i in range(n) if d[i]==1]; edges.append((u,v))
        A=np.zeros((n,n))
        for a,b in edges: A[a,b]=A[b,a]=1
        key=(tuple(np.round(np.sort(np.linalg.eigvalsh(A)),9)),tuple(sorted(deg)))
        if key in seen: continue
        seen.add(key); yield A

def qualifying(A, tol=1e-7):
    n=A.shape[0]; w,V=np.linalg.eigh(A); out=[]; i=0
    while i<n:
        j=i
        while j+1<n and abs(w[j+1]-w[i])<1e-8: j+=1
        if np.linalg.norm(V[:,i:j+1],axis=1).min()>tol: out.append(float(w[i]))
        i=j+1
    return out

print("min positive qualifying eigenvalue over all trees on n vertices\n")
print(f"{'n':>3}{'trees':>7}{'min pos lambda':>16}{'path predicts':>16}{'attained by path':>18}{'pi/(n+1)':>11}")
for n in range(2, 10):
    best=None; bestA=None; ntrees=0
    for A in trees(n):
        ntrees+=1
        q=[x for x in qualifying(A) if x>1e-7]
        if q and (best is None or min(q)<best-1e-12):
            best=min(q); bestA=A.copy()
    ks=[k for k in range(1,n+1) if math.gcd(k,n+1)==1]
    pred=min(abs(2*math.cos(k*math.pi/(n+1))) for k in ks)
    P=np.zeros((n,n))
    for i in range(n-1): P[i,i+1]=P[i+1,i]=1
    ispath = bestA is not None and abs(min(x for x in qualifying(P) if x>1e-7)-best)<1e-9
    print(f"{n:>3}{ntrees:>7}{best:>16.9f}{pred:>16.9f}{str(ispath):>18}{math.pi/(n+1):>11.5f}")

print("\nconsequence: kappa(lambda) = min tree size, and the degree bound Delta > (delta-2)kappa + 2")
print(f"{'|lambda| <':>12}{'kappa >=':>10}{'delta=3 gives Delta >':>23}{'delta=4 gives Delta >':>23}")
for lam, kap in [(2.0,2),(1.0,4),(0.62,6),(0.45,8),(0.31,10)]:
    print(f"{lam:>12.2f}{kap:>10}{(3-2)*kap+2:>23}{(4-2)*kap+2:>23}")
