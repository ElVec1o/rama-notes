"""Is p_k <= (m/2) W_{2k} true for the plane class?  Falsify first.

W_{2k} is the number of closed walks of length 2k from a root of the a-regular tree. For
locally tree-like a-regular graphs p_k = (m/2) W_{2k} exactly, so the bound is sharp there. The
question is whether it survives on NONCOMMUTING plane families, where the classical path-tree
argument is unavailable. If it does, it removes the dimension restriction at every rung at once.

FROZEN BEFORE THE DATA:
  P16. p_k <= (m/2) W_{2k} for every weighted 2-plane family with Adj(A) <= aI, at every k.

A single family with ratio above one refutes it, and the size of the excess says what the true
bound looks like.
"""
import os, sys, math, itertools
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
from scipy.optimize import nnls
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode
rng=np.random.default_rng(7)

def tree_walks(a, kmax):
    """W_{2k}: closed walks of length 2k from the root of the a-regular tree, by DP on distance."""
    out=[]
    for k in range(1,kmax+1):
        L=2*k
        cur={0:1.0}
        for _ in range(L):
            nxt={}
            for d,v in cur.items():
                if d==0: nxt[1]=nxt.get(1,0.0)+a*v
                else:
                    nxt[d-1]=nxt.get(d-1,0.0)+v
                    nxt[d+1]=nxt.get(d+1,0.0)+(a-1)*v
            cur=nxt
        out.append(cur.get(0,0.0))
    return out

def moments_from_frames(frames,c,m):
    rmax=m//2; M=[0.0]*(rmax+1); M[0]=1.0
    q=len(frames)
    for r in range(1,rmax+1):
        if r>q: break
        tot=0.0
        for T in itertools.combinations(range(q),r):
            C=np.hstack([frames[k] for k in T]); G=C.T@C
            d=np.linalg.det(G)
            if d>1e-14: tot+=float(np.prod([c[k] for k in T]))*d
        M[r]=tot
    return M

def pks(M,kmax):
    p=[]
    for k in range(1,kmax+1):
        s=0.0
        for i in range(1,k): s+=(-1)**(i-1)*(M[i] if i<len(M) else 0.0)*p[k-i-1]
        s+=(-1)**(k-1)*k*(M[k] if k<len(M) else 0.0)
        p.append(s)
    return p

def tight_general(m,q,a):
    frames=[]
    for _ in range(q):
        B,_=np.linalg.qr(rng.standard_normal((m,2))); frames.append(B)
    iu=np.triu_indices(m)
    w=np.array([1.0 if i==j else math.sqrt(2.0) for i,j in zip(*iu)])
    A=np.stack([(B@B.T)[iu] for B in frames],axis=1)
    c,_=nnls(A*w[:,None],(a*np.eye(m))[iu]*w)
    S=sum(ci*(B@B.T) for ci,B in zip(c,frames))
    return (frames,c) if np.abs(S-a*np.eye(m)).max()<1e-7 else None

print("P16 (frozen): p_k <= (m/2) W_2k for every weighted 2-plane family with Adj(A) <= aI.\n")
print(f"{'kind':>11}{'m':>4}{'a':>4}" + "".join(f"{f'k={k}':>10}" for k in (1,2,3,4,5))
      + f"{'worst':>9}")
worst_all=0.0
for a in quickmode.few((3,4)):
    W=tree_walks(a,6)
    # coordinate: random a-regular graphs
    import networkx as nx
    for m in quickmode.few((8,10,12)):
        if (a*m)%2: continue
        G=nx.random_regular_graph(a,m,seed=int(rng.integers(1<<30)))
        frames=[]
        for (u,v) in G.edges():
            B=np.zeros((m,2)); B[u,0]=1.0; B[v,1]=1.0; frames.append(B)
        M=moments_from_frames(frames,np.ones(len(frames)),m)
        kk=min(5,m//2); p=pks(M,kk)
        rat=[p[k-1]/((m/2)*W[k-1]) for k in range(1,kk+1)]
        worst_all=max(worst_all,max(rat))
        print(f"{'coordinate':>11}{m:>4}{a:>4}"
              + "".join(f"{(rat[k-1] if k<=kk else float('nan')):>10.4f}" for k in (1,2,3,4,5))
              + f"{max(rat):>9.4f}")
    for m in quickmode.few((6,8)):
        got=None
        for q in (3*m*(m+1)//2, 5*m*(m+1)//2):
            for _ in range(6):
                r=tight_general(m,q,float(a))
                if r: got=r; break
            if got: break
        if not got:
            print(f"{'general':>11}{m:>4}{a:>4}   no exact tight frame"); continue
        frames,c=got
        M=moments_from_frames(frames,c,m)
        kk=min(5,m//2); p=pks(M,kk)
        rat=[p[k-1]/((m/2)*W[k-1]) for k in range(1,kk+1)]
        worst_all=max(worst_all,max(rat))
        print(f"{'general':>11}{m:>4}{a:>4}"
              + "".join(f"{(rat[k-1] if k<=kk else float('nan')):>10.4f}" for k in (1,2,3,4,5))
              + f"{max(rat):>9.4f}")
print(f"\n  worst ratio over everything tested: {worst_all:.4f}")
# Rule 7: the verdict may not outrun its coverage. This script sweeps small m only, where no
# excess appears; the refutation lives at larger m and is the business of code/p16verify.py.
# Saying "SURVIVES" without that qualification made the shipped baseline read as contradicting
# the abstract, which reports the refutation.
if worst_all > 1.0 + 1e-9:
    print("  P16 IS FALSE: some family exceeds the tree bound")
else:
    print(f"  no excess over the configurations swept here (worst {worst_all:.4f}); this sweep is")
    print("  small-m only and does not reach the refuting range. See code/p16verify.py.")
