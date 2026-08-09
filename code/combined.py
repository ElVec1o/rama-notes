"""Where exactly does (3,6,5) fail, and does combining both counting bounds help?

The depth-indexed recursion uses only the depth bound on child counts,
    left-type at path length l:  k <= min(d-1, r - floor(l/2)),
and drops the parent-to-child bound of child_count_drop,
    child of a right-type vertex with k children:  k_u <= k - (q - r).
Both are proved, and both apply. Tracking the pair (depth, parent's child count) uses them
together, which is strictly stronger than either alone.

Two questions:
 1. At which path length does the depth-only recursion first fail as lambda rises past 0.69 g?
 2. Does the combined recursion reach further?
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'

def depth_only(d,q,r,lam,n,trace=False):
    D=q-r; kap={n+1:lam}; m={n+1:float('inf')}
    for l in range(n,0,-1):
        half=l//2
        Kl=max(0,min(d-1, r-half)); Kr=min(max(D, q-half), q-1)
        mv=m.get(l+1,float('inf'))
        kap[l]=lam + (Kl/mv if mv!=float('inf') and Kl>0 else 0.0)
        kp=kap.get(l+1,lam)
        if kp<=0: return (False,l,'kappa<=0') if trace else False
        m[l]= Kr/kp - lam if Kr>0 else -1.0
        if Kr>0 and m[l]<=0: return (False,l,f'm({l})={m[l]:.4f}<=0') if trace else False
    return (True,None,None) if trace else True

def combined(d,q,r,lam,n):
    """kap[l][k] : bound for a left-type vertex at length l whose PARENT had k children.
       m[l][k]   : bound for a right-type vertex at length l with k children."""
    D=q-r; K=q-1
    kap={}; m={}
    for l in range(n,0,-1):
        half=l//2
        # left-type at l, parent (right-type, length l-1) had kp children: k <= min(d-1, r-half, kp-D)
        kap[l]={}
        for kp in range(0,K+1):
            Kl=max(0,min(d-1, r-half, kp-D))
            if Kl==0: kap[l][kp]=lam; continue
            nxt=m.get(l+1)
            if nxt is None: kap[l][kp]=lam; continue
            worst=max(nxt.get(kk,-1) for kk in range(0,K+1)) if nxt else -1
            # children of this left vertex are right-type at l+1 with unknown k; use the
            # smallest admissible bound over their possible child counts
            cand=[nxt[kk] for kk in range(0,K+1) if kk in nxt and nxt[kk]>0]
            if not cand: kap[l][kp]=lam; continue
            kap[l][kp]=lam+Kl/min(cand)
        # right-type at l with k children: children are left-type at l+1 with parent k
        m[l]={}
        for k in range(0,K+1):
            if k < max(D, q-half): m[l][k]=-1; continue     # not attainable
            nxt=kap.get(l+1)
            kp = nxt[k] if (nxt and k in nxt) else lam
            if kp<=0: return False
            m[l][k]= k/kp - lam
        if all(v<=0 for v in m[l].values() if v!=-1) and any(v!=-1 for v in m[l].values()):
            return False
    return True

d,q,r=3,6,5; m_=(r*q)//d; n=m_+r
g=math.sqrt(q-1)-math.sqrt(d-1)
print(f"({d},{q},{r}) n={n} g={g:.4f}\n")
print("1. where the depth-only recursion first fails\n")
print(f"{'lam/g':>8}{'result':>10}{'first failing l':>18}{'reason':>22}")
for frac in (0.69,0.70,0.75,0.85,0.99):
    ok,l,why=depth_only(d,q,r,frac*g,n,trace=True)
    print(f"{frac:>8.2f}{('closes' if ok else 'FAILS'):>10}{(str(l) if l else '-'):>18}{(why or '-'):>22}")

print("\n2. depth-only against depth+drop combined\n")
best_d=0.0; best_c=0.0
for i in range(1,1001):
    if depth_only(d,q,r,i/1000*g,n): best_d=i/1000
    else: break
for i in range(1,1001):
    if combined(d,q,r,i/1000*g,n): best_c=i/1000
    else: break
print(f"   depth only : {best_d:.0%} of g")
print(f"   depth+drop : {best_c:.0%} of g   ({best_c-best_d:+.0%})")
