"""The lossy range: a depth-indexed bound, from the same alternation count.

code/slack.py locates the loss exactly. The left bound kappa is TIGHT, attained with ratio
1.0000 at every vertex measured. All the slack is on the right, where the true |F| exceeds the
uniform m by factors of 1.19 to 1.94. So the right step is what needs sharpening, and the
uniform m is what makes it blunt.

The sharpening comes from the alternation count already proved, used per depth rather than only
between a parent and its child. A self-avoiding path of l vertices ending on one side has
floor(l/2) vertices on the other. Hence, for a path of length l:

    left-type vertex:   children lie in R \\ pi, so k <= min(d-1, r - floor(l/2))
    right-type vertex:  |N(w) ∩ pi| <= |pi ∩ L| = floor(l/2), so k >= q - floor(l/2)

Both tighten as the path lengthens, and the first reaches zero, which is what forces leaves.
So instead of one constant m solving a fixed point, there are constants per depth, computed by a
finite BACKWARD recursion from the deepest level, where every vertex is a leaf of ratio lambda:

    kappa(l) = lam + Kl(l) / m(l+1),     m(l) = Kr(l) / kappa(l+1) - lam

with Kl and Kr the bounds above. This is strictly stronger than the uniform version, which is
the special case of using the worst depth everywhere.

FROZEN BEFORE THE DATA:
  P13. The depth-indexed recursion closes on strictly more of the gap than the uniform fixed
       point, in every family where the uniform one fails.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'

def uniform_m(D,K,lam,iters=20000):
    m=1e6
    for _ in range(iters):
        nm=min(j/(lam+(j-D)/m)-lam for j in range(D,K+1))
        if nm<=1e-12: return None
        if abs(nm-m)<1e-14: return nm
        m=nm
    return m

def depth_closes(d,q,r,lam,n):
    """backward recursion over path length l = n down to 1."""
    D=q-r
    kap={}; m={}
    kap[n+1]=lam; m[n+1]=float('inf')
    for l in range(n, 0, -1):
        half=l//2
        Kl=max(0, min(d-1, r-half))          # children of a left-type vertex
        Kr=max(D, q-half)                    # children of a right-type vertex, lower bound
        Kr=min(Kr, q-1)
        mv = m.get(l+1, float('inf'))
        kap[l] = lam + (Kl/mv if mv!=float('inf') and Kl>0 else 0.0)
        kp = kap.get(l+1, lam)
        if kp <= 0: return False
        m[l] = Kr/kp - lam if Kr>0 else -1.0
        if m[l] <= 0 and Kr>0: return False
    return True

print("P13: the depth-indexed recursion closes on strictly more of the gap.\n")
print(f"{'(d,q,r)':>11}{'n':>5}{'uniform closes to':>20}{'depth-indexed closes to':>26}{'gain':>8}")
for (d,q,r) in ((3,6,4),(3,6,5),(3,9,4),(3,12,4),(4,8,4),(4,12,4),(5,10,4)):
    if (r*q)%d: continue
    m_=(r*q)//d; n=m_+r
    g=math.sqrt(q-1)-math.sqrt(d-1); D=q-r; K=q-1
    u=0.0
    for i in range(1,1001):
        if uniform_m(D,K,i/1000*g) is not None: u=i/1000
        else: break
    dpt=0.0
    for i in range(1,1001):
        if depth_closes(d,q,r,i/1000*g,n): dpt=i/1000
        else: break
    print(f"{f'({d},{q},{r})':>11}{n:>5}{f'{u:.0%} of g':>20}{f'{dpt:.0%} of g':>26}"
          f"{f'{dpt-u:+.0%}':>8}")
print("\n  A positive gain column means the depth-indexed bound recovers part of the range the")
print("  uniform fixed point could not reach, using no new mathematics beyond the alternation")
print("  count already proved in PathCount.")
