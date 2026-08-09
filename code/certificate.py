"""Closing the certificate: the constants solve a fixed point, and it is the tree fixed point.

Setting a = lambda (the leaf value), B = lambda + (d-1)/c from left_step and c = k0/B - lambda
from right_step, where k0 is the least number of children at a right-type path-tree vertex,
eliminates c and gives a closed quadratic for B:

    lambda B^2 - B (k0 + lambda^2 - d + 1) + lambda k0 = 0.

Three things to check, and they decide whether the route closes.

 1. The discriminant (k0 + lambda^2 - d + 1)^2 - 4 lambda^2 k0 is positive inside the gap and
    vanishes exactly at the edge lambda = g. Derived: with s = sqrt(d-1), t = sqrt(q-1),
    k0 = q-1 = t^2 and lambda = t-s, one has q-d+lambda^2 = 2t(t-s), so the discriminant is
    4t^2(t-s)^2 - 4(t-s)^2 t^2 = 0. A certificate that degenerates exactly at the gap edge is
    the right object; one that degenerates early is not.
 2. The smaller root B should equal the universal cover's cavity fixed point F_d, since the
    path tree tracks it.
 3. k0 in practice: measure the least number of children at a right-type vertex over actual
    path trees, and compare with the k0 the quadratic needs, which is k0 > d - 1 - lambda^2 for
    a positive root.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pathratio import small_biregular, tree_fixed_point

def disc(d,q,lam,k0): return (k0 + lam*lam - d + 1)**2 - 4*lam*lam*k0
def Bsmall(d,q,lam,k0):
    D = disc(d,q,lam,k0)
    if D < 0: return None
    return ((k0 + lam*lam - d + 1) - math.sqrt(D))/(2*lam)

def min_children_right(adj, m, root, maxpaths=400000):
    """least number of path-tree children at a right-type (index >= m) vertex."""
    best=[10**9]; cnt=[0]
    def rec(v, vis):
        cnt[0]+=1
        if cnt[0]>maxpaths: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        if v>=m: best[0]=min(best[0],len(kids))
        for u in kids: rec(u, vis|{u})
    rec(root,{root})
    return best[0]

print("1. discriminant inside the gap and at its edge (k0 = q-1)\n")
print(f"{'(d,q)':>8}{'g':>9}" + "".join(f"{f'lam={f}g':>13}" for f in (0.25,0.5,0.9,0.99,1.0)))
for (d,q) in ((3,6),(3,9),(4,8),(5,15),(3,18)):
    g = math.sqrt(q-1)-math.sqrt(d-1)
    row=[disc(d,q,f*g,q-1) for f in (0.25,0.5,0.9,0.99,1.0)]
    print(f"{f'({d},{q})':>8}{g:>9.4f}" + "".join(f"{v:>13.3e}" for v in row))
print("\n  Positive throughout the open gap and exactly zero at the edge in every family:")
print("  the certificate degenerates precisely where the gap closes, which is the correct")
print("  behaviour and not something imposed.\n")

print("2. does the smaller root B equal the tree cavity fixed point F_d?\n")
print(f"{'(d,q)':>8}{'lam':>9}{'B from quadratic':>19}{'tree F_d':>12}{'rel err':>11}")
for (d,q) in ((3,6),(3,9),(4,8),(5,15)):
    g = math.sqrt(q-1)-math.sqrt(d-1)
    for f in (0.25,0.5,0.75):
        lam=f*g
        B=Bsmall(d,q,lam,q-1)
        fps=[p for p in tree_fixed_point(d,q,lam) if p[0]>0]
        if B is None or not fps: continue
        Fd=min(p[0] for p in fps)
        print(f"{f'({d},{q})':>8}{lam:>9.4f}{B:>19.6f}{Fd:>12.6f}{abs(B-Fd)/Fd:>11.2e}")

print("\n3. the per-vertex requirement is k > lambda*B, NOT the quadratic's root condition.")
print("   Near the gap edge B -> sqrt(q-1), so the requirement tends to")
print("   (q-1) - sqrt((d-1)(q-1)).  Measuring how often real path trees meet it.\n")
print(f"{'(d,q,r)':>11}{'n':>5}{'lam':>8}{'lam*B':>9}{'need k >':>10}"
      f"{'min k seen':>12}{'frac failing':>14}")
for (d,q,r) in ((3,6,4),(3,6,5),(3,9,4)):
    m,rr,adj = small_biregular(d,q,r)
    g = math.sqrt(q-1)-math.sqrt(d-1)
    for f in (0.5, 0.99):
        lam=f*g; B=Bsmall(d,q,lam,q-1)
        if B is None: continue
        need = lam*B
        ks=[]
        cnt=[0]
        def rec(v, vis):
            cnt[0]+=1
            if cnt[0]>400000: raise RuntimeError
            kids=[u for u in adj[v] if u not in vis]
            if v>=m: ks.append(len(kids))
            for u in kids: rec(u, vis|{u})
        try: rec(0,{0})
        except RuntimeError: print(f"{f'({d},{q},{r})':>11}  too large"); continue
        bad = sum(1 for k in ks if k <= need)
        print(f"{f'({d},{q},{r})':>11}{m+rr:>5}{lam:>8.4f}{need:>9.4f}{need:>10.4f}"
              f"{min(ks):>12}{bad/len(ks):>14.4f}")
print("\n  Where the fraction is zero the uniform certificate closes at that lambda.")
print("  Where it is not, the certificate as stated does NOT close: a right vertex with few")
print("  children is only safe because its child's ratio sits well below B, which a uniform")
print("  interval cannot express.  That is the precise defect, and it is the remaining work.")
