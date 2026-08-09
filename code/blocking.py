"""A10' reduced: blocking propagates from a vertex to its children, by an alternation count.

CLAIM (derived, then tested here). Let pi be a self-avoiding path in a (d,q)-biregular bipartite
graph with left side L (degree d, size m) and right side R (degree q, size r), ending at
w in R, and let k = |N(w) \\ pi| be w's child count in the path tree. Then for every child u:

    k >= q - r                          every right-type vertex has at least q - r children
    k_u <= r - q + k = k - (q - r)      the child count DROPS by at least q - r each level

Derivation, three steps, each elementary:
  1. The q - k blocked neighbours of w all lie in L, so |pi ∩ L| >= q - k.
  2. pi alternates and ends in R, so |pi ∩ R| >= |pi ∩ L| >= q - k.  Combined with |pi ∩ R| <= r
     this already forces k >= q - r.
  3. N(u) lies in R, and an unblocked neighbour of u must avoid pi ∩ R, so
     k_u <= r - |pi ∩ R| <= r - q + k.

Consequence, and it is the one the certificate needs: when k attains its minimum q - r, the
bound gives k_u <= 0, so every child is a LEAF with ratio exactly lambda. That is precisely the
pattern measured in code/childbound.py, where the largest child ratio at the minimum child count
equalled lambda to the last digit in every family.

This file tests both inequalities on every right-type path-tree vertex, which is the
falsification pass owed before the statement is used.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pathratio import small_biregular

def check(d,q,r,maxpaths=600000):
    m,rr,adj = small_biregular(d,q,r)
    stats={'n':m+rr,'vertices':0,'minK':10**9,'badK':0,'badKu':0,'maxKu_at_minK':-1,
           'worst_slack':10**9}
    cnt=[0]
    def rec(v, vis):
        cnt[0]+=1
        if cnt[0]>maxpaths: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        if v>=m:                                  # right-type vertex
            k=len(kids)
            stats['vertices']+=1
            stats['minK']=min(stats['minK'],k)
            if k < q-r: stats['badK']+=1
            for u in kids:
                ku=len([z for z in adj[u] if z not in vis|{u}])
                if ku > r-q+k: stats['badKu']+=1
                stats['worst_slack']=min(stats['worst_slack'], (r-q+k)-ku)
                if k==q-r or (q-r<=0 and k==stats['minK']):
                    stats['maxKu_at_minK']=max(stats['maxKu_at_minK'],ku)
        for u in kids: rec(u, vis|{u})
    rec(0,{0})
    return stats

print("Testing  k >= q-r  and  k_u <= k-(q-r)  on every right-type path-tree vertex\n")
print(f"{'(d,q,r)':>11}{'n':>5}{'q-r':>6}{'right vtx':>11}{'min k':>7}"
      f"{'k<q-r':>8}{'k_u>bound':>11}{'worst slack':>13}")
for (d,q,r) in ((3,6,4),(3,6,5),(3,9,4),(3,6,6),(4,8,4)):
    if (r*q)%d: continue
    try: st=check(d,q,r)
    except RuntimeError:
        print(f"{f'({d},{q},{r})':>11}  path tree too large"); continue
    print(f"{f'({d},{q},{r})':>11}{st['n']:>5}{q-r:>6}{st['vertices']:>11}{st['minK']:>7}"
          f"{st['badK']:>8}{st['badKu']:>11}{st['worst_slack']:>13}")
print("\nZero violations in both columns means the counting argument is sound as derived, and")
print("A10' reduces to it: at the minimum child count the bound forces k_u = 0, so the children")
print("are leaves of ratio exactly lambda, which is the binding case of right_step_sharp.")
