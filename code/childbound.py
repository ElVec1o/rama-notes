"""A10': does a heavily blocked vertex carry small child ratios?

The right step needs sum_j 1/F_{u_j} > lambda at a right-type path-tree vertex w with k
children.  The uniform bound F_u <= B gives k/B > lambda, which fails when k is small.  But such
a w is safe in practice, and the reason should be structural: w has few children because the
path pi already contains most of N(w), and a path long enough to do that also blocks the
children.

The exact requirement, for k children, is that the worst child ratio satisfy
    max_j F_{u_j}  <  k / lambda        (sufficient, since then sum 1/F_j > k/(k/lambda) = lambda)
and for k = 1 that reads F_u < 1/lambda.

This measures, for every right-type path-tree vertex, its child count k against the largest
child ratio it actually carries, and against the threshold k/lambda.  The output says whether
the needed lemma is true and how much room it has.

Left-type ratios obey F_u = lambda + sum over u's children of 1/|F|, so F_u = lambda exactly
when u has no children.  The lemma to prove is therefore about how blocking propagates from w
to its children.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pathratio import small_biregular

def scan(d,q,r,lam,maxpaths=600000):
    m,rr,adj = small_biregular(d,q,r)
    rows=[]; cnt=[0]
    def rec(v, vis):
        cnt[0]+=1
        if cnt[0]>maxpaths: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        childF=[rec(u, vis|{u}) for u in kids]
        F = lam - sum(1.0/x for x in childF)
        if v>=m:
            rows.append((len(kids), F, max(childF) if childF else None,
                         min(childF) if childF else None))
        return F
    rec(0,{0})
    return m+rr, rows

print("A10': child count k at a right-type vertex against the largest child ratio it carries\n")
for (d,q,r) in ((3,6,5),(3,6,4),(3,9,4)):
    g = math.sqrt(q-1)-math.sqrt(d-1)
    for f in (0.99,):
        lam=f*g
        try: n,rows = scan(d,q,r,lam)
        except RuntimeError:
            print(f"({d},{q},{r}) path tree too large"); continue
        print(f"=== ({d},{q})-biregular n={n}, lambda={lam:.4f} (0.99 g), 1/lambda={1/lam:.4f}")
        print(f"{'k':>4}{'count':>8}{'max child F':>14}{'threshold k/lam':>17}"
              f"{'slack':>10}{'max F_w':>10}")
        bad=0
        for k in sorted({t[0] for t in rows}):
            sel=[t for t in rows if t[0]==k]
            mx=max(t[2] for t in sel if t[2] is not None) if any(t[2] is not None for t in sel) else None
            thr=k/lam if k>0 else float('nan')
            mw=max(t[1] for t in sel)
            slack = (thr-mx) if mx is not None else float('nan')
            if mx is not None and mx>=thr: bad+=len(sel)
            print(f"{k:>4}{len(sel):>8}"
                  f"{(f'{mx:.4f}' if mx is not None else '-'):>14}{thr:>17.4f}"
                  f"{slack:>10.4f}{mw:>10.4f}")
        print(f"    vertices where the child bound is violated: {bad}")
        print(f"    max F_w over ALL right vertices: {max(t[1] for t in rows):.4f} "
              f"(must be < 0)\n")
print("If the slack column is positive for every k, the lemma 'max child ratio < k/lambda'")
print("holds on these path trees and is the statement to prove.  The k = 1 row is the binding")
print("one, since that is where the uniform certificate failed.")
