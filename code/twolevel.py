"""P24: does a CHILD-COUNT-AWARE certificate close the (3,6,5) defect?

The uniform right_step needs k > lambda*B, with B the worst-case bound for EVERY child. It fails
on right vertices with very few children: at (3,6,5), lambda = 0.8136, lambda*B = 1.6247, and
0.21% of right vertices have k = 1.

But B is not the right bound for those children. A left vertex with j children satisfies
F <= B_j := lambda + j/c, and B = B_{d-1} is the worst case. A right vertex with k = 1 sits where
the path tree is nearly exhausted, so its single child should itself be child-poor, giving a much
smaller B_j and hence a much weaker requirement k > lambda*B_j.

MEASURED HERE. For every right vertex, record its child count k and the child counts j of its
children, then test the refined requirement

    k > lambda * max_i B_{j_i},     B_j = lambda + j/c,

against the uniform k > lambda*B. If the refined test passes everywhere the certificate closes
and the defect is an artefact of using one interval for all left vertices.
"""
import os,sys,math
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
sys.path.insert(0,'/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from certificate import small_biregular, Bsmall

def analyse(d,q,r,frac):
    m,rr,adj = small_biregular(d,q,r)
    g = math.sqrt(q-1)-math.sqrt(d-1); lam = frac*g
    B = Bsmall(d,q,lam,q-1)
    if B is None: return None
    c = (q-1)/B - lam                      # from right_step with k0 = q-1
    if c <= 0: return None
    rows=[]; cnt=[0]
    def rec(v, vis):
        cnt[0]+=1
        if cnt[0]>400000: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        if v>=m:                                   # right-type vertex
            js=[len([w for w in adj[u] if w not in (vis|{u})]) for u in kids]
            rows.append((len(kids), js))
        for u in kids: rec(u, vis|{u})
    try: rec(0,{0})
    except RuntimeError: return 'toolarge'
    unif_bad=0; refi_bad=0; worst=None
    for k,js in rows:
        if k <= lam*B: unif_bad+=1
        Bj = max((lam + j/c) for j in js) if js else lam
        need = lam*Bj
        if k <= need:
            refi_bad+=1
            if worst is None or (k-need) < worst[0]: worst=(k-need,k,js,need)
    return dict(n=m+rr, lam=lam, B=B, c=c, uniform_need=lam*B, rows=len(rows),
                unif_bad=unif_bad, refi_bad=refi_bad, worst=worst)

print("P24 (frozen): a child-count-aware certificate closes where the uniform one fails.\n")
print(f"{'(d,q,r)':>11}{'lam':>8}{'unif need':>11}{'unif fail':>11}{'refined fail':>14}{'verdict':>10}")
for (d,q,r) in ((3,6,4),(3,6,5),(3,9,4),(3,9,5),(4,8,4)):
    for frac in (0.5,0.9,0.99):
        res=analyse(d,q,r,frac)
        if res is None: continue
        if res=='toolarge':
            print(f"{f'({d},{q},{r})':>11}  path tree too large at frac={frac}"); break
        v = 'CLOSES' if res['refi_bad']==0 else 'fails'
        print(f"{f'({d},{q},{r})':>11}{res['lam']:>8.4f}{res['uniform_need']:>11.4f}"
              f"{res['unif_bad']:>11}{res['refi_bad']:>14}{v:>10}")
        if res['refi_bad'] and res['worst']:
            d_,k,js,need = res['worst']
            print(f"{'':>11}  worst refined case: k={k}, child counts {js[:6]}, need k>{need:.4f}")
