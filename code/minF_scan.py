"""#4: what a non-alternating invariant would have to look like.

P28 says the path tree has no eigenvalue in the gap, so no F_v vanishes there and the ratio
method's target is true. The sign-alternating certificate fails near the gap edge because the
signs themselves stop alternating once lambda^2 >= Delta. So the invariant must not be about
signs. The natural candidate is a quantitative one: a lower bound on |F_v|.

Measured here across the gap: min |F_v| over the whole path tree, the sign split, and whether the
minimum is attained at a leaf (where F = lambda exactly, so the bound cannot beat lambda).
"""
import os,sys,math
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
sys.setrecursionlimit(100000)
sys.path.insert(0,'/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from certificate import small_biregular

def scan(adj, root, lam, cap=1_500_000):
    st={'neg':0,'tot':0,'min':float('inf'),'argleaf':False,'minneg':float('inf'),
        'minpos':float('inf')}
    def rec(v, visited):
        st['tot']+=1
        if st['tot']>cap: raise RuntimeError
        s=0.0; nk=0
        for u in adj[v]:
            if u in visited: continue
            nk+=1
            fu=rec(u, visited|{u})
            s+=1.0/fu
        f=lam-s
        a=abs(f)
        if a<st['min']:
            st['min']=a; st['argleaf']=(nk==0)
        if f<0:
            st['neg']+=1; st['minneg']=min(st['minneg'],a)
        else:
            st['minpos']=min(st['minpos'],a)
        return f
    try: rec(root,{root})
    except RuntimeError: return None
    return st

print("min |F_v| over the path tree, across the gap.\n")
print(f"{'(d,q,r)':>10}{'frac':>7}{'lam':>8}{'|P|':>9}{'min|F|':>10}{'min|F|/lam':>12}"
      f"{'at leaf':>9}{'%neg':>7}")
for (d,q,r) in ((3,6,4),(3,6,5),(3,9,4)):
    m,rr,adj=small_biregular(d,q,r)
    g=math.sqrt(q-1)-math.sqrt(d-1)
    for frac in (0.1,0.3,0.5,0.7,0.9,0.99):
        lam=frac*g
        st=scan(adj,0,lam)
        if st is None:
            print(f"{f'({d},{q},{r})':>10}{frac:>7.2f}   cap"); continue
        print(f"{f'({d},{q},{r})':>10}{frac:>7.2f}{lam:>8.4f}{st['tot']:>9}{st['min']:>10.5f}"
              f"{st['min']/lam:>12.5f}{str(st['argleaf']):>9}"
              f"{100*st['neg']/st['tot']:>7.1f}", flush=True)
print("\n  If min|F| never falls below lambda, the invariant is `every ratio has modulus at")
print("  least the leaf value', which is sign-free and would close the whole gap.")
