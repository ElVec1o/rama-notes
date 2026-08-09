"""Can a single graph have 2 <= deg <= 3 and still violate Conjecture 10?

Both candidate repairs are dead, but by different constructions: the pendant-cycle family has
min degree two and maximum degree eleven, the binary-skeleton family has maximum degree three
and a pendant leaf. This asks for both at once, which is the cleanest possible class:

    every vertex of degree two or three.

Construction: a rooted binary skeleton whose internal vertices have degree three, and whose
leaves ARE vertices of an attached cycle C_m. Then skeleton internal vertices have degree
three, the attachment vertex has degree three (parent plus two cycle neighbours), every other
cycle vertex has degree two, and the skeleton root has degree two. No leaves anywhere.

mu_G by the same rooted pair recursion, with the cycle supplying
(A, B) = (mu_{C_m}, mu_{P_{m-1}}) at its attachment vertex.
"""
import sys, math, time, sympy as sp
sys.path.insert(0, 'code')
x = sp.Symbol('x')

def mu_brute(nv, elist):
    m=len(elist); cnt={}
    for bits in range(1<<m):
        used,ok,k=set(),True,0
        b,t=bits,0
        while b:
            if b&1:
                a,c=elist[t]
                if a in used or c in used: ok=False; break
                used.add(a); used.add(c); k+=1
            b>>=1; t+=1
        if ok: cnt[k]=cnt.get(k,0)+1
    return sum((-1)**k*c*x**(nv-2*k) for k,c in cnt.items())

def build(m, arity, depth):
    """binary (or arity-ary) skeleton; each leaf is a vertex of an attached C_m."""
    ce=[(i,(i+1)%m) for i in range(m)]
    Ac=sp.expand(mu_brute(m,ce))
    Bc=sp.expand(mu_brute(m-1,[(a-1,b-1) for a,b in ce if 0 not in (a,b)]))
    edges=[]; counter=[0]
    def place():
        off=counter[0]; counter[0]+=m
        for (a,b) in ce: edges.append((a+off,b+off))
        return Ac,Bc,off
    def rec(d):
        if d==0: return place()
        r=counter[0]; counter[0]+=1
        subs=[rec(d-1) for _ in range(arity)]
        for (_,_,rt) in subs: edges.append((r,rt))
        As=[s[0] for s in subs]; Bs=[s[1] for s in subs]
        pA=sp.prod(As)
        A=sp.expand(x*pA-sum(Bs[i]*sp.prod(As[:i]+As[i+1:]) for i in range(len(subs))))
        return A,sp.expand(pA),r
    A,B,root=rec(depth)
    return A,B,counter[0],edges

def degs(n,edges):
    d=[0]*n
    for a,b in edges: d[a]+=1; d[b]+=1
    return max(d),min(d)

def dos_ladder(n, edges, root, etas=(1e-5,1e-7,1e-9)):
    adj={i:set() for i in range(n)}
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    de=[]
    for a,b in edges: de.append((a,b)); de.append((b,a))
    idx={e:k for k,e in enumerate(de)}
    foll=[[idx[(b,c)] for c in adj[b] if c!=a] for (a,b) in de]
    h=[complex(0.0,-0.1)]*len(de); out=[]
    for eta in etas:
        z=complex(root,eta)
        for _ in range(60000):
            new=[0j]*len(de); d=0.0
            for k in range(len(de)):
                s=z
                for f in foll[k]: s-=h[f]
                v=1.0/s; d=max(d,abs(v-h[k])); new[k]=v
            h=new
            if d<1e-14: break
        acc=0.0
        for u in range(n):
            s=z
            for b in adj[u]: s-=h[idx[(u,b)]]
            acc+=(1.0/s).imag
        out.append(-acc/(math.pi*n)/eta)
    return out

def main():
    print(f"{'m':>3}{'arity':>6}{'d':>3}{'n':>5}{'Dmax':>6}{'Dmin':>6}"
          f"{'root':>10}{'DOS/eta':>24}{'verdict':>10}", flush=True)
    hits=[]
    for m in (3,4,5,6,7,8):
        for arity in (2,3):
            for depth in (2,3,4):
                A,B,n,edges = build(m,arity,depth)
                if n>140: continue
                Dm,Dn = degs(n,edges)
                co=sp.Poly(sp.expand(A),x).all_coeffs()
                while co and co[-1]==0: co.pop()
                if len(co)<2: continue
                try:
                    rts=[sp.re(r) for r in sp.Poly(co,x).nroots(n=15,maxsteps=3000)
                         if abs(sp.im(r))<1e-10 and sp.re(r)>1e-9]
                except Exception:
                    print(f"{m:>3}{arity:>6}{depth:>3}{n:>5}  root-finding failed, skipped",
                          flush=True)
                    continue
                found=False
                for r in rts:
                    lad=dos_ladder(n,edges,float(r))
                    if max(lad)<50.0:
                        hits.append((n,m,arity,depth,float(r),Dm,Dn))
                        print(f"{m:>3}{arity:>6}{depth:>3}{n:>5}{Dm:>6}{Dn:>6}"
                              f"{float(r):>10.5f}{str([f'{t:.2f}' for t in lad]):>24}"
                              f"{'GAP':>10}", flush=True)
                        found=True
                if not found:
                    print(f"{m:>3}{arity:>6}{depth:>3}{n:>5}{Dm:>6}{Dn:>6}"
                          f"{'-':>10}{'-':>24}{'in spec':>10}", flush=True)
    if hits:
        b=min(hits)
        print(f"\nsubcubic min-degree-two counterexample: n={b[0]}, C{b[1]}, arity {b[2]}, "
              f"depth {b[3]}, root {b[4]:.6f}, degrees in [{b[6]},{b[5]}]")
    else:
        print("\nnone found in this family")
    return 0

if __name__ == '__main__':
    sys.exit(main())
