"""Adversarial search for a biregular counterexample (Rule 3: adversarially constructed).

Random sampling found nothing, but our counterexamples are highly structured, so random
sampling is the wrong instrument. This does local search over (a,b)-biregular bipartite
graphs, moving by degree-preserving edge swaps and descending on the smallest nonzero root of
mu_G, which is the quantity that must not fall below |sqrt(a-1) - sqrt(b-1)|.

A swap takes edges (a1,b1),(a2,b2) to (a1,b2),(a2,b1); it preserves both degree sequences, so
the walk stays inside the biregular class exactly.
"""
import sys, os, math, time, random
import numpy as np, sympy as sp
x = sp.Symbol('x')
CKPT='private/biregular_anneal_ckpt.txt'

def counts(nA,nB,adjA):
    size=1<<nB
    dp=np.zeros(size,dtype=np.int64); dp[0]=1
    idx=np.arange(size,dtype=np.int64)
    for i in range(nA):
        new=dp.copy()
        for bv in adjA[i]:
            bit=np.int64(1)<<np.int64(bv)
            has=(idx&bit)!=0
            new[has]+=dp[idx[has]^bit]
        if np.any(new<0): raise OverflowError
        dp=new
    pc=np.zeros(size,dtype=np.int64)
    for j in range(nB): pc+=(idx>>np.int64(j))&np.int64(1)
    return [int(dp[pc==k].sum()) for k in range(nB+1)]

def smallest_root(nA,nB,adjA):
    n=nA+nB
    m=counts(nA,nB,adjA)
    poly=sum((-1)**k*m[k]*x**(n-2*k) for k in range(len(m)))
    co=sp.Poly(poly,x).all_coeffs()
    while co and co[-1]==0: co.pop()
    if len(co)<2: return None
    rts=[abs(complex(r)) for r in sp.Poly(co,x).nroots(n=18,maxsteps=400)
         if abs(sp.im(r))<1e-9 and abs(sp.re(r))>1e-9]
    return min(rts) if rts else None

def init(a,b,k,rng):
    nA,nB=b*k,a*k
    for _ in range(2000):
        sa=[i for i in range(nA) for _ in range(a)]
        sb=[j for j in range(nB) for _ in range(b)]
        rng.shuffle(sb)
        e=list(zip(sa,sb))
        if len(set(e))!=len(e): continue
        adjA=[[] for _ in range(nA)]
        for (i,j) in e: adjA[i].append(j)
        return nA,nB,[sorted(t) for t in adjA]
    return None

def swap(adjA,rng):
    nA=len(adjA)
    for _ in range(200):
        i1,i2=rng.randrange(nA),rng.randrange(nA)
        if i1==i2: continue
        b1=rng.choice(adjA[i1]); b2=rng.choice(adjA[i2])
        if b1==b2 or b2 in adjA[i1] or b1 in adjA[i2]: continue
        new=[list(t) for t in adjA]
        new[i1].remove(b1); new[i1].append(b2)
        new[i2].remove(b2); new[i2].append(b1)
        return [sorted(t) for t in new]
    return None

def main():
    rng=random.Random(4242)
    print(f"{'a':>3}{'b':>3}{'k':>3}{'n':>4}{'threshold':>11}{'start':>10}{'best':>10}"
          f"{'ratio':>8}{'steps':>7}", flush=True)
    for (a,b) in [(3,4),(4,5),(3,5),(4,6),(5,6)]:
        thr=abs(math.sqrt(a-1)-math.sqrt(b-1))
        for k in (3,4,5):
            nA,nB=b*k,a*k
            if nB>14 or nA+nB>40: continue
            g=init(a,b,k,rng)
            if g is None: continue
            nA,nB,adjA=g
            try: cur=smallest_root(nA,nB,adjA)
            except OverflowError: continue
            if cur is None: continue
            start=cur; best=cur; bestg=adjA
            steps=1200
            for s in range(steps):
                cand=swap(adjA,rng)
                if cand is None: continue
                try: v=smallest_root(nA,nB,cand)
                except OverflowError: continue
                if v is None: continue
                T=0.02*(1-s/steps)
                if v<cur or rng.random()<math.exp(-(v-cur)/max(T,1e-9)):
                    adjA, cur = cand, v
                    if v<best: best, bestg = v, cand
                if best<thr-1e-9:
                    print(f"  VIOLATION a={a} b={b} k={k} root={best:.8f} < {thr:.8f}")
                    print(f"    adjA={bestg}")
                    break
            print(f"{a:>3}{b:>3}{k:>3}{nA+nB:>4}{thr:>11.5f}{start:>10.5f}{best:>10.5f}"
                  f"{best/thr:>8.3f}{steps:>7}", flush=True)
            with open(CKPT+'.tmp','w') as f: f.write(f"{a} {b} {k} best={best:.8f} thr={thr:.8f}\n")
            os.replace(CKPT+'.tmp',CKPT)
    print("\nratio is best-found / threshold; below 1 refutes Song-Fan-Miao Problem 1.")
    return 0

if __name__=='__main__': sys.exit(main())
