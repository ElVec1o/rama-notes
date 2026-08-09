"""Does the biregular margin y_1 / tau^2 converge to one, or plateau above it?

This decides the shape of the remaining problem. By Csikvari-Frenkel the empirical root
distribution of biregular graphs converges to the spectral measure of the biregular tree,
whose support begins at tau^2. Weak convergence puts a positive fraction of roots in any
interval [tau^2, tau^2 + eps], so the smallest root should descend to tau^2 and the margin to
one; if instead the margin plateaus above one, the extreme root is behaving like a spectral
outlier and Song-Fan-Miao would hold with uniform slack, which is a far stronger and more
attackable statement.

Four data points suggested a plateau near 2.5 for (3,4), which contradicts the convergence
argument, so the extrapolation was probably premature. This adds larger sizes to settle it.
"""
import sys, math, random, time
import numpy as np, sympy as sp
x=sp.Symbol('x')

def counts(nA,nB,adjA):
    size=1<<nB
    dp=np.zeros(size,dtype=object); dp[0]=1
    idx=np.arange(size)
    for i in range(nA):
        new=dp.copy()
        for bv in adjA[i]:
            bit=1<<bv; has=(idx&bit)!=0
            new[has]+=dp[idx[has]^bit]
        dp=new
    pc=np.array([bin(t).count('1') for t in idx])
    return [int(dp[pc==k].sum()) for k in range(nB+1)]

def random_biregular(a,b,k,rng,tries=800):
    nA,nB=b*k,a*k
    for _ in range(tries):
        sa=[i for i in range(nA) for _ in range(a)]
        sb=[j for j in range(nB) for _ in range(b)]
        rng.shuffle(sb)
        e=list(zip(sa,sb))
        if len(set(e))!=len(e): continue
        adjA=[[] for _ in range(nA)]
        for (i,j) in e: adjA[i].append(j)
        nbrB=[[] for _ in range(nB)]
        for (i,j) in e: nbrB[j].append(i)
        seen={('A',0)}; st=[('A',0)]
        while st:
            side,v=st.pop()
            nb=[('B',t) for t in adjA[v]] if side=='A' else [('A',t) for t in nbrB[v]]
            for w in nb:
                if w not in seen: seen.add(w); st.append(w)
        if len(seen)==nA+nB: return nA,nB,adjA
    return None

def smallest_sq(nA,nB,adjA):
    n=nA+nB
    m=counts(nA,nB,adjA)
    poly=sum((-1)**kk*m[kk]*x**(n-2*kk) for kk in range(len(m)))
    co=sp.Poly(poly,x).all_coeffs()
    while co and co[-1]==0: co.pop()
    rts=[abs(complex(r)) for r in sp.Poly(co,x).nroots(n=25,maxsteps=900)
         if abs(sp.im(r))<1e-9 and abs(sp.re(r))>1e-9]
    return min(rts)**2 if rts else float('nan')

def main():
    rng=random.Random(2718)
    print(f"{'a':>3}{'b':>3}{'k':>3}{'n':>4}{'nB':>4}{'tau^2':>9}"
          f"{'min y1':>10}{'median y1':>11}{'margin':>9}", flush=True)
    t0=time.time()
    for (a,b) in [(3,4),(3,5)]:
        tau2=(math.sqrt(a-1)-math.sqrt(b-1))**2
        for k in (1,2,3,4,5,6):
            nA,nB=b*k,a*k
            if nB>18 or nA+nB>50: continue
            vals=[]
            reps = 5 if nB<=12 else 2
            for _ in range(reps):
                g=random_biregular(a,b,k,rng)
                if g is None: continue
                vals.append(smallest_sq(*g))
            if not vals: continue
            vals.sort()
            print(f"{a:>3}{b:>3}{k:>3}{nA+nB:>4}{nB:>4}{tau2:>9.5f}"
                  f"{vals[0]:>10.5f}{vals[len(vals)//2]:>11.5f}"
                  f"{vals[0]/tau2:>9.3f}", flush=True)
    print(f"\n{time.time()-t0:.0f}s")
    print("margin -> 1 means Song-Fan-Miao is tight and any proof must be delicate.")
    print("margin plateauing above 1 means uniform slack, a stronger and easier target.")
    return 0

if __name__=='__main__': sys.exit(main())
