"""The power-sum certificate run at scale, in exact rational arithmetic.

Each success is an unconditional proof of Conjecture 10 for that graph: no floating point, no
Angel-Friedman-Hoory, only the machine-checked implication
PowerSumCertificate.roots_ge_of_powersum together with Heilmann-Lieb real-rootedness.

The check is: with q a rational UPPER bound for tau^2 = a+b-2-2 sqrt((a-1)(b-1)), obtained
from a rational LOWER bound for the square root, verify P_m q^m <= 1 for some m. Everything
is a Fraction; nothing is rounded.

Rule 8: progress, ETA, atomic checkpoint, backgrounded.
"""
import sys, os, time, random
from fractions import Fraction
from math import isqrt
import numpy as np

CKPT='private/certify_ckpt.txt'
MS=(4,8,16,24)

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

def power_sums(asc, M):
    """asc = ascending coeffs of Gt; return p_m = sum (1/y_i)^m as Fractions."""
    c=[Fraction(t) for t in asc]; nu=len(c)-1
    a=[c[nu-j] for j in range(nu+1)]; lead=a[nu]
    e=[Fraction((-1)**k)*a[nu-k]/lead for k in range(nu+1)]
    p=[Fraction(0)]*(M+1)
    for m in range(1,M+1):
        s=Fraction(0)
        for i in range(1,m):
            if i<=nu: s+=Fraction((-1)**(i-1))*e[i]*p[m-i]
        if m<=nu: s+=Fraction((-1)**(m-1))*m*e[m]
        p[m]=s
    return p

def tau2_upper(a,b,prec=10**12):
    """rational q >= tau^2, via a rational lower bound for sqrt((a-1)(b-1))."""
    D=(a-1)*(b-1)
    r=Fraction(isqrt(D*prec*prec), prec)      # r <= sqrt(D)
    return Fraction(a+b-2) - 2*r

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

def main():
    rng=random.Random(31337)
    pairs=[(3,4),(3,5),(4,5),(3,6),(4,6),(5,6),(3,7),(4,7),(5,7)]
    trials=int(os.environ.get('TRIALS','25'))
    todo=[(a,b,k,t) for (a,b) in pairs for k in (1,2,3,4) for t in range(trials)]
    print(f"{len(todo)} biregular graphs to certify, exact rational arithmetic", flush=True)
    cert=0; tot=0; fails=[]
    t0=time.time()
    for i,(a,b,k,t) in enumerate(todo):
        nA,nB=b*k,a*k
        if nB>12 or nA+nB>40: continue
        g=random_biregular(a,b,k,rng)
        if g is None: continue
        nA,nB,adjA=g
        n=nA+nB
        m=counts(nA,nB,adjA)
        # mu_G = sum (-1)^k m_k x^{n-2k}; even part Gt ascending in y = x^2
        nu=len(m)-1
        while nu>0 and m[nu]==0: nu-=1
        asc=[Fraction((-1)**(nu-j)*m[nu-j]) for j in range(nu+1)]
        if asc[0]==0: continue
        P=power_sums(asc,max(MS))
        q=tau2_upper(a,b)
        ok=any(abs(P[mm])*q**mm<=1 for mm in MS)
        tot+=1; cert+=1 if ok else 0
        if not ok: fails.append((a,b,k,n))
        if (i+1)%50==0 or tot in (1,5):
            el=time.time()-t0
            print(f"  {i+1}/{len(todo)}  certified {cert}/{tot}  {el:.0f}s"
                  f"  ETA {(len(todo)-i-1)*el/max(i+1,1)/60:.1f}min", flush=True)
            with open(CKPT+'.tmp','w') as f: f.write(f"{i+1} certified={cert}/{tot}\n")
            os.replace(CKPT+'.tmp',CKPT)
    print(f"\ngraphs certified : {cert}/{tot}  ({100*cert/max(tot,1):.1f}%)")
    if fails:
        from collections import Counter
        print(f"not certified    : {Counter((a,b) for a,b,k,n in fails)}")
    print("\nEach certified graph is an unconditional proof of Conjecture 10 for that graph.")
    return 0

if __name__=='__main__': sys.exit(main())
