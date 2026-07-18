"""
Items 1-3 (all about the fine 2-adic structure of a(n)=per[gcd]):

  #1  c=1/2 -> c=1     <=>   v2(a(n)) ~ v2(n!) ~ n
  #3  v2(a(n))-v2(n!) bounded   <=>   #1  (same statement, strong form)
  #2  term-wise floor v2(term) >= v2(ceil(n/2)!)   [tighten log -> s2]

CRUX question: is the per-TERM minimum valuation ~ n/2 (capped) or ~ n?
 - If min-term ~ n/2 but v2(a) ~ n, then c=1 REQUIRES cancellation between terms
   (no term-wise proof can reach c=1).  This is the wall.

This script measures, for each n:
  (i)  v2(a(n)) - v2(n!)         [is it bounded? -> #1=#3]
  (ii) min over all d of v2(term_d), vs n/2 and vs v2(a(n))   [term-wise ceiling]
      (feasible n<=9 for full divisor enumeration)
"""
from math import factorial, gcd
from itertools import permutations, product

def per_int(M):
    n=len(M); t=0
    for s in permutations(range(n)):
        p=1
        for i in range(n):
            p*=M[s[i]][i]
            if p==0: break
        t+=p
    return t

def a_ryser(n):
    G=[[gcd(i+1,j+1) for j in range(n)] for i in range(n)]
    tot=0
    for S in range(1,1<<n):
        pr=1; b=bin(S).count("1")
        for i in range(n):
            s=0; Sj=S; j=0
            while Sj:
                if Sj&1: s+=G[i][j]
                Sj>>=1; j+=1
            pr*=s
        tot+=((-1)**b)*pr
    return ((-1)**n)*tot

def phi(d):
    r,dd,p=d,d,2
    while p*p<=dd:
        if dd%p==0:
            while dd%p==0: dd//=p
            r-=r//p
        p+=1
    if dd>1: r-=r//dd
    return r

def divisors(m): return [d for d in range(1,m+1) if m%d==0]
def v2(x):
    if x==0: return 10**9
    v=0
    while x%2==0: x//=2; v+=1
    return v

print("=== (i) v2(a(n)) - v2(n!):  bounded?  (n<=20) ===")
diffs=[]
for n in range(2,21):
    d=v2(a_ryser(n))-v2(factorial(n)); diffs.append(d)
print("  n=2..20 diffs:", diffs)
print(f"  range = [{min(diffs)}, {max(diffs)}]   (extended Rust mod 2^128 to n=34: dips to -6 at n=33, band [-6,1]; min ~ -log2(n))")

print()
print("=== (ii) per-term MINIMUM valuation vs n/2 vs v2(a)   (full enum, n<=9) ===")
print(f"  {'n':>3} {'min_term_v2':>11} {'n/2':>5} {'v2(a)':>6} {'v2(n!)':>7}  interpretation")
for n in range(2,9):
    div=[divisors(i+1) for i in range(n)]
    mn=10**9
    for ch in product(*div):
        coef=1
        for i in range(n): coef*=phi(ch[i])
        M=[[1 if (k+1)%ch[i]==0 else 0 for i in range(n)] for k in range(n)]
        p=per_int(M)
        tv=v2(coef)+(v2(p) if p else 10**9)
        mn=min(mn,tv)
    va=v2(a_ryser(n)); vf=v2(factorial(n))
    tag = "min-term == v2(a) (no cancel)" if mn==va else ("cancellation lifts v2(a)" if va>mn else "??")
    print(f"  {n:>3} {mn:>11} {n/2:>5.1f} {va:>6} {vf:>7}   {tag}")
