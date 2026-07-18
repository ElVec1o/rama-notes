# Adaptive-peak parity engine (2026-07-07): generalized engines + Gram/chi4 + matching formula.
# Validated: brute-force minors (n=17), c=1 counts 3,1,12,11,17, out-of-sample n=67 (D_N0=7).
# Usage: python3 adaptive_peaks.py   -> prints the C(k,c) parity table.
from math import gcd
from itertools import combinations
import sys
def prime_powers3(N):
    P=[]
    for q in range(3,N+1,4):
        if all(q%p for p in range(2,int(q**.5)+1)):
            qa=q
            while qa<=N: P.append(qa); qa*=q
    return sorted(P)
def matching_sum(T,N):
    if not T: return 1
    t=T[0]; rest=T[1:]
    s=N(t)*matching_sum(rest,N)
    for i in range(len(rest)):
        l=t*rest[i]//gcd(t,rest[i])
        s+=N(l)*matching_sum(rest[:i]+rest[i+1:],N)
    return s%2
def pi_parity_all_v(j,rowN,colbase,P,n):
    # returns dict v -> parity, using base + delta over T's containing a divisor of v
    Ts=[T for T in combinations(P,j) if matching_sum(list(T),rowN)==1]
    base={}; S0=0
    for T in Ts:
        b=matching_sum(list(T),colbase)
        base[T]=b; S0^=b
    bucket={}
    for T in Ts:
        for t in T: bucket.setdefault(t,[]).append(T)
    out={}
    for v in range(1,n+1,2):
        Dv=[p for p in P if v%p==0]
        aff=set()
        for p in Dv: aff.update(bucket.get(p,[]))
        delta=0
        for T in aff:
            colv=lambda D: colbase(D)-(1 if v%D==0 else 0)
            delta^= (base[T]^matching_sum(list(T),colv))
        out[v]=S0^delta
    return out
def achiever_parity(k,c):
    d=(c-1)//2; n=2**k+c; m=n//2
    P=prime_powers3(n)
    nodd=lambda D:((n//D)+1)//2
    A_row=lambda D: m//D
    A_colbase=lambda D: nodd(D)
    B_row=lambda D: nodd(D)
    # B cols: base = m//D, and v ADDS one (+[D|v]) -> handle sign inside delta by custom base
    PA=pi_parity_all_v(d+1,A_row,A_colbase,P,n)
    # for B: colN_v(D)=m//D+[D|v]; reuse function with base=m//D and delta sign +1: matching only cares mod2 so same code with colv adding
    Ts=[T for T in combinations(P,d+2) if matching_sum(list(T),B_row)==1]
    Bbase={};S0=0
    colb=lambda D:m//D
    for T in Ts:
        b=matching_sum(list(T),colb); Bbase[T]=b; S0^=b
    bucket={}
    for T in Ts:
        for t in T: bucket.setdefault(t,[]).append(T)
    cnt=0
    for v in range(1,n+1,2):
        if PA[v]==0: continue
        Dv=[p for p in P if v%p==0]
        aff=set()
        for p in Dv: aff.update(bucket.get(p,[]))
        delta=0
        for T in aff:
            colv=lambda D:m//D+(1 if v%D==0 else 0)
            delta^=(Bbase[T]^matching_sum(list(T),colv))
        if S0^delta==1: cnt+=1
    return cnt
# sanity: c=1 counts must be 3,1,12,11,17
print("sanity c=1:",[achiever_parity(k,1) for k in [4,5,6,7,8]],"expect [3,1,12,11,17]")
sys.stdout.flush()
print("\nADAPTIVE-PEAK TABLE  C(k,c) parity   [D_N0(2^k+c)=2k-3-s2(c) iff ODD]")
print("k\\c |  1    3    5    7")
for k in [5,6,7,8,9,10]:
    row=[]
    for c in [1,3,5,7]:
        if k==9 and c==7: row.append("  - "); continue
        if k==10 and c in (5,7): row.append("  - "); continue
        cnt=achiever_parity(k,c)
        row.append(f"{'ODD' if cnt%2 else 'EVN'}{cnt%2 and '*' or ' '}")
        sys.stdout.flush()
    print(f"{k:>3} | "+"  ".join(row))
print("\n(6,3) must be ODD to match the real n=67 datum D_N0=7=2*6-3-s2(3).")
print("DONE")
