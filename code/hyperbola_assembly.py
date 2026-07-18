# ASSEMBLY of the hyperbola recursion for Corr(k) (2026-07-10)
# Every reduction step is a proven identity:
#   product-swap:      Corr(k) = G(2^{k-1}, 2^k) mod 2
#   quadrant split:    G(M,N)  = K(M,N) + H(M/2,N) + H(N/2,M) + G(M/2,N/2)
#   H-unroll:          H(X,N)  = sum_e K(X/2^e, N)
#   involution:        K(X,X)  = #{v<=X: v=3 mod 4} mod 2        [PROVEN, Lean: kappa_diag]
#   dyadic strips:     K(X,2^b) = K(X,2^{b-1}) + strip
#   translation:       strip   = FP + BD  (w-periodicity mod 2v, gcd-preserving)
#   FP:                sum_v floor(L/2v) * t3(v),  t3 = chi3 * phi  (telescopes to tau3 strata)
#   BD:                per-v boundary window (absolute interval), Mobius over divisors;
#                      normal form: window == (r_v, 2r_v] mod 2v, r_v = L mod 2v  (doubling map!)
from math import gcd
import sys
sys.setrecursionlimit(10000)

AMAX=22
spf=list(range(2**AMAX+1))
for p in range(2,int((2**AMAX)**.5)+1):
    if spf[p]==p:
        for q in range(p*p,2**AMAX+1,p):
            if spf[q]==q: spf[q]=p
def factor(n):
    f={}
    while n>1:
        p=spf[n];e=0
        while n%p==0:n//=p;e+=1
        f[p]=e
    return f
def divisors_mu(n):  # squarefree divisors with mu
    ds=[(1,1)]
    for p in factor(n):
        ds=[(d*pp,m*mm) for (d,m) in ds for (pp,mm) in [(1,1),(p,-1)]]
    return ds
def divisors_all(n):
    ds=[1]
    for p,e in factor(n).items():
        ds=[d*p**i for d in ds for i in range(e+1)]
    return ds
def phi(n):
    r=n
    for p in factor(n): r-=r//p
    return r
def t3(v):  # full-period count: #{r mod v: gcd(v,r) = 3 mod 4} = sum_{d|v, d=3(4)} phi(v/d)
    return sum(phi(v//d) for d in divisors_all(v) if d%4==3)
def oddmult_le(x,m):  # #odd multiples of odd m <= x
    return (x//m+1)//2
def count_window(v,alpha,beta):  # #{w in (alpha,beta], w odd, gcd(v,w) = 3 mod 4}
    tot=0
    for d in divisors_all(v):
        if d%4!=3: continue
        vd=v//d
        for e,mu in divisors_mu(vd):
            de=d*e
            tot+=mu*(oddmult_le(beta,de)-oddmult_le(alpha,de))
    return tot

from functools import lru_cache
@lru_cache(maxsize=None)
def K(i,j):  # K(2^i, 2^j) mod 2, i<=j
    if i>j: return K(j,i)
    X=2**i
    if i==j:
        return ((X+1)//4)&1   # involution theorem
    # strip from 2^{j-1} to 2^j
    A=2**(j-1);B=2**j
    FP=0;BD=0
    for v in range(1,X+1,2):
        q,r=divmod(B-A,2*v)
        FP+=q*t3(v)
        if r: BD+=count_window(v,A+q*2*v,B)
    return (K(i,j-1)+FP+BD)&1

@lru_cache(maxsize=None)
def H(i,j):  # H(2^i, 2^j) = sum_e K(2^{i-e}, 2^j) mod 2  (v any <= 2^i, w odd <= 2^j)
    if i<0: return 0
    s=0
    for e in range(0,i+1):
        s^=K(i-e,j)
    # careful: v ranges 1..2^i; the odd-v layer at e gives odd v' <= 2^{i-e}; e=i gives v'<=1: K(0,j)
    return s

@lru_cache(maxsize=None)
def G(i,j):  # G(2^i, 2^j) mod 2
    if i<0 or j<0: return 0
    if i==0:  # v=1 only: gcd=1 never
        return 0
    if j==0: return 0
    return (K(i,j) ^ H(i-1,j) ^ H(j-1,i) ^ G(i-1,j-1))

# ==== validation ====
def pp3(N):
    P=[]
    for q in range(3,N+1,4):
        if all(q%p for p in range(2,int(q**.5)+1)):
            qa=q
            while qa<=N:P.append(qa);qa*=q
    return P
def corr_direct(k):  # prime-side definition
    n=2**k+1
    return sum(1 for D in pp3(n) if ((2**(k-1)//D)&1) and ((2**k//D)&1))%2
def G_brute(i,j):
    def oddpart(x):
        while x%2==0:x//=2
        return x
    return sum(1 for v in range(1,2**i+1) for w in range(1,2**j+1) if oddpart(gcd(v,w))%4==3)%2

if __name__=="__main__":
    print("VALIDATE assembled G vs brute lattice count:")
    for (i,j) in [(3,4),(4,5),(5,6),(4,6),(6,7),(5,8)]:
        a=G(i,j);b=G_brute(i,j)
        print(f"  G(2^{i},2^{j}): assembled={a} brute={b} {'OK' if a==b else 'FAIL'}")
    print("VALIDATE assembled G(2^(k-1),2^k) vs PRIME-side Corr(k):")
    ok=True
    for k in range(4,15):
        a=G(k-1,k);b=corr_direct(k)
        ok&=a==b
        print(f"  k={k}: assembled={a} prime-side Corr={b} {'OK' if a==b else 'FAIL'}")
    print("ALL:",ok)
