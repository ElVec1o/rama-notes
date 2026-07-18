# Automaticity attack on the achiever-parity barrier (2026-07-10).
# Object: Corr(k) = parity of #{prime powers D ≡ 3 (4), D ≤ 2^k : floor(2^{k-1}/D) odd AND floor(2^k/D) odd}
# the leading (linear) stratum of the achiever parity C(k). Reformulation:
#   deficit unbounded  <=  C(k) not eventually periodic  <=  C(k) not 2-automatic (Christol).
# Diagnostics: density of 1s, shortest eventual period (rule out), and 2-KERNEL growth.
import sys
KMAX=24
N=1<<KMAX
# sieve primes up to N
sieve=bytearray([1])*(N+1)
sieve[0]=sieve[1]=0
i=2
while i*i<=N:
    if sieve[i]:
        sieve[i*i::i]=bytearray(len(range(i*i,N+1,i)))
    i+=1
# accumulate Corr[k] for k=1..KMAX
Corr=[0]*(KMAX+1)
# iterate prime powers D ≡ 3 (mod 4)
def contribute(D):
    # for each k with D <= 2^k, add [floor(2^{k-1}/D) odd and floor(2^k/D) odd]
    kmin=D.bit_length()  # smallest k with 2^k >= D (roughly); ensure 2^k+1>=D
    # floor(2^{k}/D): compute incrementally
    for k in range(1,KMAX+1):
        if (1<<k)+1 < D: continue
        a=( (1<<(k-1))//D ) & 1
        b=( (1<<k)//D ) & 1
        if a and b:
            Corr[k]^=1
cnt=0
for p in range(3,N+1):
    if sieve[p]:
        if p%4==3:
            D=p
            while D<=N:
                contribute(D); cnt+=1
                if D> N//p: break
                D*=p
        # p%4==1 prime powers never ≡3(4) unless... p^a mod4: p≡1 → p^a≡1; skip
# print sequence
seq=[Corr[k] for k in range(4,KMAX+1)]
print("Corr(k), k=4..%d:"%KMAX)
print("  ", "".join(map(str,seq)))
ones=sum(seq); print(f"  density of 1s: {ones}/{len(seq)} = {ones/len(seq):.3f}")
# shortest eventual period test: for period P and offset, check tail consistency
def eventually_periodic(s, maxP):
    n=len(s)
    for P in range(1,maxP+1):
        for start in range(0, n-2*P):  # need at least 2 periods of tail
            tail=s[start:]
            if len(tail)>=2*P and all(tail[i]==tail[i%P] for i in range(len(tail))):
                # also require the periodic block to contain a 0 AND be non-trivial length
                return (P,start)
    return None
ep=eventually_periodic(seq, len(seq)//2)
print("  eventual-period (P,start) within tested range:", ep if ep else "NONE (no short eventual period)")
# 2-KERNEL: subsequences (C(2^a n + b)). Estimate distinct kernel elements as prefixes.
full=[Corr[k] for k in range(1,KMAX+1)]  # index by k
def kernel_elements(s, depth):
    # s indexed 0.. ; kernel = { (s[2^a * n + b])_n : a<=depth, 0<=b<2^a }, compared on available prefix
    elems=set()
    L=len(s)
    for a in range(0,depth+1):
        step=1<<a
        for b in range(step):
            sub=tuple(s[b + step*n] for n in range((L-b+step-1)//step) if b+step*n<L)
            # compare on a fixed short prefix length to detect distinctness
            pref=sub[:6]
            if len(pref)==6:
                elems.add(pref)
    return elems
for depth in range(0,5):
    e=kernel_elements(full,depth)
    print(f"  2-kernel distinct 6-prefixes up to depth {depth}: {len(e)}")
