"""
c=1 attack — A0 recon + A1 graded-piece dissection.

Decomposition:  a(n) = Σ_σ 2^{w(σ)} O(σ),  w(σ)=Σ_i min(v2(σi),v2(i)),  O(σ)=∏ gcd(odd(σi),odd(i)) odd.
Grade:  a(n) = Σ_w 2^w N_w,  N_w = Σ_{w(σ)=w} O(σ).   max w = v2(n!).
c=1 needs the low-w pieces N_w to carry high v2 (cancellation).  This script prints v2(N_w)
per grade w, to locate the cancellation and hint at a group action.
"""
from math import gcd
from itertools import permutations

def v2(x):
    if x == 0: return 10**9
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def odd(x): return x >> v2(x)
def v2fac(m): return m - bin(m).count("1")

def graded(n):
    # returns dict w -> N_w  (exact ints)
    N = {}
    for s in permutations(range(1, n+1)):
        w = sum(min(v2(s[i]), v2(i+1)) for i in range(n))
        O = 1
        for i in range(n):
            O *= gcd(odd(s[i]), odd(i+1))
        N[w] = N.get(w, 0) + O
    return N

print("=== A1: v2(N_w) per grade w  (a(n)=Σ_w 2^w N_w, max w = v2(n!)) ===")
for n in range(4, 11):
    N = graded(n)
    a = sum((1 << w) * Nw for w, Nw in N.items())
    wmax = max(N); assert wmax == v2fac(n), (n, wmax, v2fac(n))
    # print w : v2(N_w) : (N_w odd?) for each grade
    prof = []
    for w in range(0, wmax+1):
        Nw = N.get(w, 0)
        prof.append(f"{w}:{v2(Nw) if Nw!=0 else '.'}")
    print(f" n={n:2d}  v2(a)={v2(a):2d}  v2(n!)={wmax:2d}   v2(N_w) by w=0..{wmax}:  " + "  ".join(prof))

print()
print("Reading:  entry 'w:k' means grade w contributes 2^w·(2^k·odd).  The 2-adic value of")
print("grade w is (w + v2(N_w)); v2(a) = v2 of the sum.  Look for v2(N_w) LARGE at small w")
print("(=> that grade self-cancels, like an orbit-sum) vs small (=> it can drag v2(a) down).")
