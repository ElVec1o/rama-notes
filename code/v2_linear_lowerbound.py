"""
Item-2 CRACK candidate:   v2(a(n))  >=  v2( ceil(n/2)! )  ~  n/2   (LINEAR, c=1/2).

Discovered via the divisor-filtration identity
    a(n) = sum_{d: d_i | i}  ( prod_i phi(d_i) )  per(M_d),   M_d[k,i] = [ d_i | k ].

TERM-WISE claim (verified n<=8, all d):
    v2( prod_i phi(d_i) )  +  v2( per(M_d) )   >=   v2( ceil(n/2)! ).

Partial proof:
  * all-ones-column lemma:  per(M_d) = c1! * N,  c1 = #{i : d_i = 1},
    because the c1 unconstrained columns take the c1 leftover values in any order.
    => v2(per(M_d)) >= v2(c1!).
  * phi(d_i) is EVEN for d_i >= 3  => v2(prod phi) >= c3,  c3 = #{i : d_i >= 3}.
  * counting: with c2 = #{d_i = 2} <= floor(n/2) (only even positions),
    c1 + c3 = n - c2 >= ceil(n/2).
  The residual gap (when odd positions are constrained, shrinking c1 while
  c1 is 2-adically large) is covered by extra 2s inside N -- the part still
  needing a clean proof.  This script checks:
    (A) per(M_d) is ALWAYS divisible by c1!   (the lemma);
    (B) the global bound v2(a(n)) >= v2(ceil(n/2)!) for n up to 21 (Ryser);
    (C) the simple bound v2(c1!)+c3 vs the true term v2 -- where N's extra 2s kick in.
"""
from math import factorial, gcd
from itertools import permutations, product

def per_int(M):
    n = len(M); tot = 0
    for sig in permutations(range(n)):
        p = 1
        for i in range(n):
            p *= M[sig[i]][i]
            if p == 0: break
        tot += p
    return tot

def a_ryser(n):
    G = [[gcd(i+1, j+1) for j in range(n)] for i in range(n)]
    total = 0
    for S in range(1, 1 << n):
        prod = 1; bits = bin(S).count("1")
        for i in range(n):
            s = 0; Sj = S; j = 0
            while Sj:
                if Sj & 1: s += G[i][j]
                Sj >>= 1; j += 1
            prod *= s
        total += ((-1) ** bits) * prod
    return ((-1) ** n) * total

def phi(d):
    r, dd, p = d, d, 2
    while p*p <= dd:
        if dd % p == 0:
            while dd % p == 0: dd //= p
            r -= r//p
        p += 1
    if dd > 1: r -= r//dd
    return r

def divisors(m): return [d for d in range(1, m+1) if m % d == 0]

def v2(x):
    if x == 0: return 10**9
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

print("=== (A) all-ones-column lemma:  c1! | per(M_d)  for ALL d  (n<=8) ===")
allok = True
for n in range(1, 9):
    div = [divisors(i+1) for i in range(n)]
    bad = 0
    for choice in product(*div):
        c1 = sum(1 for x in choice if x == 1)
        M = [[1 if (k+1) % choice[i] == 0 else 0 for i in range(n)] for k in range(n)]
        p = per_int(M)
        if p % factorial(c1) != 0:
            bad += 1
    allok &= (bad == 0)
    print(f"  n={n:2d}  divisor-tuples checked, c1!|per failures = {bad}")
print(f"  LEMMA (A) holds for all tested: {allok}")

print()
print("=== (B) global bound   v2(a(n))  >=  v2(ceil(n/2)!) ~ n/2   (Ryser, n<=21) ===")
print(f"  {'n':>3} {'v2(a)':>6} {'v2(ceil(n/2)!)':>15} {'margin':>7} {'~n/2':>6}")
for n in range(2, 21):
    an = a_ryser(n)
    tgt = v2(factorial((n+1)//2))
    va = v2(an)
    print(f"  {n:>3} {va:>6} {tgt:>15} {va-tgt:>7}   {n/2:>5.1f}   {'OK' if va>=tgt else 'FAIL <<<'}")

print()
print("=== (C) rigorous CHAIN check: proven per-term floor  v2(c1!)+c3  vs true, and vs ceil(n/2)-floor(log2 n)-1 ===")
import math
for n in range(1, 9):
    div = [divisors(i+1) for i in range(n)]
    m = (n+1)//2
    rig = m - (n.bit_length()-1) - 1     # ceil(n/2) - floor(log2 n) - 1
    floor_ok = True; min_floor = 10**9
    for choice in product(*div):
        c1 = sum(1 for x in choice if x==1)
        c3 = sum(1 for x in choice if x>=3)
        coef = 1
        for i in range(n): coef *= phi(choice[i])
        M = [[1 if (k+1)%choice[i]==0 else 0 for i in range(n)] for k in range(n)]
        p = per_int(M)
        proven_floor = v2(factorial(c1)) + c3
        true_v2 = v2(coef) + (v2(p) if p else 10**9)
        if proven_floor > true_v2: floor_ok = False    # floor must be <= true
        min_floor = min(min_floor, proven_floor)
    print(f"  n={n:2d}  min_d[v2(c1!)+c3]={min_floor:2d}  >= rigorous_bound({rig})? {min_floor>=rig}   floor<=true always? {floor_ok}")
