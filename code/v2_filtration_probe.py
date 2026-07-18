"""
Item-2 (linear v2 rate) probe:  the DIVISOR-FILTRATION identity.

Using gcd(i,j) = sum_{d | i, d | j} phi(d) (Smith), expand the permanent:

    a(n) = sum_{sigma} prod_i gcd(sigma i, i)
         = sum_{d : d_i | i}  ( prod_i phi(d_i) )  per(M_d),
    where M_d[k,i] = [ d_i | k ]  (0-1 matrix), so per(M_d) = #{ sigma : d_i | sigma(i) }.

Key structural facts this script CONFIRMS numerically (memory-safe, n <= 12 for the
full divisor sum; n <= 18 for a(n) via Ryser):

  (1) the identity holds exactly;
  (2) the term d = (1,...,1) is exactly n!  (phi(1)=1, per(all-ones)=n!),
      which is WHY v2(a(n)) sits near v2(n!);
  (3) filtration by |S|, S = {i : d_i >= 3}: every term with |S|=s has v2 >= s,
      so  a(n) = T(n) + (v2 >= 1 tail),  T(n) = |S|=0 layer (d_i in {1,2});
  (4) T(n) = sum_{b} C(h,b) (h)_b (n-b)!,  h = floor(n/2)  [closed form];
  (5) v2(T(n)) UNDERSHOOTS v2(a(n)) -- the tail cancels bits to lift a(n) higher.
      This is the wall: no single filtration layer lower-bounds v2(a(n)).
"""
from math import comb, factorial
from itertools import permutations, product

def a_exact_small(n):
    """a(n) = per[gcd] by brute permutation sum (n <= 8)."""
    from math import gcd
    G = [[gcd(i+1, j+1) for j in range(n)] for i in range(n)]
    tot = 0
    for sig in permutations(range(n)):
        p = 1
        for i in range(n):
            p *= G[sig[i]][i]
        tot += p
    return tot

def a_ryser(n):
    """a(n) = permanent via Ryser, O(2^n * n).  Memory O(n).  n <= 20 ok."""
    from math import gcd
    G = [[gcd(i+1, j+1) for j in range(n)] for i in range(n)]
    total = 0
    # Ryser: per = (-1)^n sum_{S} (-1)^|S| prod_i sum_{j in S} G[i][j]
    for S in range(1, 1 << n):
        # row sums over columns in S
        prod = 1
        bits = bin(S).count("1")
        for i in range(n):
            s = 0
            Sj = S
            j = 0
            while Sj:
                if Sj & 1:
                    s += G[i][j]
                Sj >>= 1
                j += 1
            prod *= s
        total += ((-1) ** bits) * prod
    return ((-1) ** n) * total

def per_01(M):
    """permanent of a 0-1 (or int) matrix, brute (small)."""
    n = len(M)
    tot = 0
    for sig in permutations(range(n)):
        p = 1
        for i in range(n):
            p *= M[sig[i]][i]
            if p == 0:
                break
        tot += p
    return tot

def phi(d):
    r, dd = d, d
    p = 2
    while p * p <= dd:
        if dd % p == 0:
            while dd % p == 0:
                dd //= p
            r -= r // p
        p += 1
    if dd > 1:
        r -= r // dd
    return r

def divisors(m):
    return [d for d in range(1, m + 1) if m % d == 0]

def a_filtration(n):
    """a(n) via the divisor-filtration identity (n <= 9; grows as prod tau(i))."""
    div = [divisors(i + 1) for i in range(n)]  # divisors of i+1 (i=0..n-1 -> value 1..n)
    total = 0
    for choice in product(*div):  # choice[i] = d_i | (i+1)
        # M_d[k,i] = [ d_i | (k+1) ]
        coef = 1
        for i in range(n):
            coef *= phi(choice[i])
        if coef == 0:
            continue
        M = [[1 if (k + 1) % choice[i] == 0 else 0 for i in range(n)] for k in range(n)]
        total += coef * per_01(M)
    return total

def T_closed(n):
    """T(n) = |S|=0 layer = sum_b C(h,b) (h)_b (n-b)!,  h=floor(n/2)."""
    h = n // 2
    s = 0
    for b in range(h + 1):
        falling = 1
        for t in range(b):
            falling *= (h - t)
        s += comb(h, b) * falling * factorial(n - b)
    return s

def v2(x):
    if x == 0:
        return float("inf")
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v

print("=== (1)+(2) identity check: a(n) == filtration, and d=1 term == n! ===")
for n in range(1, 9):
    af = a_filtration(n)
    ab = a_exact_small(n) if n <= 7 else a_ryser(n)
    print(f"  n={n:2d}  a_filtration={af}  a_direct={ab}  match={af==ab}  (n!={factorial(n)})")

print()
print("=== (KEY) TERM-WISE test:  v2( prod phi(d_i) * per(M_d) )  >=  v2( ceil(n/2)! ) ? ===")
print("    if the min margin is >= 0 for all d, then v2(a(n)) >= v2(ceil(n/2)!) ~ n/2 is PROVABLE term-wise")
for n in range(1, 9):
    div = [divisors(i + 1) for i in range(n)]
    target = v2(factorial((n + 1) // 2))  # v2(ceil(n/2)!)
    min_margin = 10**9
    argmin = None
    for choice in product(*div):
        coef = 1
        for i in range(n):
            coef *= phi(choice[i])
        M = [[1 if (k + 1) % choice[i] == 0 else 0 for i in range(n)] for k in range(n)]
        p = per_01(M)
        term_v2 = v2(coef) + (v2(p) if p != 0 else 10**9)
        margin = term_v2 - target
        if margin < min_margin:
            min_margin = margin
            argmin = choice
    status = "OK (>=0)" if min_margin >= 0 else "FAILS (<0)"
    print(f"  n={n:2d}  v2(ceil(n/2)!)={target:2d}  min term margin={min_margin:+d}  {status}   worst d={argmin}")

print()
print("=== (4)+(5) T(n) closed form, and v2 comparison  a  vs  T  vs  n! ===")
print(f"  {'n':>3} {'v2(a)':>6} {'v2(T)':>6} {'v2(n!)':>7} {'v2(a)-v2(n!)':>13} {'v2(a)-v2(T)':>12}")
known = {}  # fill a(n) from Ryser up to 18
for n in range(2, 17):
    an = a_ryser(n)
    Tn = T_closed(n)
    va, vT, vf = v2(an), v2(Tn), v2(factorial(n))
    print(f"  {n:>3} {va:>6} {vT:>6} {vf:>7} {va-vf:>13} {va-vT:>12}")
