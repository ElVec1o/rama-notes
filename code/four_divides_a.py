"""CRACK: 4 | a(n) for n>=4  (sharpens 2|a(n), n>=3).
a(n)=det(M)+2*Sigma, Sigma=sum_{sigma odd} prod gcd(i,sigma i).
- det(M)=prod_{k<=n} phi(k) (Smith); phi(3)phi(4)=4 => 4|det for n>=4.
- Sigma = #{sigma odd: prod gcd odd} mod 2.
- prod gcd odd <=> no even->even <=> sigma(evens) subset odds.
  #{such sigma} = (ceil(n/2)!)^2  [inject evens->odds then bijection of rest].
- G=[gcd odd]=J-e e^T has rank<=2 => det G=0 (n>=3) => #odd = #even = (ceil(n/2)!)^2 / 2,
  which is EVEN for n>=3.  => 2*Sigma = 0 mod 4.  => 4 | a(n) for n>=4. QED.
Tower (empirical): 2^k | a(n) for n>=n_k, n_k=3,4,7,7,9,10,11,12,... => v2(a(n))->infinity.
Higher rungs (8|,...) need #{sigma:d(sigma)=k} for k>=1, which lack the clean k=0 closed form. OPEN.
"""
