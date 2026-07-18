"""ITEM 2 CRACKED: v2(a(n)) -> infinity, PROVEN.
Rows m with all prime factors ≡1 mod 2^k are ≡(1,...,1) mod 2^k (divisors all ≡1).
By Dirichlet, C_k={such m} is infinite; for n large, >= 2^k such rows R.
Regular (Z/2)^k action on R: |G|=2^k, every nonid = product of 2^{k-1} transpositions
=> sign=(-1)^{2^{k-1}}=+1 for k>=2 => G ⊆ A_n. Acts freely on {sigma: sign=-1},
preserves ∏gcd mod 2^k (permutes ≡1-mod-2^k rows) => each orbit (size 2^k) sums to 0
mod 2^k => 2^k | Sigma. With 2^{k+1}|det=∏φ(j) (large n) => 2^{k+1}|a(n) => v2(a(n))≥k+1.
Thresholds N_k finite => v2(a(n))->infinity. Rate >= ~(1/2)log2(n) (conjectured ~n).
Verified: rows≡1 mod 2^k (k=2,3,4); Klein-4 all even; 8|a(n) for n≥17 (rows 1,5,13,17)."""
