# A quadratic-form / Smith-diagonalized formula for the grade-0 permanent `N₀(2^k+1)`

*(Paper 3, §on computing `N₀` beyond Ryser. Self-contained; all claims verified — see foot.)*

## Setup

Let `n = 2^k+1`, `m = 2^{k-1}`. Split `{1,…,n}` into the odd indices
`O = {o_0,…,o_m} = {1,3,…,2m+1}` (`m+1` of them) and even indices `E = {2,4,…,2m}` (`m` of them).
Let `G = [gcd(i,j)]` be the gcd matrix and define the **grade-0 permanent**

> `N₀ := per(M')`, where `M'` is `G` with its `E×E` block set to `0`.

`M'` keeps exactly the permutation terms that use no even→even entry (the "`w=0` grade"); at the peaks
`n=2^k+1` this is the `N₀ = Σ_v per(A_v)per(B_v)` of the achiever-count / MacWilliams theory.

Using `gcd(2a,odd)=gcd(a,odd)`, order rows/cols as `O,E` and write
```
        [ P  Q ]                 P_ij = gcd(o_i,o_j)        (m+1)×(m+1)
   M' = [ R  0 ],   with         Q_ij = gcd(o_i, j)         (m+1)×m,  and Q = Rᵀ
                                  R_ij = gcd(i, o_j)         m×(m+1).
```

## Theorem 1 (quadratic form).  `N₀ = uᵀ P u`,  where `u_i = per(R with column i deleted)`, `i=0..m`.

*Proof.* In `per(M')` the `E×E` zero block forces all `m` even-rows through `R` into odd columns; they
occupy `m` of the `m+1` odd columns, leaving one odd column `j₀` for the odd-rows. Hence
`per(M') = Σ_{j₀} per(R_{-j₀})·per[P_{·j₀} | Rᵀ]`. Expanding the second factor along its first column,
`per[P_{·j₀}|Rᵀ] = Σ_i P_{ij₀}·per(Rᵀ minus row i) = Σ_i P_{ij₀} u_i`. So
`per(M') = Σ_{j₀} u_{j₀} Σ_i P_{ij₀} u_i = uᵀPu`. ∎

## Theorem 2 (Smith/Euler diagonalization).  `N₀ = Σ_{d odd} φ(d) · w_d²`,  `w_d = Σ_{i: d | o_i} u_i`.

*Proof.* `gcd(o_i,o_j) = Σ_{d | o_i, d | o_j} φ(d)` (Smith), i.e. `P = FᵀΦF` with `F_{d,i}=[d|o_i]`
(`d` odd), `Φ=diag φ(d)`. Then `uᵀPu = (Fu)ᵀΦ(Fu) = Σ_d φ(d)(Fu)_d²` and `(Fu)_d = Σ_{i:d|o_i}u_i=w_d`. ∎

## Corollary (2-adic valuation).
Since every odd prime gives `v₂(φ(p^a))=v₂(p-1)≥1`, we have `v₂(φ(d))=1 ⟺ d = p^a` with
`p ≡ 3 (mod 4)`. Empirically the minimum term valuation is attained an **odd** number of times (no
cancellation), whence
```
   v₂(N₀(2^k+1)) = min_{d odd} [ v₂(φ(d)) + 2 v₂(w_d) ] = 1 + 2·min_{q=p^a, p≡3(4)} v₂(w_q).
```
The controlling prime-powers `q≡3 (mod 4)` are exactly those of the character-sum theory.

## Computation beyond Ryser
Theorem 1 reduces `N₀` (an `n×n` permanent, `2^n` by Ryser) to `m+1 = 2^{k-1}+1` permanents of size
`m = 2^{k-1}`. Only the 2-adic valuation is needed, and it is `< 64`, so all arithmetic is native
`u64` (mod `2^64`). Engine: `code/rust_recursion/vperm.rs`.

| k | n | permanents × size | `v₂(N₀)` |
|---|----|------------------|----------|
| 3 | 9  | 5 × 4   | 5  |
| 4 | 17 | 9 × 8   | 11 |
| 5 | 33 | 17 × 16 | 25 |
| 6 | 65 | 33 × 32 | **58** |

`v₂(N₀(65)) = 58` was obtained here **independently of the divisor-sieve** that first produced it — a
cross-check by a completely different route, on a permanent (`n=65`) that is `2^65` by brute force.

## Caveat (scope)
`N₀` is the grade-0 part, **not** the full permanent `a`. `v₂(a) − v₂(N₀)` is irregular (it equals
`0` at n=9,17 but `+1,−2,+3,−1,+4` at n=5,7,13,19,22), so this formula does **not** compute `v₂(a)` and
does not by itself resolve `D(2^k+1)`. Its use is as a fast, exact handle on `N₀` — the object the
achiever-count / deficit-at-`N₀` theory is actually about.

---
*Verified:* Thm 1 as an exact integer identity (k=3,4); Thm 2 and the Corollary (k=3,4,5); the table by
`vperm` (k=3,4,5 machine-matched to known values, k=6 = 58). Cross-checked against the divisor-sieve
`v₂(N₀)=11,25,58` at k=4,5,6.
