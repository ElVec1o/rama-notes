# `vperm` — the 2-adic valuation of the grade-0 permanent `N₀(2^k+1)`

Computes `v₂(N₀(2^k+1))`, where `N₀ = per M'` and `M'` is the gcd matrix `G(2^k+1)` with its
even×even block set to zero (the grade with no even→even entry).

## Method

Ordering rows and columns as (odd, even), `M' = [[P, Rᵀ],[R, 0]]` with
`P_ij = gcd(o_i,o_j)`, `R_ij = gcd(i, o_j)`, `o_t = 2t+1`. The zero block forces all `m = 2^{k-1}`
even rows through `R` into odd columns, which collapses the permanent to a quadratic form

    N₀ = per M' = uᵀ P u,      u_i = per(R with column i deleted),

so an `n × n` permanent (`2^n` by Ryser) reduces to `m+1` permanents of size `m`. Since only the
2-adic valuation is needed and it is below 64, all arithmetic is native `u64` (mod `2^64`); a printed
valuation of 64 means the residue vanished and a wider modulus is required.

A Smith/Euler diagonalization `P = FᵀΦF` gives the equivalent form `N₀ = Σ_d φ(d) w_d²` with
`w_d = Σ_{i : d | o_i} u_i` (see `code/N0_formula.md`).

## Build and run

```bash
cargo build --release
./target/release/vperm 6          # n = 65
NTHREADS=10 ./target/release/vperm 6
```

## Cost and output

| k | n   | permanents × size | `v₂(N₀)` |
|---|-----|-------------------|----------|
| 3 | 9   | 5 × 4             | 5        |
| 4 | 17  | 9 × 8             | 11       |
| 5 | 33  | 17 × 16           | 25       |
| 6 | 65  | 33 × 32           | 58       |

`k = 7` (size-64 permanents) is out of reach by this method. The `k ≤ 5` values agree with direct
Ryser evaluation of `a(n)`; `k = 6` agrees with the independent divisor-sieve computation of `v₂(N₀)`.

Note that `N₀` is the grade-0 part, not the full permanent `a(n)`; the two valuations differ in
general (see the note *The permanent of the GCD matrix*, §on the deficit).
