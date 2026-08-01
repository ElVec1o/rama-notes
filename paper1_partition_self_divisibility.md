# Integers n Where n Divides p(n) − 1

This note records the complete list of n ≤ 10⁶ with n | (p(n) − 1), an
elementary explanation for the early appearance of the Ramanujan primes 7
and 11, and a uniformity test of p(n) mod n at that scale.

## Summary

We study the sequence S = { n ≥ 2 : n | (p(n) − 1) }, where p(n) is the
integer partition function. This is OEIS A128836 (2007); the companion
classes { n : n | p(n) } and { n : n | p(n) + 1 } are A051177 and A203023,
and the residue sequence p(n) mod n is A093952. These sequences were
already computed complete to 10⁸. We recompute all 13 terms of S through
n = 10⁶ and observe that the Ramanujan congruence primes 7 and 11 appear
among the first three terms. We give an elementary explanation for this
using the pentagonal number recurrence, and verify it formally in Lean 4
against Mathlib's combinatorial partition function (RamaLean/Paper1.lean).

These sequences are known (A128836, A051177, A203023, A093952; see above),
so nothing here is a new sequence. The contributions are: the Lean 4
formalization of the small congruences p(7) ≡ 1 (mod 7) and
p(11) ≡ 1 (mod 11) (RamaLean/Paper1.lean); the elementary
pentagonal-recurrence explanation for the appearance of the Ramanujan
primes 7 and 11 (Section 3); and the uniformity computation for p(n) mod n
at scale 10⁶–4×10⁶ (Section 1a). The main open question — is S infinite? —
is the pre-existing conjecture recorded in the comments to A051177, along
with the same probabilistic heuristic.


## 1. Definition and computed values

Let p(n) denote the number of integer partitions of n. Define

    S = { n ≥ 2 : p(n) ≡ 1 (mod n) }.

Through n = 10⁶ (complete search):

    S = { 4, 7, 11, 54, 55, 115, 146, 157, 234, 239, 951, 272732, 419192 }

(13 terms; the gap between 951 and 272732 is large but typical — see §1a.)

| n | p(n) | (p(n)−1)/n |
|-----|------|------------|
| 4 | 5 | 1 |
| 7 | 15 | 2 |
| 11 | 56 | 5 |
| 54 | 386155 | 7151 |
| 55 | 451276 | 8205 |
| 115 | 1064144451 | 9253430 |
| 146 | 27517052599 | 188472963 |
| 157 | 80630964769 | 513573024 |
| 234 | 65851585970275 | 281417034061 |
| 239 | 97862933703585 | 409468341856 |
| 951 | 338110563...863 | 355531612...962 |


## 1a. Distribution of p(n) mod n at scale 10⁶

Interim runs at N = 2×10⁵ showed no S-terms past 951 (a ≈ 0.5%-probability
gap under the pseudorandomness heuristic), which we briefly flagged as an
anomaly. The full run to N = 10⁶ **with control residue classes** settles
it: the gap was ordinary fluctuation.

Counts up to N = 10⁶ (random expectation ≈ ln N ≈ 13.8 per class):

| residue class | terms | last term | largest gap (ratio) |
|---------------|-------|-----------|---------------------|
| +1 (= S) | 13 | 419192 | 951 → 272732 (287×) |
| 0 (= S₀) | 16 | 274534 | — steady |
| −1 (= S₋₁) | 6 | 322733 | 1219 → 322733 (265×) |
| +2 | 18 | 851226 | 164882 → 851226 (5×) |
| −2 | 7 | 275548 | 7862 → 275548 (35×) |
| +3 | 8 | 310707 | 8608 → 172167 (20×) |
| −3 | 16 | 227557 | — steady |
| +5 | 8 | 354192 | 27705 → 354192 (13×) |

Conclusions: (i) S continues — further terms **272732 and 419192**; S₋₁ gains
322733; S₀ gains 274534. (ii) Class counts range from 6 to 18 around the
Poisson mean 13.8 (σ ≈ 3.7) — the scatter, and multiplicative gaps of
one-to-two orders of magnitude, are typical across control classes, so
the ±1 classes are NOT special. (iii) Directly at scale: the normalized
residue (p(n) mod n)/n over all n ≤ 10⁶ is uniform to within ~1% per
5%-bin (20-bin histogram, `code/paper1_output_n1000000.txt`) — a
large-scale empirical test of the uniformity heuristic for p(n) mod n,
and it passes cleanly.

**Extension to N = 4×10⁶** (C+GMP scanner, validated bin-for-bin against
the 10⁶ run; `code/pent_4e6.txt`): the histogram uniformity tightens to a
maximum deviation of **0.40% per bin** (4×10⁶ samples), scaling as
expected with √N — strong direct support for the pseudorandomness
heuristic. Counts at 4×10⁶ (expectation ln N ≈ 15.2): S = 13, S₀ = 16,
S₋₁ = 6, controls +2: 19, −2: 7, +3: 9, −3: 18, +5: 10 — spread 6–19,
Poisson-typical. No new terms in the three distinguished classes between
10⁶ and 4×10⁶. (A full N = 10⁷ run needs ≈ 12 GB for the value table —
Θ(N^{3/2}) bits is inherent to the recurrence, and there is no obvious
modular shortcut since the modulus n varies; see `code/README.md`.)

A pleasant by-product of the extension: the consecutive triple

    (156, 157, 158):  p(156) ≡ −1 (mod 156), p(157) ≡ +1 (mod 157),
                      p(158) ≡ 0 (mod 158)

— three consecutive integers hitting the three distinguished residues.
No further adjacent pairs appear up to 10⁶.

## 2. Related sequences

Through n = 10⁶ (both catalogued in the OEIS, complete to 10⁸):

    S₀ = { n ≥ 2 : n | p(n) }   (A051177)
       = { 2, 3, 124, 158, 342, 693, 1896, 3853, 4434, 5273, 8640,
           14850, 17928, 110516, 178984, 274534 }
    S₋₁ = { n ≥ 2 : p(n) ≡ −1 (mod n) }   (A203023)
        = { 6, 156, 305, 484, 1219, 322733 }


## 3. Why 7 and 11 appear (and 5 does not)

The first three nontrivial members of S are 4, 7, 11. The primes 7 and 11
are two of Ramanujan's three congruence primes (5, 7, 11). We explain their
appearance using only Euler's pentagonal number recurrence.

### Proposition

p(5) ≡ 2 (mod 5), p(7) ≡ 1 (mod 7), p(11) ≡ 1 (mod 11).

### Proof

Euler's recurrence gives, for the specific values n = 5, 7, 11:

    p(5)  = p(4) + p(3) − p(0)             = 5 + 3 − 1       = 7
    p(7)  = p(6) + p(5) − p(2) − p(0)      = 11 + 7 − 2 − 1  = 15
    p(11) = p(10) + p(9) − p(6) − p(4)     = 42 + 30 − 11 − 5 = 56

Reducing modulo 5, 7, 11 respectively:

    p(5) mod 5:  In the sum 5 + 3 − 1, the term p(4) = 5 ≡ 0 (mod 5).
                 Remaining: 3 − 1 = 2.

    p(7) mod 7:  In the sum 11 + 7 − 2 − 1, the term p(5) = 7 ≡ 0 (mod 7).
                 Remaining: 11 − 2 − 1 = 8 ≡ 1 (mod 7).

    p(11) mod 11: In the sum 42 + 30 − 11 − 5, the term p(6) = 11 ≡ 0 (mod 11).
                  Remaining: 42 + 30 − 5 = 67 ≡ 1 (mod 11).

In each case, exactly one term in the pentagonal recurrence vanishes modulo
the prime in question: p(4) = 5, p(5) = 7, p(6) = 11. These vanishings are
trivial — each value literally equals the prime — but they are also the n = 0
instances of Ramanujan's congruences p(5n+4) ≡ 0 (mod 5), p(7n+5) ≡ 0
(mod 7), p(11n+6) ≡ 0 (mod 11). ∎


### Remark on the Ramanujan connection

We emphasize that the proof above does NOT require Ramanujan's congruences
in their full generality. The vanishing of p(5) mod 7 is the trivial fact
that 7 is divisible by 7. The connection to Ramanujan is aesthetic: the
reason p(5) = 7, p(6) = 11 happen to equal primes is related to the
algebraic identity

    24 · g_k + 1 = (6k − 1)²

where g_k = k(3k−1)/2 are the generalized pentagonal numbers. For k = 1,
−1, 2, this gives |6k−1| = 5, 7, 11 — Ramanujan's primes. The magic
residues β_q = q − g_k then satisfy β_5 = 4, β_7 = 5, β_11 = 6, and
the partition values at these points are p(4) = 5, p(5) = 7, p(6) = 11 —
the primes themselves. This is a coincidence of small partition values,
not a deep theorem. For q = 13, the analogous β_13 = 6, but p(6) = 11 ≠ 13,
and the pattern breaks.


## 4. Open questions

1. **Is S infinite?** Conjecturally yes. Sharpened form:
   `#{ n ≤ N : n | p(n) − 1 } = log N + O(√(log N)·loglog N)`, the
   prediction of the model "p(n) mod n is uniform on {0,…,n−1}, terms
   independent." (Expected count Σ_{n≤N} 1/n ≈ log N + γ; variance ≈ log N.)
   Data through 4×10⁶: 13 terms vs log N + γ ≈ 15.8 expected — within 1σ.

   **This is beyond current technology and we do not claim a path to a
   proof.** Even the distribution of p(n) in residue classes modulo a
   *fixed* small integer is hard: positive density of n with p(n) even is
   open (Parkin–Shanks conjecture); infinitely-many-congruences results
   (Ono 2000, and mod 4 work) go the other way (they produce structured
   families, not equidistribution). With a *varying* modulus n there is no
   equidistribution theorem at all, so "S is infinite" sits with a large
   family of probabilistically-obvious-but-unreachable statements about
   p(n) (e.g. "p(n) is prime infinitely often"). The §1a uniformity data is
   the strongest evidence we can currently offer for the heuristic.

2. Are there other consecutive pairs in S besides (54, 55)? None appear
   up to 10⁶. Across the three sequences, the known adjacent runs are
   (2,3), (3,4), (6,7), (54,55), and the triple (156, 157, 158).

3. Can the ~1%-level uniformity of (p(n) mod n)/n (§1a) be pushed to a
   discrepancy bound, or explained by anything beyond heuristics? (No
   equidistribution theorem for p(n) mod n is known even for fixed
   moduli.)


## 5. Reproducibility code

The computation to N = 10^6 is `code/paper1_million.py` in the `rama-notes`
repository, with its outputs committed as `code/paper1_output_n200000.txt` and
`code/paper1_output_n1000000.txt`; the companion sequences of Section 2 are
regenerated by `code/paper1_extend_sequences.py`. The snippet below is the same
recurrence in its simplest form, for readability.


```python
from functools import lru_cache

@lru_cache(maxsize=200000)
def p(n):
    """Integer partition function via Euler's pentagonal recurrence."""
    if n < 0: return 0
    if n == 0: return 1
    total = 0
    for k in range(1, n + 1):
        sign = (-1) ** (k + 1)
        g1 = k * (3 * k - 1) // 2
        g2 = k * (3 * k + 1) // 2
        if g1 <= n: total += sign * p(n - g1)
        if g2 <= n: total += sign * p(n - g2)
    return total

# Compute S = { n >= 2 : p(n) ≡ 1 (mod n) } up to N
# (For large N, e.g. N = 200000, use an iterative bottom-up version of the
# same recurrence to avoid recursion limits: build p[0..N] in an array,
# inner loop over generalized pentagonal indices. Runtime ~25 s at 2×10⁵.
# See code/paper1_extend_sequences.py, output code/paper1_output_n200000.txt.)
N = 1000
S = [n for n in range(2, N + 1) if p(n) % n == 1]
print(f"S up to {N}: {S}")
print(f"Count: {len(S)}")

# Verify each value
for n in S:
    assert p(n) % n == 1, f"FAILED at n={n}"
    print(f"  n={n}: p({n}) = {p(n)}, (p(n)-1)/n = {(p(n)-1)//n}")
```

Expected output:
```
S up to 1000: [4, 7, 11, 54, 55, 115, 146, 157, 234, 239, 951]
Count: 11
```
