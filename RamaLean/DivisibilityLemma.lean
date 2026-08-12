import Mathlib

/-!
# The Divisibility Lemma

The mechanism behind every counterexample in this development. Let `G` be a finite graph, `S` a set
of `k` vertices, and suppose `G - S` has `p` components each inducing the same graph `B`, with
`A = μ_B` its matching polynomial. Then

  **`A ^ (p - k) ∣ μ_G`.**

At `k = 2` this is the divisor `A ^ (p - 2)` of the two-cut identity
`μ_G = A^(p-2)(x²A² - px(B_u+B_v)A + pDA + p(p-1)B_uB_v)`, and at `k = 3` it is `A ^ (p - 3)`, which
is what produces the 3-connected counterexample to C2 on 23 vertices. The lemma is why no hypothesis
bounding the *ambient* graph reaches the engine: `A` depends on `B` alone, and enlarging `S` raises
the connectivity while leaving `A` untouched. It is also why the construction costs `p ≥ k + 1`
branches, since the exponent `p - k` must be positive for the divisor to carry a root.

## The argument

Expand `μ_G = ∑_M (-1)^{|M|} x^{n - 2|M|}` over matchings and group the terms by

  `J(M) = { i : some edge of M joins S to the i-th component }`.

A matching uses each vertex of `S` at most once, so distinct branches in `J(M)` are entered through
distinct vertices of `S`; picking one such vertex per branch is an injection `J(M) → S`, whence
`|J(M)| ≤ k`. For `i ∉ J(M)` the restriction of `M` to the `i`-th branch is an arbitrary matching of
`B`, so summing over those choices contributes a factor `A ^ (p - |J(M)|)`. Each term is therefore
divisible by `A ^ (p - k)`, and so is the sum.

## What is formalised

Mathlib carries no matching polynomial, the standing gap in this development, so the expansion itself
is taken as a hypothesis rather than derived. Both halves that the expansion is combined *from* are
proved here:

* `card_branches_le_sep` is the counting step, in the form the argument uses: a family of branches
  each with a representative in `S`, distinct branches having distinct representatives, has at most
  `|S|` members. The injectivity is exactly "a matching uses each vertex of `S` at most once".
* `dvd_sum_of_pow_terms` is the algebraic step: a sum whose terms carry `A ^ (p - j i)` with every
  `j i ≤ k ≤ p` is divisible by `A ^ (p - k)`. This is where `p ≥ k + 1` earns its keep.

`matching_expansion_dvd` combines them into the lemma as stated, and `two_cut_divisor` and
`three_cut_divisor` are the two instances the paper uses.

## Status

`card_branches_le_sep`, `dvd_sum_of_pow_terms`, `matching_expansion_dvd`, `two_cut_divisor` and
`three_cut_divisor` are `VERIFIED`. The matching expansion is `PROVED` in the note and carries
formalisation debt, the blocker being the absence of the matching polynomial in Mathlib.
-/

namespace DivisibilityLemma

open Finset

/-! ### The counting step -/

/-- **At most `k` branches meet a separator of size `k`.**  Each branch that a matching enters is
entered through a vertex of the separator, and a matching uses each separator vertex at most once, so
the choice of entry vertex is injective on the branches entered. -/
theorem card_branches_le_sep {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (J : Finset γ) (S : Finset β) (rep : γ → β)
    (hrep : ∀ i ∈ J, rep i ∈ S) (hinj : Set.InjOn rep J) :
    J.card ≤ S.card :=
  Finset.card_le_card_of_injOn rep hrep hinj

/-- The same bound against a named size, which is how the lemma below consumes it. -/
theorem card_branches_le_of_card {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (J : Finset γ) (S : Finset β) (rep : γ → β) (k : ℕ)
    (hrep : ∀ i ∈ J, rep i ∈ S) (hinj : Set.InjOn rep J) (hS : S.card = k) :
    J.card ≤ k := by
  rw [← hS]; exact card_branches_le_sep J S rep hrep hinj

/-! ### The algebraic step -/

variable {R : Type*} [CommRing R]

/-- **A sum of terms each carrying `A ^ (p - j i)` with `j i ≤ k ≤ p` is divisible by
`A ^ (p - k)`.**  This is the whole algebraic content: the branches a matching does not touch each
contribute a full factor of `A`, and there are at least `p - k` of them. -/
theorem dvd_sum_of_pow_terms {ι : Type*} (T : Finset ι) (A : Polynomial R)
    (c : ι → Polynomial R) (j : ι → ℕ) (p k : ℕ)
    (hj : ∀ i ∈ T, j i ≤ k) (hk : k ≤ p) :
    A ^ (p - k) ∣ ∑ i ∈ T, c i * A ^ (p - j i) := by
  refine Finset.dvd_sum ?_
  intro i hi
  have hle : p - k ≤ p - j i := by
    have := hj i hi
    omega
  exact Dvd.dvd.mul_left (pow_dvd_pow A hle) _

/-! ### The lemma -/

/-- **The Divisibility Lemma.**  Given the matching expansion grouped by the set of branches a
matching enters, together with the bound `|J(M)| ≤ k` supplied by `card_branches_le_of_card`, the
matching polynomial of `G` is divisible by `A ^ (p - k)`.

The expansion is the hypothesis `hexp`; it is what Mathlib cannot state, and it is proved in the
note. Everything downstream of it is here. -/
theorem matching_expansion_dvd {ι : Type*} (A muG : Polynomial R) (T : Finset ι)
    (c : ι → Polynomial R) (touched : ι → ℕ) (p k : ℕ)
    (hexp : muG = ∑ i ∈ T, c i * A ^ (p - touched i))
    (htouch : ∀ i ∈ T, touched i ≤ k) (hk : k ≤ p) :
    A ^ (p - k) ∣ muG := by
  rw [hexp]
  exact dvd_sum_of_pow_terms T A c touched p k htouch hk

/-- **The two-hub instance**, `A ^ (p - 2) ∣ μ_G`, which is the divisor appearing in the two-cut
identity and hence in the 14-vertex counterexample to D3. -/
theorem two_cut_divisor {ι : Type*} (A muG : Polynomial R) (T : Finset ι)
    (c : ι → Polynomial R) (touched : ι → ℕ) (p : ℕ)
    (hexp : muG = ∑ i ∈ T, c i * A ^ (p - touched i))
    (htouch : ∀ i ∈ T, touched i ≤ 2) (hp : 2 ≤ p) :
    A ^ (p - 2) ∣ muG :=
  matching_expansion_dvd A muG T c touched p 2 hexp htouch hp

/-- **The three-hub instance**, `A ^ (p - 3) ∣ μ_G`, which is what makes the 23-vertex graph of
vertex connectivity three a counterexample to C2. -/
theorem three_cut_divisor {ι : Type*} (A muG : Polynomial R) (T : Finset ι)
    (c : ι → Polynomial R) (touched : ι → ℕ) (p : ℕ)
    (hexp : muG = ∑ i ∈ T, c i * A ^ (p - touched i))
    (htouch : ∀ i ∈ T, touched i ≤ 3) (hp : 3 ≤ p) :
    A ^ (p - 3) ∣ muG :=
  matching_expansion_dvd A muG T c touched p 3 hexp htouch hp

/-- **The divisor is nontrivial exactly when `p > k`.**  A root of `A` is a root of `μ_G` only if the
exponent is positive, which is why the construction needs `p ≥ k + 1` branches: at `p = k` the
divisor is `A ^ 0 = 1` and carries nothing. -/
theorem exponent_pos_iff (p k : ℕ) : 0 < p - k ↔ k < p := Nat.sub_pos_iff_lt

end DivisibilityLemma
