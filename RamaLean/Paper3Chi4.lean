import Mathlib
open Finset BigOperators

/-!
# The `χ₄` foundation of the deficit-parity mechanism

The 2-adic deficit of the gcd permanent at `n = 2^k+1` is `2k−4` exactly when an "achiever count"
`C(k)` is odd (Paper 3, §7). That count is `Σ_v P₁(v)P₂(v)` where `P₁(v) = π₁(A_v) mod 2` for an
all-odd matrix `A_v`. The two lemmas here formalize the rigorous *entry point* of the arithmetic
mechanism: because a `gcd` of two odds is odd and `(g−1)/2` is odd iff `g ≡ 3 (mod 4)`, the parity of
`π₁ = Σ (g−1)/2` equals the parity of the **number of entries `≡ 3 (mod 4)`** — i.e. it is a count
weighted by the non-principal character `χ₄` mod 4.

From here (developed on paper in the note) a Dirichlet convolution `χ₄ = 1 * (χ₄∗μ)` collapses the
count, modulo 2, to `Σ_{q^a | v, q≡3(4)} ⌊2^{k−1}/q^a⌋`, whose terms are binary digits of `1/q^a`
(period `ord_{q^a}(2)`) — tying the whole question to the multiplicative orders of `2` (Artin
territory). That collapse uses Mathlib's `ArithmeticFunction` machinery and is left as a larger
formalization; the character-count reduction below is its foundation.
-/
namespace Paper3Chi4

/-- The `χ₄` characterization: for odd `g`, `(g−1)/2` is odd iff `g ≡ 3 (mod 4)`. -/
lemma odd_half_iff {g : ℕ} (hg : Odd g) : Odd ((g - 1) / 2) ↔ g % 4 = 3 := by
  obtain ⟨t, rfl⟩ := hg
  have h : (2 * t + 1 - 1) / 2 = t := by omega
  rw [h, Nat.odd_iff]; omega

/-- Parity of `Σ (gᵢ−1)/2` over odd values equals the parity of `#{ i : gᵢ ≡ 3 (mod 4) }`.
Applied to the entries of an all-odd matrix, this makes `π₁ mod 2` a `χ₄`-count. -/
lemma sum_half_parity {ι : Type*} (s : Finset ι) (M : ι → ℕ) (hM : ∀ i ∈ s, Odd (M i)) :
    (∑ i ∈ s, (M i - 1) / 2) % 2 = (s.filter (fun i => M i % 4 = 3)).card % 2 := by
  have hpt : ∀ i ∈ s, (M i - 1) / 2 % 2 = (if M i % 4 = 3 then 1 else 0) := by
    intro i hi
    have hiff := odd_half_iff (hM i hi)
    rw [Nat.odd_iff] at hiff
    by_cases h : M i % 4 = 3
    · simp [h, hiff.mpr h]
    · simp only [h, if_false]
      have hne : (M i - 1) / 2 % 2 ≠ 1 := fun hh => h (hiff.mp hh)
      omega
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl hpt, Finset.sum_boole, Nat.cast_id]

end Paper3Chi4
