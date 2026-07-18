import Mathlib
import RamaLean.ZeroedCorner
import RamaLean.Paper3FourDivides
open Matrix Finset Paper3Four
/-!
# `c = 1`, machine-checked:  `v₂(a(n)) ≥ n − 2⌊log₂ n⌋ − 2`

The 2-adic valuation of `a(n) = per[gcd(i,j)]` grows **linearly with rate 1**, `v₂(a(n))/n → 1`
(improving the machine-checked `c = ½`).  The proof is a *direct* application of the zeroed-corner
engine: `gcd(k+1,i+1)` is even **iff both `k+1` and `i+1` are even**, so the gcd matrix is exactly
a zeroed-corner matrix `2·ee + [¬(k,i both even)]` with corner `S×S`, `S = {even indices}`.
`ZeroedCorner.two_pow_dvd_permanent_zeroed` (built on the two-group factorial
`|S\t|!·|Sᶜ\t|!∣per`) then gives the bound with no further work — the even→even cancellation the
hand proof organised by permutation grade is captured abstractly by the two identical mask-column
groups.
-/

namespace Paper3C1

/-- **`c = 1`.**  `2^(n − 2⌊log₂ n⌋ − 2) ∣ a(n)`, hence `v₂(a(n))/n → 1`. -/
theorem two_pow_dvd_permanent_c1 (n : ℕ) :
    (2 : ℤ) ^ (n - 2 * Nat.log 2 n - 2) ∣ (gcdMat n).permanent := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun i => 2 ∣ ((i : ℕ) + 1)) with hS
  have hmem : ∀ j : Fin n, j ∈ S ↔ 2 ∣ ((j : ℕ) + 1) := by
    intro j; rw [hS, Finset.mem_filter]; simp
  -- `2 ∣ gcd(k+1,i+1)` iff both indices are even
  have hgcd_even : ∀ k i : Fin n,
      (2 : ℕ) ∣ Nat.gcd ((k : ℕ) + 1) ((i : ℕ) + 1) ↔ (k ∈ S ∧ i ∈ S) := by
    intro k i
    rw [hmem, hmem]
    exact ⟨fun hd => ⟨hd.trans (Nat.gcd_dvd_left _ _), hd.trans (Nat.gcd_dvd_right _ _)⟩,
           fun ⟨ha, hb⟩ => Nat.dvd_gcd ha hb⟩
  -- `2 ∣ (gcd − base)` where `base = [¬(k∈S ∧ i∈S)]`
  have key : ∀ k i : Fin n,
      (2 : ℤ) ∣ ((gcdMat n) k i - (if k ∈ S ∧ i ∈ S then (0 : ℤ) else 1)) := by
    intro k i
    have hg : (gcdMat n) k i = (Nat.gcd ((k : ℕ) + 1) ((i : ℕ) + 1) : ℤ) := rfl
    by_cases h : k ∈ S ∧ i ∈ S
    · rw [if_pos h, sub_zero, hg]
      exact_mod_cast (hgcd_even k i).mpr h
    · rw [if_neg h, hg]
      have hnd : ¬ (2 : ℕ) ∣ Nat.gcd ((k : ℕ) + 1) ((i : ℕ) + 1) :=
        fun hd => h ((hgcd_even k i).mp hd)
      obtain ⟨m, hm⟩ := (Nat.even_or_odd _).resolve_left (fun he => hnd he.two_dvd)
      rw [hm]; push_cast; exact ⟨(m : ℤ), by ring⟩
  -- realise the gcd matrix as `2·ee + base`
  set ee : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of (fun k i => ((gcdMat n) k i - (if k ∈ S ∧ i ∈ S then (0 : ℤ) else 1)) / 2) with hee
  have hform : gcdMat n
      = Matrix.of (fun k i => 2 * ee k i + (if k ∈ S ∧ i ∈ S then (0 : ℤ) else 1)) := by
    ext k i
    simp only [hee, Matrix.of_apply]
    rw [Int.mul_ediv_cancel' (key k i)]
    ring
  rw [hform]
  exact ZeroedCorner.two_pow_dvd_permanent_zeroed ee S S

end Paper3C1
