import Mathlib
import RamaLean.PermanentFactorial
import RamaLean.Paper3LinearRate
open Matrix Equiv Finset BigOperators
/-!
# `v₂(per M) ≥ n − ⌊log₂ n⌋ − 1` for any ALL-ODD matrix `M`

If every entry of an `n×n` integer matrix is odd (`M = 2e + 1`), then
`2^(n − ⌊log₂ n⌋ − 1) ∣ per M`.  Proof: `per(2e+1) = Σ_t 2^{|t|} per(M_t)` (multilinear
`Finset.prod_add` expansion), where `M_t` has `n−|t|` all-ones columns, so `(n−|t|)! ∣ per(M_t)`
(`factorial_dvd_permanent_of_ones_rows`); combine with `v₂((n−|t|)!) = (n−|t|) − s₂(n−|t|)` and
`s₂ ≤ log₂+1`.  This is the engine behind the `c=1` attack on `a(n)=per[gcd]`: the `w=0` grade
is `per(M₁)²` with `M₁` all-odd, so `v₂(N₀) = 2·v₂(per M₁) ≥ n − O(log)`.
-/
namespace OddPerm

/-- Per-permutation multilinear expansion:
`∏ᵢ (2·e(σi,i)+1) = Σ_t 2^{|t|} ∏_{i∈t} e(σi,i)`. -/
lemma prod_two_mul_add_one {n : ℕ} (e : Matrix (Fin n) (Fin n) ℤ) (σ : Perm (Fin n)) :
    (∏ i, (2 * e (σ i) i + 1))
      = ∑ t : Finset (Fin n), 2 ^ t.card * ∏ i ∈ t, e (σ i) i := by
  classical
  rw [Finset.prod_add (fun i => (2:ℤ) * e (σ i) i) (fun _ => (1:ℤ)) Finset.univ,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Multilinear expansion of the permanent of `2e+1` over column-subsets. -/
lemma permanent_two_mul_add_one {n : ℕ} (e : Matrix (Fin n) (Fin n) ℤ) :
    (Matrix.of (fun k i => 2 * e k i + 1)).permanent
      = ∑ t : Finset (Fin n), 2 ^ t.card *
          (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
  classical
  simp only [Matrix.permanent, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun σ _ => prod_two_mul_add_one e σ), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- Each column-subset term has `(n − |t|)!` dividing its permanent (the `n−|t|` columns off
`t` are all-ones). -/
lemma factorial_dvd_permanent_off (n : ℕ) (e : Matrix (Fin n) (Fin n) ℤ) (t : Finset (Fin n)) :
    ((n - t.card).factorial : ℤ)
      ∣ (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
  classical
  -- the complement `tᶜ` indexes `n − |t|` all-ones columns; transpose ⟹ all-ones rows
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun k i => if i ∈ t then e k i else 1) with hM
  have hcard : (tᶜ.card).factorial = (n - t.card).factorial := by
    rw [Finset.card_compl, Fintype.card_fin]
  let ι : Fin tᶜ.card ↪ Fin n :=
    (tᶜ.equivFin.symm).toEmbedding.trans (Function.Embedding.subtype (· ∈ tᶜ))
  have hrow : ∀ (k : Fin tᶜ.card) (j : Fin n), Mᵀ (ι k) j = 1 := by
    intro k j
    have hmem : ι k ∈ tᶜ := (tᶜ.equivFin.symm k).2
    have : ι k ∉ t := by simpa using hmem
    simp [hM, Matrix.transpose_apply, this]
  have hd := factorial_dvd_permanent_of_ones_rows Mᵀ ι hrow
  rw [hcard] at hd
  rwa [Matrix.permanent_transpose] at hd

/-- **All-odd matrix ⟹ `v₂(per) ≥ n − log₂ n − 1`.**  `2^(n − ⌊log₂ n⌋ − 1) ∣ per(2e+1)`. -/
theorem two_pow_dvd_permanent_odd {n : ℕ} (e : Matrix (Fin n) (Fin n) ℤ) :
    (2 : ℤ) ^ (n - Nat.log 2 n - 1) ∣ (Matrix.of (fun k i => 2 * e k i + 1)).permanent := by
  classical
  rw [permanent_two_mul_add_one]
  apply Finset.dvd_sum
  intro t _
  -- 2^(|t|) · (n−|t|)!  divides the term;  its v₂ ≥ n − log − 1
  have h1 : (2 : ℤ) ^ (t.card + (n - t.card - (Nat.digits 2 (n - t.card)).sum))
      ∣ 2 ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
    rw [pow_add]
    refine mul_dvd_mul_left _ ?_
    have hf : (2:ℤ) ^ (n - t.card - (Nat.digits 2 (n - t.card)).sum)
        ∣ ((n - t.card).factorial : ℤ) := by
      exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial (n - t.card)
    exact hf.trans (factorial_dvd_permanent_off n e t)
  refine dvd_trans (pow_dvd_pow 2 ?_) h1
  -- n − log − 1 ≤ |t| + (n−|t|) − s₂(n−|t|)
  have hs : (Nat.digits 2 (n - t.card)).sum ≤ Nat.log 2 n + 1 := by
    rcases eq_or_ne (n - t.card) 0 with h0 | h0
    · simp [h0]
    · exact le_trans (Paper3Linear.digitsum_le_log_succ _ h0)
        (by gcongr; exact Nat.sub_le _ _)
  have htc : t.card ≤ n := (Finset.card_le_univ t).trans_eq (by simp)
  have hds : (Nat.digits 2 (n - t.card)).sum ≤ n - t.card := Nat.digit_sum_le 2 _
  omega

end OddPerm
