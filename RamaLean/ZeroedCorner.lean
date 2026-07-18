import Mathlib
import RamaLean.TwoGroupFactorial
import RamaLean.Paper3LinearRate
import RamaLean.OddPermanentBound
open Matrix Equiv Finset BigOperators
/-!
# `v₂(per M) ≥ s − 2⌊log₂ s⌋ − 2` for an odd matrix with a zeroed `S×T` corner

If `M k i = 0` on a "corner" `k ∈ S, i ∈ T` and is odd (`2e+1`) off it, then
`2^(s − 2 log₂ s − 2) ∣ per M`.  Column-multilinear expansion `per M = Σ_t 2^{|t|} per(N_t)`
(`N_t = ee` on `t`-columns, `base` on the rest, `base k i = [¬(k∈S ∧ i∈T)]`); the off-`t`
columns of `N_t` fall into **two groups of identical columns** — the corner columns `T\t`
(all equal to `[k∉S]`) and the non-corner columns `tᶜ\T` (all-ones) — so the two-group factorial
`TwoGroup.two_factorial_dvd_permanent` gives `|T\t|! · |tᶜ\T|! ∣ per(N_t)`, and the `2`-adic
bookkeeping yields the bound.  This is the zeroed-corner engine of the `c=1` theorem.
-/

namespace ZeroedCorner

/-- Split a product over `univ` by membership in `t`. -/
lemma prod_split {s : ℕ} (t : Finset (Fin s)) (f g : Fin s → ℤ) :
    (∏ i ∈ t, f i) * (∏ i ∈ tᶜ, g i) = ∏ i, (if i ∈ t then f i else g i) := by
  classical
  rw [Finset.prod_ite]
  congr 1
  · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← Finset.compl_eq_univ_sdiff]

/-- Per-permutation multilinear expansion of `2·ee + base`. -/
lemma prod_add_two_mul {s : ℕ} (base ee : Matrix (Fin s) (Fin s) ℤ) (σ : Perm (Fin s)) :
    (∏ i, (2 * ee (σ i) i + base (σ i) i))
      = ∑ t : Finset (Fin s), 2 ^ t.card *
          ((∏ i ∈ t, ee (σ i) i) * ∏ i ∈ tᶜ, base (σ i) i) := by
  classical
  rw [Finset.prod_add (fun i => (2 : ℤ) * ee (σ i) i) (fun i => base (σ i) i) Finset.univ,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, mul_assoc]

/-- The permanent multilinear expansion over column-subsets. -/
lemma permanent_add_two_mul {s : ℕ} (base ee : Matrix (Fin s) (Fin s) ℤ) :
    (Matrix.of (fun k i => 2 * ee k i + base k i)).permanent
      = ∑ t : Finset (Fin s), 2 ^ t.card *
          (Matrix.of (fun k i => if i ∈ t then ee k i else base k i)).permanent := by
  classical
  simp only [Matrix.permanent, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun σ _ => prod_add_two_mul base ee σ), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  exact prod_split t (fun i => ee (σ i) i) (fun i => base (σ i) i)

/-- **Zeroed-corner bound.**  For any `ee` and any corner `S×T`, with `base = [¬(k∈S ∧ i∈T)]`,
`2^(s − 2⌊log₂ s⌋ − 2) ∣ per(2·ee + base)`.  (Off the corner the matrix is `2·ee+1`, odd;
on it, `2·ee` — the bound holds regardless of `ee` on the corner.) -/
theorem two_pow_dvd_permanent_zeroed {s : ℕ} (ee : Matrix (Fin s) (Fin s) ℤ)
    (S T : Finset (Fin s)) :
    (2 : ℤ) ^ (s - 2 * Nat.log 2 s - 2) ∣
      (Matrix.of (fun k i => 2 * ee k i + (if k ∈ S ∧ i ∈ T then (0 : ℤ) else 1))).permanent := by
  classical
  set base : Matrix (Fin s) (Fin s) ℤ :=
    Matrix.of (fun k i => if k ∈ S ∧ i ∈ T then (0 : ℤ) else 1) with hbase
  have hmat : (Matrix.of (fun k i => 2 * ee k i + (if k ∈ S ∧ i ∈ T then (0 : ℤ) else 1)))
      = Matrix.of (fun k i => 2 * ee k i + base k i) := rfl
  rw [hmat, permanent_add_two_mul base ee]
  apply Finset.dvd_sum
  intro t _
  set Nt : Matrix (Fin s) (Fin s) ℤ :=
    Matrix.of (fun k i => if i ∈ t then ee k i else base k i) with hNt
  -- the two disjoint groups of identical columns of `Nt`: `T \ t` and `tᶜ \ T`
  let ι₁ : Fin (T \ t).card ↪ Fin s :=
    ((T \ t).equivFin.symm).toEmbedding.trans (Function.Embedding.subtype (· ∈ T \ t))
  let ι₂ : Fin (tᶜ \ T).card ↪ Fin s :=
    ((tᶜ \ T).equivFin.symm).toEmbedding.trans (Function.Embedding.subtype (· ∈ tᶜ \ T))
  have hm₁ : ∀ k, ι₁ k ∈ T \ t := fun k => ((T \ t).equivFin.symm k).2
  have hm₂ : ∀ k, ι₂ k ∈ tᶜ \ T := fun k => ((tᶜ \ T).equivFin.symm k).2
  have hdisj : ∀ k₁ k₂, ι₁ k₁ ≠ ι₂ k₂ := by
    intro k₁ k₂ h
    have h1 : ι₁ k₁ ∈ T := (Finset.mem_sdiff.mp (hm₁ k₁)).1
    have h2 : ι₂ k₂ ∉ T := (Finset.mem_sdiff.mp (hm₂ k₂)).2
    rw [h] at h1; exact h2 h1
  -- identical rows of `Ntᵀ` within each group
  have hrow₁ : ∀ (k k' : Fin (T \ t).card) (j : Fin s), Ntᵀ (ι₁ k) j = Ntᵀ (ι₁ k') j := by
    intro k k' j
    have e1 : ι₁ k ∉ t := (Finset.mem_sdiff.mp (hm₁ k)).2
    have e1' : ι₁ k' ∉ t := (Finset.mem_sdiff.mp (hm₁ k')).2
    have i1 : ι₁ k ∈ T := (Finset.mem_sdiff.mp (hm₁ k)).1
    have i1' : ι₁ k' ∈ T := (Finset.mem_sdiff.mp (hm₁ k')).1
    simp only [Matrix.transpose_apply, hNt, hbase, Matrix.of_apply, e1, e1', if_false]
    by_cases hj : j ∈ S <;> simp [hj, i1, i1']
  have hrow₂ : ∀ (k k' : Fin (tᶜ \ T).card) (j : Fin s), Ntᵀ (ι₂ k) j = Ntᵀ (ι₂ k') j := by
    intro k k' j
    have e2 : ι₂ k ∉ t := (Finset.mem_compl.mp (Finset.mem_sdiff.mp (hm₂ k)).1)
    have e2' : ι₂ k' ∉ t := (Finset.mem_compl.mp (Finset.mem_sdiff.mp (hm₂ k')).1)
    have i2 : ι₂ k ∉ T := (Finset.mem_sdiff.mp (hm₂ k)).2
    have i2' : ι₂ k' ∉ T := (Finset.mem_sdiff.mp (hm₂ k')).2
    simp only [Matrix.transpose_apply, hNt, hbase, Matrix.of_apply, e2, e2', if_false]
    simp [i2, i2']
  have hdvd := TwoGroup.two_factorial_dvd_permanent Ntᵀ ι₁ ι₂ hdisj hrow₁ hrow₂
  rw [Matrix.permanent_transpose] at hdvd
  -- now the 2-adic bound: 2^(s−2log−2) | 2^|t| · ((T\t)! · (tᶜ\T)!) | 2^|t| · per(Nt)
  set a := (T \ t).card with ha
  set b := (tᶜ \ T).card with hb
  have hunion : (T \ t) ∪ (tᶜ \ T) = tᶜ := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]; tauto
  have hdisjoint : Disjoint (T \ t) (tᶜ \ T) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1
  have hab : a + b = s - t.card := by
    rw [ha, hb, ← Finset.card_union_of_disjoint hdisjoint, hunion, Finset.card_compl,
        Fintype.card_fin]
  have has : a ≤ s := (Finset.card_le_univ _).trans_eq (by simp)
  have hbs : b ≤ s := (Finset.card_le_univ _).trans_eq (by simp)
  have htc : t.card ≤ s := (Finset.card_le_univ t).trans_eq (by simp)
  -- 2^(t.card + (a−s₂a) + (b−s₂b)) divides the term
  have h1 : (2 : ℤ) ^ (t.card + ((a - (Nat.digits 2 a).sum) + (b - (Nat.digits 2 b).sum)))
      ∣ 2 ^ t.card * Nt.permanent := by
    rw [pow_add]
    refine mul_dvd_mul_left _ ?_
    have hfa : (2 : ℤ) ^ (a - (Nat.digits 2 a).sum) ∣ (a.factorial : ℤ) := by
      exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial a
    have hfb : (2 : ℤ) ^ (b - (Nat.digits 2 b).sum) ∣ (b.factorial : ℤ) := by
      exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial b
    have hfac : (2 : ℤ) ^ ((a - (Nat.digits 2 a).sum) + (b - (Nat.digits 2 b).sum))
        ∣ (a.factorial * b.factorial : ℤ) := by
      rw [pow_add]; exact mul_dvd_mul hfa hfb
    exact hfac.trans hdvd
  refine dvd_trans (pow_dvd_pow 2 ?_) h1
  -- s − 2log − 2 ≤ t.card + (a−s₂a) + (b−s₂b) = s − s₂a − s₂b
  have hsa : (Nat.digits 2 a).sum ≤ Nat.log 2 s + 1 := by
    rcases eq_or_ne a 0 with h0 | h0
    · simp [h0]
    · have hd := Paper3Linear.digitsum_le_log_succ a h0
      have hlog : Nat.log 2 a ≤ Nat.log 2 s := Nat.log_mono_right has
      omega
  have hsb : (Nat.digits 2 b).sum ≤ Nat.log 2 s + 1 := by
    rcases eq_or_ne b 0 with h0 | h0
    · simp [h0]
    · have hd := Paper3Linear.digitsum_le_log_succ b h0
      have hlog : Nat.log 2 b ≤ Nat.log 2 s := Nat.log_mono_right hbs
      omega
  have hda : (Nat.digits 2 a).sum ≤ a := Nat.digit_sum_le 2 a
  have hdb : (Nat.digits 2 b).sum ≤ b := Nat.digit_sum_le 2 b
  omega

end ZeroedCorner
