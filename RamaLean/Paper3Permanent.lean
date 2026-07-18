/-
# Paper 3, Theorem 3 — reusable ingredients toward Lemma A

Paper 3's Theorem 3 (`3 ∣ a(n)` for `n ≥ 13`, and the general prime-`p`
congruence family) rests on **Lemma A**: over `ZMod p`, if `p` columns of a
matrix are equal, its permanent is `0`. Mathlib has `Matrix.permanent`, so this
is formalizable; the crux is a free `ℤ/p` orbit argument on `Perm (Fin n)`.

The full lemma `permanent_eq_zero_of_col_period` is proved below (no `sorry`,
standard axioms only): the summand is invariant under right multiplication by
`c` (`summand_invariant`, `summand_zpow`), so it is constant on each left coset
of `⟨c⟩`; each coset has `orderOf c = p` elements, and `p • (·) = 0` in `ZMod p`.

* `permanent_eq_zero_of_col_period` — Lemma A: a column period of order `p`
  forces `permanent = 0` over `ZMod p`. Applying it with `c` a `p`-cycle through
  `p` equal columns is exactly "`≥ p` equal columns mod `p` ⟹ `p ∣ permanent`",
  the engine of Paper 3 Theorem 3 (`3 ∣ a(n)` for `n ≥ 13`).
* `permanent_eq_zero_of_two_cols_eq` — the `p = 2` case via a transposition,
  i.e. the parity mechanism.

The only unformalized parts of Theorem 3 are then the elementary number theory
(Lemma B: which gcd-columns collide mod `p`) and the "type-A" count — the
substance, Lemma A, is machine-checked here. Numerically cross-checked in
`code/verify_mod3_theorem.py`.
-/
import Mathlib

open Matrix Equiv Finset

namespace Paper3

variable {n : ℕ}

/-- The permanent summand `∏ i, M (σ i) i` is invariant under right
multiplication by a column period `c` (a `c` with `M i (c j) = M i j` for all
`i, j` — e.g. `c` permuting a set of equal columns). Over any commutative ring. -/
lemma summand_invariant {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (c : Perm (Fin n))
    (hM : ∀ i j, M i (c j) = M i j) (σ : Perm (Fin n)) :
    (∏ i, M ((σ * c) i) i) = ∏ i, M (σ i) i := by
  have step1 : (∏ i, M ((σ * c) i) i) = ∏ j, M (σ j) (c⁻¹ j) := by
    rw [← Equiv.prod_comp c (fun j => M (σ j) (c⁻¹ j))]
    apply Finset.prod_congr rfl
    intro i _
    simp [Perm.mul_apply]
  rw [step1]
  apply Finset.prod_congr rfl
  intro j _
  simpa using (hM (σ j) (c⁻¹ j)).symm

/-- Iterated invariance: the summand is invariant under `σ ↦ σ · cᵏ` for every
integer `k`. -/
lemma summand_zpow {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (c : Perm (Fin n))
    (hM : ∀ i j, M i (c j) = M i j) :
    ∀ (k : ℤ) (σ : Perm (Fin n)), (∏ i, M ((σ * c ^ k) i) i) = ∏ i, M (σ i) i := by
  intro k
  refine Int.induction_on k ?_ ?_ ?_
  · intro σ; simp
  · intro m ih σ
    rw [_root_.zpow_add_one, ← mul_assoc, summand_invariant M c hM (σ * c ^ (m : ℤ)), ih σ]
  · intro m ih σ
    have h := summand_invariant M c hM (σ * c ^ (-(m : ℤ) - 1))
    rw [mul_assoc, ← _root_.zpow_add_one, show (-(m : ℤ) - 1) + 1 = -(m : ℤ) by ring] at h
    rw [← h]; exact ih σ

/-- **Lemma A.** Over `ZMod p` (p prime): if `c : Perm (Fin n)` has order `p`
and fixes every column of `M` (`M i (c j) = M i j`), then `M.permanent = 0`.
With `c` a `p`-cycle through `p` equal columns, this is "`≥ p` equal columns
mod `p` ⟹ `p ∣ permanent`". -/
theorem permanent_eq_zero_of_col_period {p : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p))
    (c : Perm (Fin n)) (hc : orderOf c = p) (hM : ∀ i j, M i (c j) = M i j) :
    M.permanent = 0 := by
  classical
  set H := Subgroup.zpowers c with hH
  set f : Perm (Fin n) → ZMod p := fun σ => ∏ i, M (σ i) i with hf
  let π : Perm (Fin n) → Perm (Fin n) ⧸ H := fun σ => (σ : Perm (Fin n) ⧸ H)
  -- each fibre (coset) contributes 0
  have fiber_zero : ∀ σ₀ : Perm (Fin n),
      (∑ σ ∈ univ.filter (fun σ => π σ = π σ₀), f σ) = 0 := by
    intro σ₀
    have hmem : ∀ {σ : Perm (Fin n)}, π σ = π σ₀ → σ₀⁻¹ * σ ∈ H := by
      intro σ hσ
      have h1 : σ⁻¹ * σ₀ ∈ H := QuotientGroup.eq.mp hσ
      simpa [_root_.mul_inv_rev] using H.inv_mem h1
    -- reindex the coset by the subgroup H
    have hb : (∑ σ ∈ univ.filter (fun σ => π σ = π σ₀), f σ)
        = ∑ h : H, f (σ₀ * (h : Perm (Fin n))) := by
      refine Finset.sum_bij' (fun σ hσ => (⟨σ₀⁻¹ * σ, hmem (by simpa using hσ)⟩ : H))
        (fun h _ => σ₀ * (h : Perm (Fin n))) ?_ ?_ ?_ ?_ ?_
      · intro σ hσ; exact mem_univ _
      · intro h _
        simp only [mem_filter, mem_univ, true_and]
        show (↑(σ₀ * (h : Perm (Fin n))) : Perm (Fin n) ⧸ H) = (↑σ₀ : Perm (Fin n) ⧸ H)
        rw [QuotientGroup.eq]
        simpa using H.inv_mem h.2
      · intro σ hσ; simp
      · intro h _; simp
      · intro σ hσ; simp only [hf, mul_inv_cancel_left]
    rw [hb]
    have hconst : ∀ h : H, f (σ₀ * (h : Perm (Fin n))) = f σ₀ := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
      show (∏ i, M ((σ₀ * (h : Perm (Fin n))) i) i) = ∏ i, M (σ₀ i) i
      rw [← hk]
      exact summand_zpow M c hM k σ₀
    rw [Finset.sum_congr rfl (fun h _ => hconst h), Finset.sum_const, Finset.card_univ,
      Fintype.card_zpowers, hc, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  -- assemble via the fibrewise decomposition over the quotient
  have hmaps : ∀ σ ∈ (univ : Finset (Perm (Fin n))), π σ ∈ (univ : Finset _) :=
    fun σ _ => mem_univ _
  rw [Matrix.permanent, ← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_eq_zero fun L _ => ?_
  obtain ⟨σ₀, rfl⟩ := QuotientGroup.mk_surjective L
  exact fiber_zero σ₀

/-- The `p = 2` specialization (via the transposition of the two columns): a
matrix over `ZMod 2` with two equal columns has permanent `0`. This is the
parity mechanism — `2 ∣ perm[gcd(i,j)]` for `n ≥ 3` because any two odd columns
are `≡ (1,…,1) (mod 2)`. -/
theorem permanent_eq_zero_of_two_cols_eq (M : Matrix (Fin n) (Fin n) (ZMod 2))
    {j₁ j₂ : Fin n} (hne : j₁ ≠ j₂) (heq : ∀ i, M i j₁ = M i j₂) :
    M.permanent = 0 := by
  refine permanent_eq_zero_of_col_period M (Equiv.swap j₁ j₂) ?_ ?_
  · refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]; exact Equiv.swap_mul_self j₁ j₂
    · intro hcon
      apply hne
      have h := Equiv.swap_apply_left j₁ j₂
      rw [hcon] at h
      simpa using h
  · intro i j
    rcases eq_or_ne j j₁ with rfl | hj1
    · rw [Equiv.swap_apply_left]; exact (heq i).symm
    · rcases eq_or_ne j j₂ with rfl | hj2
      · rw [Equiv.swap_apply_right]; exact heq i
      · rw [Equiv.swap_apply_of_ne_of_ne hj1 hj2]

end Paper3
