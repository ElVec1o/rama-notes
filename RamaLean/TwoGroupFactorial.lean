import Mathlib
import RamaLean.OrbitSumDivisibility
import RamaLean.PermanentFactorial
open Equiv Equiv.Perm Matrix
/-!
# `a!·b! ∣ per M` for two disjoint groups of identical rows

Generalises `factorial_dvd_permanent_of_ones_rows` (one all-ones group) to **two** disjoint
groups of *identical* rows.  The group `Perm (Fin a) × Perm (Fin b)` acts freely on
`Perm (Fin n)` by `(π₁,π₂) • σ = (viaEmbedding ι₁ π₁ · viaEmbedding ι₂ π₂) · σ` (the two
embeddings have disjoint ranges, so the extensions commute); the permanent summand
`∏ᵢ M (σ i) i` is invariant because permuting identical rows leaves each factor unchanged.
`card_dvd_sum_of_free_invariant` then gives `|G| = a!·b! ∣ per M`.

This is the engine for the zeroed-corner bound `v₂(per) ≥ s − 2log` (row-multilinear expansion
of an odd matrix with a zeroed corner: each term has a group of identical corner mask-rows
`[0,…,0,1,…,1]` and a group of identical all-ones mask-rows), hence for the `c=1` theorem.
-/

namespace TwoGroup

/-- Two disjoint groups of identical rows ⟹ `a!·b! ∣ per M`. -/
theorem two_factorial_dvd_permanent {n a b : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (ι₁ : Fin a ↪ Fin n) (ι₂ : Fin b ↪ Fin n)
    (hdisj : ∀ (k₁ : Fin a) (k₂ : Fin b), ι₁ k₁ ≠ ι₂ k₂)
    (h₁ : ∀ (k k' : Fin a) (j : Fin n), M (ι₁ k) j = M (ι₁ k') j)
    (h₂ : ∀ (k k' : Fin b) (j : Fin n), M (ι₂ k) j = M (ι₂ k') j) :
    (a.factorial * b.factorial : ℤ) ∣ M.permanent := by
  classical
  -- `ι₁ k` is never in the range of `ι₂` and vice versa
  have hnr₂ : ∀ k : Fin a, (ι₁ k : Fin n) ∉ Set.range ι₂ := by
    rintro k ⟨k', hk'⟩; exact hdisj k k' hk'.symm
  have hnr₁ : ∀ k : Fin b, (ι₂ k : Fin n) ∉ Set.range ι₁ := by
    rintro k ⟨k', hk'⟩; exact hdisj k' k hk'
  -- the two extended permutations commute (disjoint supports)
  have hcomm : ∀ (π₁ : Perm (Fin a)) (π₂ : Perm (Fin b)),
      Commute (viaEmbeddingHom ι₁ π₁) (viaEmbeddingHom ι₂ π₂) := by
    intro π₁ π₂
    apply Equiv.Perm.Disjoint.commute
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro x
    by_cases hx : x ∈ Set.range ι₁
    · right
      obtain ⟨k, rfl⟩ := hx
      rw [viaEmbeddingHom_apply, viaEmbedding_apply_of_notMem _ _ _ (hnr₂ k)]
    · left
      rw [viaEmbeddingHom_apply, viaEmbedding_apply_of_notMem _ _ _ hx]
  -- the product-group hom into `Perm (Fin n)`
  set φ : (Perm (Fin a) × Perm (Fin b)) →* Perm (Fin n) :=
    MonoidHom.noncommCoprod (viaEmbeddingHom ι₁) (viaEmbeddingHom ι₂) hcomm with hφdef
  have hφ : ∀ (π₁ : Perm (Fin a)) (π₂ : Perm (Fin b)),
      φ (π₁, π₂) = viaEmbeddingHom ι₁ π₁ * viaEmbeddingHom ι₂ π₂ := by
    intro π₁ π₂; rw [hφdef, MonoidHom.noncommCoprod_apply]
  letI : MulAction (Perm (Fin a) × Perm (Fin b)) (Perm (Fin n)) :=
    MulAction.compHom (Perm (Fin n)) φ
  have hsmul : ∀ (g : Perm (Fin a) × Perm (Fin b)) (σ : Perm (Fin n)), g • σ = φ g * σ :=
    fun _ _ => rfl
  -- key: `φ g` sends `σ i` to a row equal to it (identical-row invariance)
  have hroweq : ∀ (π₁ : Perm (Fin a)) (π₂ : Perm (Fin b)) (y : Fin n) (i : Fin n),
      M (φ (π₁, π₂) y) i = M y i := by
    intro π₁ π₂ y i
    rw [hφ, Perm.mul_apply]
    simp only [viaEmbeddingHom_apply]
    by_cases hy₁ : y ∈ Set.range ι₁
    · obtain ⟨k, rfl⟩ := hy₁
      rw [viaEmbedding_apply_of_notMem _ _ _ (hnr₂ k), viaEmbedding_apply]
      exact h₁ (π₁ k) k i
    · by_cases hy₂ : y ∈ Set.range ι₂
      · obtain ⟨k, rfl⟩ := hy₂
        rw [viaEmbedding_apply, viaEmbedding_apply_of_notMem _ _ _ (hnr₁ (π₂ k))]
        exact h₂ (π₂ k) k i
      · rw [viaEmbedding_apply_of_notMem _ _ _ hy₂, viaEmbedding_apply_of_notMem _ _ _ hy₁]
  -- invariance of the permanent summand
  have hf : ∀ (g : Perm (Fin a) × Perm (Fin b)) (σ : Perm (Fin n)),
      (∏ i, M ((g • σ) i) i) = ∏ i, M (σ i) i := by
    rintro ⟨π₁, π₂⟩ σ
    rw [hsmul]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Perm.mul_apply]
    exact hroweq π₁ π₂ (σ i) i
  -- freeness: the action is free
  have hfree : ∀ σ : Perm (Fin n),
      MulAction.stabilizer (Perm (Fin a) × Perm (Fin b)) σ = ⊥ := by
    intro σ
    rw [eq_bot_iff]
    rintro ⟨π₁, π₂⟩ hg
    have hg1 : φ (π₁, π₂) * σ = σ := hg
    have hφ1 : φ (π₁, π₂) = 1 := by
      have h2 : φ (π₁, π₂) * σ = 1 * σ := by rw [hg1, one_mul]
      exact mul_right_cancel h2
    rw [hφ] at hφ1
    -- π₁ = 1 : evaluate at ι₁ k
    have hπ₁ : π₁ = 1 := Equiv.ext fun k => by
      have hev := congrArg (fun p => p (ι₁ k)) hφ1
      simp only [Perm.mul_apply, Perm.one_apply, viaEmbeddingHom_apply] at hev
      rw [viaEmbedding_apply_of_notMem _ _ _ (hnr₂ k), viaEmbedding_apply] at hev
      rw [Perm.one_apply]
      exact ι₁.injective hev
    subst hπ₁
    -- now viaEmbedding ι₂ π₂ = 1
    have hπ₂ : viaEmbeddingHom ι₂ π₂ = 1 := by simpa using hφ1
    have hpi2 : π₂ = 1 := viaEmbeddingHom_injective ι₂ (by simpa using hπ₂)
    subst hpi2
    exact Subgroup.mem_bot.mpr rfl
  have hcard : Fintype.card (Perm (Fin a) × Perm (Fin b)) = a.factorial * b.factorial := by
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
        Fintype.card_fin]
  have hdvd := card_dvd_sum_of_free_invariant (G := Perm (Fin a) × Perm (Fin b))
    (X := Perm (Fin n)) hfree (fun σ => ∏ i, M (σ i) i) hf
  rw [hcard] at hdvd
  push_cast at hdvd
  simpa [Matrix.permanent] using hdvd

end TwoGroup
