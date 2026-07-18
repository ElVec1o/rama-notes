import Mathlib
import RamaLean.OrbitSumDivisibility
open Equiv Equiv.Perm Matrix
/-!
# `c! ∣ per M` when `c` rows are all-ones

The machine-checked **kernel** of the linear 2-adic lower bound
`v₂(a(n)) ≥ ⌈n/2⌉ − ⌊log₂ n⌋ − 1` for `a(n) = per[gcd(i,j)]`.  In the divisor-filtration
`a(n) = Σ_d (∏ φ(d_i)) · per(M_d)`, the columns with `d_i = 1` are all-ones, so this lemma
(applied to `M_dᵀ`) gives `c₁! ∣ per(M_d)`, hence `v₂ ≥ v₂(c₁!) = c₁ − s₂(c₁)`; combined
with `φ(≥3)` even and `c₁ + c₃ ≥ ⌈n/2⌉` this yields the linear bound (see
`code/v2_linear_rate_proof.md`).  Standard axioms, no `sorry`.
-/

/-- If `c` rows of an `n×n` integer matrix are all-ones (indexed by an embedding
`ι : Fin c ↪ Fin n`), then `c! ∣ per M`.  Proof: `Perm (Fin c)` acts freely on
`Perm (Fin n)` by `τ • σ = (viaEmbeddingHom ι τ) * σ`; the summand `∏ᵢ M (σ i) i` is
invariant (an all-ones row contributes factor `1` however it is permuted), so the
abstract kernel `card_dvd_sum_of_free_invariant` gives `|Perm (Fin c)| = c! ∣ per M`. -/
theorem factorial_dvd_permanent_of_ones_rows {n c : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (ι : Fin c ↪ Fin n) (hrow : ∀ (k : Fin c) (j : Fin n), M (ι k) j = 1) :
    (c.factorial : ℤ) ∣ M.permanent := by
  classical
  letI : MulAction (Perm (Fin c)) (Perm (Fin n)) :=
    MulAction.compHom (Perm (Fin n)) (viaEmbeddingHom ι)
  have hsmul : ∀ (τ : Perm (Fin c)) (σ : Perm (Fin n)), τ • σ = viaEmbeddingHom ι τ * σ :=
    fun _ _ => rfl
  have hfree : ∀ σ : Perm (Fin n), MulAction.stabilizer (Perm (Fin c)) σ = ⊥ := by
    intro σ
    rw [eq_bot_iff]; intro τ hτ
    rw [MulAction.mem_stabilizer_iff, hsmul] at hτ
    rw [Subgroup.mem_bot]
    exact viaEmbeddingHom_injective ι (by rw [map_one]; exact mul_right_cancel hτ)
  have hinv : ∀ (τ : Perm (Fin c)) (σ : Perm (Fin n)),
      (fun σ : Perm (Fin n) => ∏ i, M (σ i) i) (τ • σ)
        = (fun σ : Perm (Fin n) => ∏ i, M (σ i) i) σ := by
    intro τ σ
    simp only [hsmul]
    apply Finset.prod_congr rfl
    intro i _
    rw [Perm.mul_apply, viaEmbeddingHom_apply]
    by_cases hσi : σ i ∈ Set.range ι
    · obtain ⟨k, hk⟩ := hσi
      rw [← hk, viaEmbedding_apply, hrow (τ k) i, hrow k i]
    · rw [viaEmbedding_apply_of_notMem τ ι (σ i) hσi]
  have hcard : Fintype.card (Perm (Fin c)) = c.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hdvd := card_dvd_sum_of_free_invariant hfree (fun σ => ∏ i, M (σ i) i) hinv
  rw [hcard] at hdvd
  rwa [Matrix.permanent]
