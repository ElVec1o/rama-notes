import Mathlib
import RamaLean.Tightness

/-!
# The Plücker bridge

`CrossTerm` states the cross-term theorems for abstract indexed families of vectors
`f`, `w`, `u`.  `Tightness` supplies `f` and `u` as the contractions of a rank-two block,
and `GramDet` discharges the hypothesis `hsimple` in Gram coordinates.  What was left by
hand was the identification of `CrossTerm`'s `w` with a coordinate vector for the bivector
`ω'_k` — the Plücker coordinates.  This file closes that.

The bivector `b₁ ∧ b₂` is represented by the antisymmetric array
`(b₁)_i (b₂)_j - (b₁)_j (b₂)_i` on **ordered** pairs, scaled by `1/√2`.  The scale is
what makes the inner product come out right without any `i < j` bookkeeping: summing an
antisymmetric product over all ordered pairs double counts, and the two factors of
`1/√2` cancel the `2`.  So

  `⟨pl b₁ b₂, pl c₁ c₂⟩ = ⟨b₁,c₁⟩⟨b₂,c₂⟩ - ⟨b₁,c₂⟩⟨b₂,c₁⟩`,

which is the Gram determinant, i.e. the true inner product of the bivectors.

With that, `hsimple` becomes an identity provable by `ring`, once `f` is written in the
plane it lives in.  And `f_k = ι_e ω_k` does lie in the compressed plane, with explicit
coefficients: `f_k = -⟨e,b₂⟩ · b₁' + ⟨e,b₁⟩ · b₂'`.  That is `iota_eq_comb` below, and
`crossTerm_nonneg_plucker` then gives `C_2 ≥ 0` for a tight family of rank-two blocks
with no hypotheses left over at all.
-/

namespace Plucker

open Matrix Finset Tightness

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- Plücker coordinates of `b₁ ∧ b₂`, on ordered pairs, scaled by `1/√2`. -/
noncomputable def pl (b1 b2 : n → ℝ) : (n × n) → ℝ :=
  fun p => (b1 p.1 * b2 p.2 - b1 p.2 * b2 p.1) / Real.sqrt 2

/-- **The Plücker inner product is the Gram determinant.** -/
theorem pl_dot (b1 b2 c1 c2 : n → ℝ) :
    pl b1 b2 ⬝ᵥ pl c1 c2
      = (b1 ⬝ᵥ c1) * (b2 ⬝ᵥ c2) - (b1 ⬝ᵥ c2) * (b2 ⬝ᵥ c1) := by
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have hprod : ∀ A B : n → ℝ, (∑ i, ∑ j, A i * B j) = (∑ i, A i) * (∑ j, B j) :=
    fun A B => (Finset.sum_mul_sum _ _ _ _).symm
  -- the double sum, halved
  have hexp : pl b1 b2 ⬝ᵥ pl c1 c2
      = (∑ i, ∑ j, (b1 i * b2 j - b1 j * b2 i) * (c1 i * c2 j - c1 j * c2 i)) / 2 := by
    rw [dotProduct, Fintype.sum_prod_type, eq_div_iff (by norm_num : (2:ℝ) ≠ 0),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pl]
    field_simp
    rw [h2sq]
    ring
  -- and the double sum splits into four products of sums
  have e1 : (∑ i, ∑ j, (b1 i * b2 j - b1 j * b2 i) * (c1 i * c2 j - c1 j * c2 i))
      = (∑ i, ∑ j, (b1 i * c1 i) * (b2 j * c2 j))
        - (∑ i, ∑ j, (b1 i * c2 i) * (b2 j * c1 j))
        - (∑ i, ∑ j, (b2 i * c1 i) * (b1 j * c2 j))
        + (∑ i, ∑ j, (b2 i * c2 i) * (b1 j * c1 j)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, e1, hprod, hprod, hprod, hprod]
  simp only [dotProduct]
  ring

/-- `f = ι_e ω` lies in the compressed plane, with explicit coefficients. -/
theorem iota_eq_comb (e b1 b2 : n → ℝ) (he : e ⬝ᵥ e = 1) :
    iota e b1 b2
      = (-(e ⬝ᵥ b2)) • proj e b1 + (e ⬝ᵥ b1) • proj e b2 := by
  funext i
  simp only [iota, proj, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **`hsimple`, with no hypotheses left.**  For any `f` in the plane spanned by `b₁, b₂`,
`‖f‖² ‖b₁ ∧ b₂‖² = ‖ι_f (b₁ ∧ b₂)‖²`.  This is the `f ∧ ω = 0` input of the cross-term
theorem, now an identity rather than an assumption. -/
theorem hsimple_of_comb (b1 b2 : n → ℝ) (α β : ℝ) :
    ((α • b1 + β • b2) ⬝ᵥ (α • b1 + β • b2)) * (pl b1 b2 ⬝ᵥ pl b1 b2)
      = (iota (α • b1 + β • b2) b1 b2) ⬝ᵥ (iota (α • b1 + β • b2) b1 b2) := by
  have hpl := pl_dot b1 b2 b1 b2
  have hio : (iota (α • b1 + β • b2) b1 b2) ⬝ᵥ (iota (α • b1 + β • b2) b1 b2)
      = ((α • b1 + β • b2) ⬝ᵥ b1) ^ 2 * (b2 ⬝ᵥ b2)
        - 2 * (((α • b1 + β • b2) ⬝ᵥ b1) * ((α • b1 + β • b2) ⬝ᵥ b2) * (b1 ⬝ᵥ b2))
        + ((α • b1 + β • b2) ⬝ᵥ b2) ^ 2 * (b1 ⬝ᵥ b1) := by
    simp only [iota, dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm b2 b1]
    ring
  rw [hpl, hio]
  simp only [add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  rw [dotProduct_comm b2 b1]
  ring

/-- **The leading cross term is nonnegative, unconditionally.**  For a tight family of
rank-two blocks and any unit vector `e`, with the bivectors given by their Plücker
coordinates, `C_2 ≥ 0`.  Every hypothesis of `CrossTerm.crossTerm_nonneg` is now
discharged: `hsimple` by `hsimple_of_comb` through `iota_eq_comb`, and `htight` by
`Tightness.tight_sum_contraction_eq_zero`. -/
theorem crossTerm_nonneg_plucker [DecidableEq ι]
    (e : n → ℝ) (he : e ⬝ᵥ e = 1) (b1 b2 : ι → n → ℝ) (a : ℝ)
    (htight : ∀ u v : n → ℝ,
      (∑ k, (iota u (b1 k) (b2 k)) ⬝ᵥ (iota v (b1 k) (b2 k))) = a * (u ⬝ᵥ v)) :
    0 ≤ ∑ k, ∑ l ∈ Finset.univ.erase k,
        (((iota e (b1 k) (b2 k)) ⬝ᵥ (iota e (b1 l) (b2 l)))
           * (pl (proj e (b1 k)) (proj e (b2 k)) ⬝ᵥ pl (proj e (b1 l)) (proj e (b2 l)))
         - (iota (iota e (b1 k) (b2 k)) (proj e (b1 k)) (proj e (b2 k)))
           ⬝ᵥ (iota (iota e (b1 l) (b2 l)) (proj e (b1 l)) (proj e (b2 l)))) := by
  refine CrossTerm.crossTerm_nonneg _ _ _ ?_
    (tight_sum_contraction_eq_zero e he b1 b2 a htight)
  intro k
  rw [iota_eq_comb e (b1 k) (b2 k) he]
  exact hsimple_of_comb (proj e (b1 k)) (proj e (b2 k)) (-(e ⬝ᵥ b2 k)) (e ⬝ᵥ b1 k)

end Plucker
