import Mathlib
import RamaLean.AdjugatePSD

/-!
# The exterior-algebra inputs, in Gram coordinates

The cross-term theorems rest on three facts about multivectors.  Written in Gram
coordinates every one of them becomes a determinant statement, and this file proves
them, so that `CrossTerm`'s hypotheses `hsimple` are discharged rather than assumed.

For decomposable multivectors, `⟨u_1 ∧ ⋯ ∧ u_p, w_1 ∧ ⋯ ∧ w_p⟩ = det (⟨u_i, w_j⟩)`.  So:

* the identity `⟨u ∧ α, w ∧ γ⟩ = ⟨u,w⟩⟨α,γ⟩ - ⟨ι_w α, ι_u γ⟩`, which drives the whole
  computation, is exactly the **bordered determinant formula**

    `det [[a, rᵀ], [c, G]] = a · det G - rᵀ (adj G) c`,                          (†)

  with `a = ⟨u,w⟩`, `r_j = ⟨u, c_j⟩`, `c_i = ⟨a_i, w⟩`, `G_{ij} = ⟨a_i, c_j⟩`;
* `‖f‖²‖α‖² = ‖ι_f α‖² + ‖f ∧ α‖²` for simple `α` is (†) with `u = w = f`, `α = γ`;
* `f_k ∧ ω'_k = 0` is the vanishing of a Gram determinant on a dependent family, since
  `f_k = ι_e ω_k` lies in the plane of `ω'_k`.

Combining the last two gives `‖f_k‖²‖ω'_k‖² = ‖ι_{f_k} ω'_k‖²`, which is precisely the
hypothesis `hsimple` of `CrossTerm.crossTerm_eq_sq`.  That is `hsimple_of_border_zero`
below.

Scope.  (†) is proved for `IsUnit G.det`, which is the case that occurs: `G` is the Gram
matrix of the compressed block, invertible exactly when the block does not degenerate,
and when it does degenerate `ω'_k = 0` and both sides vanish — a case not formalized
here.  The remaining unformalized input to `CrossTerm` is `htight`, that tightness
`Adj(A) = aI` forces `∑_k ι_{f_k} ω'_k = 0`; that is the vanishing of the off-diagonal
block of `Adj(A)`, obtained by polarizing `⟨v, Θ_k v⟩ = ‖ι_v ω_k‖²` across `e` and
`e^⊥`, and it is carried as a hypothesis.
-/

namespace GramDet

open Matrix

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- **The bordered determinant formula.**  For `G` with invertible determinant,
`det [[a, rᵀ], [c, G]] = a · det G - r ⬝ᵥ (adj G *ᵥ c)`.

In Gram coordinates this is the identity
`⟨u ∧ α, w ∧ γ⟩ = ⟨u,w⟩⟨α,γ⟩ - ⟨ι_w α, ι_u γ⟩` that the cross-term computation runs on. -/
theorem det_border {G : Matrix p p ℝ} (hG : IsUnit G.det) (a : ℝ) (r c : p → ℝ) :
    (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => a) (Matrix.replicateRow Unit r)
        (Matrix.replicateCol Unit c) G).det
      = a * G.det - r ⬝ᵥ (G.adjugate *ᵥ c) := by
  classical
  haveI : Invertible G := G.invertibleOfIsUnitDet hG
  rw [Matrix.det_fromBlocks₂₂]
  have h11 : (((Matrix.of fun _ _ : Unit => a) : Matrix Unit Unit ℝ) -
      Matrix.replicateRow Unit r * (⅟G) * Matrix.replicateCol Unit c).det
      = a - r ⬝ᵥ ((⅟G) *ᵥ c) := by
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm]
  rw [h11, mul_sub]
  congr 1
  · ring
  · have hinv : (⅟G : Matrix p p ℝ) = G⁻¹ := by
      simp [Matrix.invOf_eq_nonsing_inv]
    rw [hinv, AdjugatePSD.adjugate_eq_det_smul_inv hG]
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring

/-- **A Gram determinant vanishes on a dependent family.**  If some nonzero combination
of the columns of `M` is zero then `det (Mᵀ M) = 0`.

This is `f_k ∧ ω'_k = 0`: the border `f_k` lies in the plane of `ω'_k`, so the bordered
family is dependent and its Gram determinant vanishes. -/
theorem det_gram_eq_zero_of_dep {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m p ℝ) {x : p → ℝ} (hx : x ≠ 0) (hMx : M *ᵥ x = 0) :
    (Mᵀ * M).det = 0 := by
  have hker : (Mᵀ * M) *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec, hMx, Matrix.mulVec_zero]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩

/-- **The hypothesis `hsimple`, discharged.**  If the bordered Gram determinant vanishes
--- which is `f ∧ ω' = 0` --- then `‖f‖²‖ω'‖² = ‖ι_f ω'‖²`, in the coordinates
`a = ⟨f,f⟩`, `r_i = ⟨f, b_i⟩`, `G = Gram(b)`. -/
theorem hsimple_of_border_zero {G : Matrix p p ℝ} (hG : IsUnit G.det) (a : ℝ) (r : p → ℝ)
    (hzero : (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => a) (Matrix.replicateRow Unit r)
        (Matrix.replicateCol Unit r) G).det = 0) :
    a * G.det = r ⬝ᵥ (G.adjugate *ᵥ r) := by
  have := det_border hG a r r
  rw [hzero] at this
  linarith

/-- The quantity the cross-term computation calls `‖ι_f ω'‖²` is nonnegative, since the
adjugate of a positive definite Gram matrix is positive definite. -/
theorem contraction_sq_nonneg {G : Matrix p p ℝ} (hG : G.PosDef) (r : p → ℝ) :
    0 ≤ r ⬝ᵥ (G.adjugate *ᵥ r) := by
  classical
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hpd := AdjugatePSD.adjugate_posDef hG
    have hquad : 0 < (Finsupp.equivFunOnFinite.symm r).sum fun i ri =>
        (Finsupp.equivFunOnFinite.symm r).sum fun j rj =>
          star ri * G.adjugate i j * rj := by
      refine hpd.2 ?_
      simpa [Finsupp.ext_iff, funext_iff] using hr
    have hq : r ⬝ᵥ (G.adjugate *ᵥ r) = ∑ i, ∑ j, r i * G.adjugate i j * r j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hq]
    simpa [Finsupp.sum_fintype, Finset.mul_sum, mul_assoc] using hquad.le

end GramDet
