import Mathlib

/-!
# Positivity of the adjugate

The kernel recursion for the determinantal representation needs that transversal determinants
decrease under downdates `A ↦ A - vvᵀ/c`. That follows from positivity of the adjugate, since
the derivative of `t ↦ det(A - t·vvᵀ)` is `-vᵀ adj(A - t·vvᵀ) v`.

For a positive definite `A` the statement is immediate from `adj A = det(A) · A⁻¹`: the determinant
is positive and the inverse is again positive definite, so the adjugate is a positive multiple of a
positive definite matrix. The positive semidefinite case follows by applying this to `A + εI` and
letting `ε → 0`, which is not formalized here.
-/

namespace AdjugatePSD

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For an invertible matrix the adjugate is `det A` times the inverse. -/
theorem adjugate_eq_det_smul_inv {A : Matrix n n ℝ} (h : IsUnit A.det) :
    A.adjugate = A.det • A⁻¹ := by
  have hmul : A * A.adjugate = A.det • (1 : Matrix n n ℝ) := Matrix.mul_adjugate A
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A h
  calc A.adjugate = (A⁻¹ * A) * A.adjugate := by rw [hinv, Matrix.one_mul]
    _ = A⁻¹ * (A * A.adjugate) := by rw [Matrix.mul_assoc]
    _ = A⁻¹ * (A.det • (1 : Matrix n n ℝ)) := by rw [hmul]
    _ = A.det • A⁻¹ := by rw [Matrix.mul_smul, Matrix.mul_one]

/-- **The adjugate of a positive definite matrix is positive definite.** -/
theorem adjugate_posDef {A : Matrix n n ℝ} (hA : A.PosDef) : A.adjugate.PosDef := by
  have hdet : 0 < A.det := hA.det_pos
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hdet)
  rw [adjugate_eq_det_smul_inv hunit]
  exact hA.inv.smul hdet

/-- The form in which the downdate argument uses it: the quadratic form of the adjugate is
nonnegative, so moving along `-vvᵀ` can only decrease the determinant. -/
theorem adjugate_quadForm_nonneg {A : Matrix n n ℝ} (hA : A.PosDef) (v : n →₀ ℝ) :
    0 ≤ v.sum fun i vi => v.sum fun j vj => star vi * A.adjugate i j * vj := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact le_of_lt ((adjugate_posDef hA).2 hv)

end AdjugatePSD
