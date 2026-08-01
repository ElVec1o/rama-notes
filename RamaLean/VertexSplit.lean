import Mathlib
import RamaLean.AdjugatePSD

/-!
# The vertex splitting, in Gram coordinates

The vertex recursion for a weighted `2`-plane family says that splitting each bivector
along a unit vector `e`, as `ω_k = e ∧ f_k + ω'_k` with `f_k = ι_e ω_k`, gives

  `M_r(A) = M_r(A^(e)) + ∑_{|T|=r} ‖∑_{k∈T} f_k ∧ ω'_{T∖k}‖²`,

so `F_A(x) = x·F_{A^(e)}(x) - N_e(x)` with the cavity term a sum of squares at every
level.  In the classical diagonal case this is the Heilmann–Lieb vertex recursion.

None of that needs exterior algebra.  Writing `C` for the matrix whose columns are the
`2r` factors of `ω_T`, one has `‖ω_T‖² = det (Cᵀ C)`, and splitting off `e` is
`C = e gᵀ + C'` with `g = Cᵀ e` and `C' = (1 - e eᵀ) C`.  Since `eᵀ C' = 0` and
`‖e‖ = 1`,

  `Cᵀ C = C'ᵀ C' + g gᵀ`,

so the whole content of the splitting is the **matrix determinant lemma**

  `det (A + g gᵀ) = det A + gᵀ (adj A) g`,                                     (*)

with `A = C'ᵀ C'` the Gram matrix of the compressed factors; and the nonnegativity of
the cavity term is positivity of the adjugate of a positive semidefinite matrix, which
is `AdjugatePSD.adjugate_posDef`.

Mathlib has the matrix determinant lemma only in the form
`det (A + col u * row v) = det A * det (1 + row v * A⁻¹ * col u)`, and records the
adjugate form (*) as an explicit `TODO` in
`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`.  `det_add_vecMulVec` below supplies
it under the hypothesis `IsUnit A.det`, which is what the application needs since the
Gram matrix of a linearly independent family is positive definite.

Scope: as in `AdjugatePSD`, the singular case is not proved here.  Both sides of (*)
are polynomial in the entries, so it extends by continuity from `A + εI`, but that
limit is not formalized.  `det_le_det_add_vecMulVec` is the inequality the recursion
actually consumes -- `M_r(A) ≥ M_r(A^(e))`, the matching numbers of a plane family
decrease under compression in *every* direction.
-/

namespace VertexSplit

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The bilinear form of a matrix, written out.  Used to move between `⬝ᵥ`/`*ᵥ` and the
double sums that `simp` produces. -/
theorem quad_eq (M : Matrix n n ℝ) (v u : n → ℝ) :
    v ⬝ᵥ (M *ᵥ u) = ∑ i, ∑ j, v i * M i j * u j := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- **The matrix determinant lemma, adjugate form.**  For `A` with invertible
determinant and any vectors `u v`,

  `det (A + u vᵀ) = det A + v ⬝ᵥ (adj A *ᵥ u)`.

This is the statement Mathlib flags as a `TODO` next to
`det_add_replicateCol_mul_replicateRow`. -/
theorem det_add_vecMulVec {A : Matrix n n ℝ} (hA : IsUnit A.det) (u v : n → ℝ) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ (A.adjugate *ᵥ u) := by
  classical
  have hrank := Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hA u v
  rw [← Matrix.vecMulVec_eq Unit] at hrank
  -- the `1 × 1` determinant on the right is `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)`
  have honeone :
      ((1 : Matrix Unit Unit ℝ) + replicateRow Unit v * A⁻¹ * replicateCol Unit u).det
        = 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) := by
    rw [Matrix.det_unique, quad_eq]
    simp [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [hrank, honeone, mul_add, mul_one]
  congr 1
  rw [AdjugatePSD.adjugate_eq_det_smul_inv hA, quad_eq, quad_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by simp; ring

/-- The form the vertex recursion uses: a rank-one *symmetric* update. -/
theorem det_add_vecMulVec_self {A : Matrix n n ℝ} (hA : IsUnit A.det) (g : n → ℝ) :
    (A + vecMulVec g g).det = A.det + g ⬝ᵥ (A.adjugate *ᵥ g) :=
  det_add_vecMulVec hA g g

/-- **The cavity term is nonnegative.**  For a positive definite Gram matrix the
adjugate is again positive definite, so the rank-one update can only increase the
determinant. -/
theorem cavity_nonneg {A : Matrix n n ℝ} (hA : A.PosDef) (g : n →₀ ℝ) :
    0 ≤ g.sum fun i gi => g.sum fun j gj => star gi * A.adjugate i j * gj :=
  AdjugatePSD.adjugate_quadForm_nonneg hA g

/-- **Monotonicity under the rank-one update**, which is `M_r(A) ≥ M_r(A^(e))`:
compressing a weighted `2`-plane family in any direction can only decrease the
matching numbers. -/
theorem det_le_det_add_vecMulVec {A : Matrix n n ℝ} (hA : A.PosDef) (g : n → ℝ) :
    A.det ≤ (A + vecMulVec g g).det := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  rw [det_add_vecMulVec_self hunit g]
  have : 0 ≤ g ⬝ᵥ (A.adjugate *ᵥ g) := by
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · have hpd := AdjugatePSD.adjugate_posDef hA
      have := hpd.1
      -- positive definiteness of the adjugate, read off on the plain vector `g`
      have hquad : 0 < (Finsupp.equivFunOnFinite.symm g).sum fun i gi =>
          (Finsupp.equivFunOnFinite.symm g).sum fun j gj =>
            star gi * A.adjugate i j * gj := by
        refine hpd.2 ?_
        simpa [Finsupp.ext_iff, funext_iff] using hg
      rw [quad_eq]
      simpa [Finsupp.sum_fintype, Finset.mul_sum, mul_assoc] using hquad.le
  linarith

end VertexSplit
