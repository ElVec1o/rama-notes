import Mathlib
open Equiv Equiv.Perm Finset
/-!
# Permanent Laplace (cofactor) expansion along column 0

`per M = Σ_i M i 0 · per(M with row i and column 0 deleted)`.  Mathlib has this only for `det`
(`det_succ_column_zero`); here is the sign-free permanent version — the base case of the block
expansion behind the `N₀ = Σ_v per(A_v)·per(B_v)` factorization (which needs the `|S|`-row form).
The `det` proof's sign bookkeeping (`det_permute`, `cycleRange` signs) collapses because the
permanent is invariant under row permutation (`permanent_permute_cols`).
-/

namespace Paper3Laplace

theorem permanent_succ_column_zero {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent = ∑ i : Fin n.succ, A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · -- i = 0 : swap 0 0 = refl, and 0.succAbove = succ
    simp only [Fin.prod_univ_succ, Matrix.permanent, Matrix.submatrix_apply, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply, Fin.succAbove_zero]
  · -- i = Fin.succ i : permute rows by cycleRange to align the swap with succAbove (no sign!)
    rw [← Matrix.permanent_permute_cols (Fin.cycleRange i)]
    simp only [Fin.prod_univ_succ, Matrix.permanent, Matrix.submatrix_apply, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
      Fin.succAbove_cycleRange, id_eq]

/-- **Row companion** of the cofactor expansion: `per M = Σ_j M 0 j · per(M with row 0, col j deleted)`.
The permanent is transpose-invariant, so this follows from `permanent_succ_column_zero` on `Mᵀ`. This
is the other base case needed for the `|S|`-row block expansion behind `N₀ = Σ_v per(A_v)·per(B_v)`
(there one Laplace-expands the block of even rows; expanding along rows is the natural direction). -/
theorem permanent_succ_row_zero {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent = ∑ j : Fin n.succ, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← Matrix.permanent_transpose A, permanent_succ_column_zero A.transpose]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply, ← Matrix.transpose_submatrix, Matrix.permanent_transpose]

end Paper3Laplace
