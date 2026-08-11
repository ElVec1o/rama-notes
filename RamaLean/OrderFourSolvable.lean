import Mathlib

/-!
# Order four is solvable: the step that joins the two halves

The order-four condition holds exactly when the `X²` vector lies in the image of

  `L_D : Y ↦ (2 ∑ₖ σₖ(j) (D_k Y_k)_jj)_j`.

Two facts about that were already machine-checked and they were checked separately:

* `OrderFour.order_four_sum_zero`: the `X²` vector has vanishing coordinate sum, because the two
  corner blocks `MMᵀ` and `MᵀM` have squares of equal trace;
* `CokernelRank.cokernel_const`: when the separation graph `G_D` is preconnected, every vector
  annihilating the image is constant, so `rank L_D = n - 1` with cokernel the constants.

Neither is the conclusion. The conclusion is that the vector is *in* the image, and the step from
the two to that is the one formalised here: in a finite-dimensional inner product space a subspace
is the orthogonal complement of its own orthogonal complement, so a subspace whose complement is
the line of constants is exactly the hyperplane of vectors summing to zero. Written out it is three
lines, and leaving it out is how a chain of true lemmas fails to prove the thing it was assembled
for. This was the recorded debt on A6b.

The hypothesis is stated as `(range L)ᗮ = span {1}`, which is what `cokernel_const` delivers under
preconnectedness of `G_D`, and preconnectedness is a property of the direction `D` that is checked
rather than assumed. Where `G_D` is empty, the cross-basis directions, the rank collapses to `1` and
the obstruction vanishes outright, so order four is solvable there for a different and easier
reason.

## Status

`inner_one_eq_sum`, `mem_of_sum_zero` and `order_four_solvable` are `VERIFIED`.
-/

namespace OrderFourSolvable

open Finset RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The all-ones vector, which spans the cokernel of `L_D` when `G_D` is preconnected. -/
def ones : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => 1)

/-- Pairing against the constants reads off the coordinate sum. -/
theorem inner_one_eq_sum (v : EuclideanSpace ℝ V) : ⟪(ones : EuclideanSpace ℝ V), v⟫ = ∑ j, v j := by
  simp [ones, PiLp.inner_apply, RCLike.inner_apply]

/-- **A subspace whose orthogonal complement is the constants is the sum-zero hyperplane.**  The
direction that is needed is the one that does not follow from the definition: membership of the
complement of the complement, which is the subspace itself only because the ambient space is
finite-dimensional. -/
theorem mem_of_sum_zero (S : Submodule ℝ (EuclideanSpace ℝ V))
    (hcoker : Sᗮ = Submodule.span ℝ {(ones : EuclideanSpace ℝ V)})
    (v : EuclideanSpace ℝ V) (hv : ∑ j, v j = 0) : v ∈ S := by
  rw [← Submodule.orthogonal_orthogonal S, hcoker, Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
  rw [real_inner_smul_left, inner_one_eq_sum, hv, mul_zero]

/-- **A6b assembled.**  With the cokernel of `L_D` the constants and the obstruction summing to
zero, the order-four equation has a solution.  This is the statement the order-four analysis needed
and the one the two earlier files stopped short of. -/
theorem order_four_solvable {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : W →ₗ[ℝ] EuclideanSpace ℝ V)
    (hcoker : (LinearMap.range L)ᗮ = Submodule.span ℝ {(ones : EuclideanSpace ℝ V)})
    (v : EuclideanSpace ℝ V) (hv : ∑ j, v j = 0) : ∃ y, L y = v :=
  LinearMap.mem_range.1 (mem_of_sum_zero (LinearMap.range L) hcoker v hv)

end OrderFourSolvable
