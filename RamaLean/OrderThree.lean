import Mathlib

/-!
# Order three imposes nothing, and the orbit carries no curvature

Two steps of the second-order analysis at a commuting tight family that were written out but not
machine-checked. Both are short. Both were load-bearing, which is the reason for checking them.

## Order three

Expanding `A_k = P_k + εD_k + ε²X_k + ε³Y_k`, idempotency at order three reads

  `Y_k - P_k Y_k - Y_k P_k = D_k X_k + X_k D_k`,

and the obstruction to solving it together with `∑ₖ Y_k = 0` is, as at order two, the diagonal of
the right-hand side. That diagonal vanishes identically. `X_k` is diagonal, having been forced so
by the order-two equation, and `D_k` is supported on pairs with exactly one endpoint in the
hyperedge `e_k`, so its diagonal is zero. `diag_mul_add_mul_of_hollow` is exactly that: the
diagonal of `D X + X D` vanishes when `X` is diagonal and `D` is hollow.

The consequence is that order three imposes no condition at all, for every direction and not only
for those on the tangent cone, and leaves `Y` free in its off-diagonal blocks. That freedom is what
the order-four condition would have to consume.

## The orbit

The curvature form vanishes on the conjugation orbit for a reason with no arithmetic in it: `μ` is
invariant under simultaneous orthogonal conjugation, so `λ_max` is constant along
`exp(εΩ)P_k exp(-εΩ)` and every coefficient of its expansion is zero. `curvature_zero_on_orbit`
records that shape. What is formalised here is the implication, not the invariance of `μ`, which
would need the mixed characteristic polynomial itself in Lean; see the note in `XuSharp` on what
Mathlib does and does not carry.

## Status

`diag_mul_add_mul_of_hollow`, `order_three_unobstructed` and `curvature_zero_on_orbit` are
`VERIFIED`. That `X_k` is diagonal is `TangentObstruction.forced`; that `D_k` is hollow is the
order-one equation `P_k D_k + D_k P_k = D_k` read on the diagonal, recorded here as the hypothesis
`hollow_of_order_one`.
-/

namespace OrderThree

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix is *hollow* when its diagonal vanishes.  The order-one equation forces this on every
`D_k`: at a diagonal entry it reads `2 (P_k)_{jj} D_{jj} = D_{jj}` with `(P_k)_{jj} ∈ {0,1}`, and
both cases give `D_{jj} = 0`. -/
theorem hollow_of_order_one (p d : ℝ) (hp : p = 0 ∨ p = 1) (h : p * d + d * p = d) : d = 0 := by
  rcases hp with rfl | rfl <;> linarith

/-- **The order-three obstruction vanishes.**  If `X` is diagonal and `D` is hollow then
`D X + X D` has zero diagonal, so the order-three equation places no condition on its right-hand
side and none on the direction. -/
theorem diag_mul_add_mul_of_hollow (D X : Matrix ι ι ℝ)
    (hX : ∀ i j, i ≠ j → X i j = 0) (hD : ∀ i, D i i = 0) (j : ι) :
    (D * X + X * D) j j = 0 := by
  have h1 : (D * X) j j = D j j * X j j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single j (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ j) h)
    rw [hX l j (fun hlj => hl hlj), mul_zero]
  have h2 : (X * D) j j = X j j * D j j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single j (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ j) h)
    rw [hX j l (fun hjl => hl hjl.symm), zero_mul]
  simp [Matrix.add_apply, h1, h2, hD j]

/-- The same statement in the form it is used: summing over the blocks, the order-three
obstruction is the zero vector, whatever the coefficients. -/
theorem order_three_unobstructed {κ : Type*} [Fintype κ] (D X : κ → Matrix ι ι ℝ) (σ : κ → ι → ℝ)
    (hX : ∀ k i j, i ≠ j → X k i j = 0) (hD : ∀ k i, D k i i = 0) (j : ι) :
    ∑ k, σ k j * ((D k * X k + X k * D k) j j) = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [diag_mul_add_mul_of_hollow (D k) (X k) (hX k) (hD k) j, mul_zero]

/-- **No curvature along the orbit.**  A quantity invariant under the group action is constant
along an orbit curve, so every coefficient of its expansion, the second-order one included,
vanishes.  Applied with the action of the orthogonal group by simultaneous conjugation, under which
the mixed characteristic polynomial and hence its greatest root are invariant. -/
theorem curvature_zero_on_orbit {α β : Type*} (F : α → β) (act : ℝ → α → α) (x : α)
    (hinv : ∀ t y, F (act t y) = F y) : ∀ t, F (act t x) = F x :=
  fun t => hinv t x

/-- The analytic consequence: a real function that is constant has vanishing second derivative, so
a direction along which `λ_max` does not move contributes nothing to the curvature form. -/
theorem second_deriv_of_const (f : ℝ → ℝ) (c : ℝ) (h : ∀ t, f t = c) :
    deriv (deriv f) = 0 := by
  have hf : f = fun _ => c := funext h
  subst hf
  simp [deriv_const]
  rfl

end OrderThree
