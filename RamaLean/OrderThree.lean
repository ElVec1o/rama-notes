import Mathlib

/-!
# Order three imposes nothing, and the orbit carries no curvature

Two steps of the second-order analysis at a commuting tight family that were written out but not
machine-checked. Both are short. Both were load-bearing, which is the reason for checking them.

## Order three

Expanding `A_k = P_k + εD_k + ε²X_k + ε³Y_k`, idempotency at order three reads

  `Y_k - P_k Y_k - Y_k P_k = D_k X_k + X_k D_k`,

and the obstruction to solving it together with `∑ₖ Y_k = 0` is, as at order two, the diagonal of
the right-hand side. That diagonal vanishes identically, and the reason is a support argument rather than a diagonality
one. `D_k` is supported on pairs with exactly one endpoint in `e_k`, by the order-one equation;
`X_k` is supported on pairs with both endpoints on the same side, the order-two equation having
fixed its two diagonal blocks and the canonical solution taking the off-diagonal blocks to zero.
The two supports are complementary, so every term of `(D X + X D)_{ii}` has a vanishing factor.

`X_k` is NOT diagonal: the order-two equation forces the `b × b` block `X₁₁ = -(D²)₁₁`, which is a
full block. An earlier version of this file assumed diagonality and proved a true theorem whose
hypothesis the actual `X` does not satisfy.

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

`diag_mul_add_mul_of_cross`, `order_three_unobstructed`, `curvature_zero_on_orbit` and
`second_deriv_of_const` are `VERIFIED`. The two support hypotheses are the order-one and order-two
equations respectively, and are hypotheses here rather than claims.
-/

namespace OrderThree

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in the hyperedge splits the index set, and the two matrices occurring at order
three are supported on complementary parts of that splitting.  `D` is *cross-supported*: the
order-one equation `P D + D P = D` says exactly that `D` vanishes whenever both indices lie on the
same side.  `X` is *block-supported*: the order-two equation determines its two diagonal blocks and
the canonical solution takes the off-diagonal blocks to be zero, so `X` vanishes whenever the
indices lie on opposite sides.

An earlier version of this file assumed `X` was diagonal.  That is false: the order-two equation
forces the `b × b` block `X₁₁ = -(D²)₁₁`, which is not a diagonal matrix.  The correct hypothesis
is the one below, and it is what the argument actually uses. -/
theorem diag_mul_add_mul_of_cross (mem : ι → Prop) [DecidablePred mem] (D X : Matrix ι ι ℝ)
    (hD : ∀ i j, (mem i ↔ mem j) → D i j = 0)
    (hX : ∀ i j, ¬(mem i ↔ mem j) → X i j = 0) (i : ι) :
    (D * X + X * D) i i = 0 := by
  have key : ∀ (U V : Matrix ι ι ℝ),
      (∀ p r, (mem p ↔ mem r) → U p r = 0) → (∀ p r, ¬(mem p ↔ mem r) → V p r = 0) →
      (U * V) i i = 0 := by
    intro U V hU hV
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : mem i ↔ mem l
    · rw [hU i l h, zero_mul]
    · rw [hV l i (fun hli => h hli.symm), mul_zero]
  have h1 : (D * X) i i = 0 := key D X hD hX
  have h2 : (X * D) i i = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : mem i ↔ mem l
    · rw [hD l i h.symm, mul_zero]
    · rw [hX i l h, zero_mul]
  simp [Matrix.add_apply, h1, h2]

/-- The same statement summed over the blocks: the order-three obstruction is the zero vector,
whatever the signs, so order three imposes no condition on the direction. -/
theorem order_three_unobstructed {κ : Type*} [Fintype κ] (mem : κ → ι → Prop)
    [∀ k, DecidablePred (mem k)] (D X : κ → Matrix ι ι ℝ) (σ : κ → ι → ℝ)
    (hD : ∀ k i j, (mem k i ↔ mem k j) → D k i j = 0)
    (hX : ∀ k i j, ¬(mem k i ↔ mem k j) → X k i j = 0) (i : ι) :
    ∑ k, σ k i * ((D k * X k + X k * D k) i i) = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [diag_mul_add_mul_of_cross (mem k) (D k) (X k) (hD k) (hX k) i, mul_zero]

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
  simp
  rfl

end OrderThree
