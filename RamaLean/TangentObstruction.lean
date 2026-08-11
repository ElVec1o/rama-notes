import Mathlib

/-!
# The second-order obstruction, and why the commuting point is singular

At a commuting tight family of rank-`b` projections, some directions in the kernel of the
linearised constraints are not tangent to the variety. That was first a measurement — the nearest
point of the variety to `A₀ + εD` sits at distance `O(ε)` rather than `O(ε²)`, at two families —
and a measurement cannot tell an obstruction from a solver that stalls, which the solver used
there had already done once. This file is the algebra, and it is two lines of linear algebra once
the right quantity is isolated.

## The reduction to a scalar

Write `A_k = P_k + ε D_k + ε² X_k + O(ε³)`. Idempotency at order two is

  `X_k - P_k X_k - X_k P_k = D_k²`,

and for coordinate projections every matrix here is diagonal at a diagonal entry, so at the vertex
`j` the equation is the scalar `x - p x - x p = g` with `p ∈ {0, 1}` the indicator of `j ∈ e_k`.
That is `(1 - 2p) x = g`, so `x` is **determined**: `x = g` outside the hyperedge and `x = -g`
inside. The off-diagonal blocks of `X_k`, which are the only freedom the equation leaves, never
meet a diagonal entry, so nothing there can help.

Tightness `∑ₖ X_k = 0` then forces `∑ₖ ε_k g_k = 0` with `ε_k = ±1` the sign above. If that sum is
nonzero there is no `X`, hence no curve on the variety with velocity `D`, hence `D` is not in the
tangent cone although it is in the kernel of the linearisation.

## The two configurations

For `D_e = E_vw + E_wv` and `D_f = -(E_vw + E_wv)` one has `D_e² = D_f² = E_vv + E_ww`: the sign
squares away. So at the vertex `v`,

* **same-group** (`w ∈ e ∩ f`, `v ∉ e ∪ f`): both signs are `+1` and the sum is `2 ≠ 0`;
* **cross** (`v ∈ e \ f`, `w ∈ f \ e`): the signs are `-1` and `+1` and the sum is `0`.

That difference of sign is the entire difference between a direction that is tangent and one that
is not. `obstruction_two_blocks` below is the same-group case with the numbers in it.

## Status

`forced_of_notMem`, `forced_of_mem`, `sum_forced`, `no_second_order` and
`obstruction_two_blocks` are `VERIFIED`. That the configuration exists in a given family, and that
the cross directions span the kernel, are checked in `code/singular.py` and `code/curvature.py`
respectively and are not proved here.
-/

namespace TangentObstruction

open Finset

/-- Outside the hyperedge the indicator is `0` and the order-two equation reads `x = g`. -/
theorem forced_of_notMem (x g : ℝ) (h : x - 0 * x - x * 0 = g) : x = g := by
  simpa using h

/-- Inside the hyperedge the indicator is `1` and the equation reads `-x = g`.  Either way `x` is
determined, which is the point: the second-order correction has no freedom on the diagonal. -/
theorem forced_of_mem (x g : ℝ) (h : x - 1 * x - x * 1 = g) : x = -g := by
  have : -x = g := by linarith [h]
  linarith

/-- The sign attached to a vertex by a hyperedge: `+1` outside it, `-1` inside. -/
noncomputable def sgn (p : ℝ) : ℝ := if p = 0 then 1 else -1

/-- **The diagonal entry is determined.**  With `p` the indicator of membership, `x = sgn p * g`. -/
theorem forced (p x g : ℝ) (hp : p = 0 ∨ p = 1) (h : x - p * x - x * p = g) :
    x = sgn p * g := by
  rcases hp with rfl | rfl
  · simp [sgn, forced_of_notMem x g h]
  · simp only [sgn, if_neg (one_ne_zero)]
    simpa using forced_of_mem x g h

/-- **Tightness is then a condition on the data alone.**  If a second-order correction exists,
the signed sum of the `D_k²` diagonal entries must vanish — a statement with no unknown in it. -/
theorem sum_forced {ι : Type*} [Fintype ι] (p x g : ι → ℝ)
    (hp : ∀ k, p k = 0 ∨ p k = 1)
    (heq : ∀ k, x k - p k * x k - x k * p k = g k)
    (hsum : ∑ k, x k = 0) :
    ∑ k, sgn (p k) * g k = 0 := by
  rw [← hsum]
  exact (Finset.sum_congr rfl fun k _ => (forced (p k) (x k) (g k) (hp k) (heq k)).symm)

/-- **The obstruction.**  A nonzero signed sum rules out every second-order correction, so no
curve on the variety has that velocity.  The direction lies in the kernel of the linearisation and
outside the tangent cone, which is what makes the point singular. -/
theorem no_second_order {ι : Type*} [Fintype ι] (p g : ι → ℝ)
    (hp : ∀ k, p k = 0 ∨ p k = 1) (hne : ∑ k, sgn (p k) * g k ≠ 0) :
    ¬ ∃ x : ι → ℝ, (∀ k, x k - p k * x k - x k * p k = g k) ∧ ∑ k, x k = 0 := by
  rintro ⟨x, heq, hsum⟩
  exact hne (sum_forced p x g hp heq hsum)

/-- **The same-group configuration, with its numbers.**  Two blocks, both missing the vertex `v`,
each contributing `(D²)_vv = 1`; every other block contributes nothing.  The signed sum is `2`, so
there is no second-order correction.  For the cross configuration one of the two signs flips and
the sum is `0`, which is why those directions are tangent. -/
theorem obstruction_two_blocks (p g : Fin 2 → ℝ)
    (hp : ∀ k, p k = 0) (hg : ∀ k, g k = 1) :
    ¬ ∃ x : Fin 2 → ℝ, (∀ k, x k - p k * x k - x k * p k = g k) ∧ ∑ k, x k = 0 := by
  refine no_second_order p g (fun k => Or.inl (hp k)) ?_
  simp [sgn, hp, hg]

end TangentObstruction
