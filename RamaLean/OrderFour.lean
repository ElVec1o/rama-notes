import Mathlib

/-!
# Order four is unobstructed, by a trace identity

At a commuting tight family the second-order obstruction is `Q`, order three imposes nothing
(`OrderThree`), and order four reads

  `Z_k - P_k Z_k - Z_k P_k = D_k Y_k + Y_k D_k + X_k²`,

whose diagonal, summed against the signs and over the blocks, must vanish. That condition is
linear in the free order-three correction `Y`, so it is solvable exactly when the `X²` vector lies
in the image of `L_D : Y ↦ (2 ∑ₖ σₖ(j)(D_k Y_k)_{jj})_j`. Measured, that image is the hyperplane
of trace-zero vectors, and the `X²` vector lands in it every time.

It lands there for a reason. Summing the `X²` vector over the vertices gives
`∑ₖ [tr((D_k²)₂₂²) - tr((D_k²)₁₁²)]`, the `X₁₂` contributions cancelling because
`tr(X₂₁X₁₂) = tr(X₁₂X₂₁)`. And `D_k` is off-diagonal for the splitting, so writing it as `M` in the
corner, `(D_k²)₁₁ = M Mᵀ` and `(D_k²)₂₂ = Mᵀ M`, whose squares have equal trace by cyclicity.
So the sum vanishes term by term.

`trace_sq_comm` is that identity, and `order_four_sum_zero` is the consequence: the order-four
obstruction lies in the trace-zero hyperplane whatever the direction.

## What this does and does not settle

It settles that the obstruction lies in the image *provided* the image is the whole trace-zero
hyperplane, that is `rank L_D = n - 1`. That rank is measured (`6` of `7` at Fano, `8` of `9` at
AG(2,3)) and is not proved here. With it, orders two, three and four are all satisfiable on the
cone; the passage from every finite order to an actual curve is a further step again.

## Status

`trace_sq_comm` and `order_four_sum_zero` are `VERIFIED`. That `rank L_D = n - 1` is `HEURISTIC`.
-/

namespace OrderFour

open Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- **The identity behind it.**  `(M Mᵀ)²` and `(Mᵀ M)²` have the same trace, by cyclicity.  This
is what makes the order-four obstruction land in the trace-zero hyperplane. -/
theorem trace_sq_comm (M : Matrix m n R) :
    trace ((M * Mᵀ) * (M * Mᵀ)) = trace ((Mᵀ * M) * (Mᵀ * M)) := by
  have h : (M * Mᵀ) * (M * Mᵀ) = M * (Mᵀ * M * Mᵀ) := by
    simp [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-- The same statement for a general pair, which is all the proof uses: the corner block of a
matrix that is off-diagonal for the splitting gives `M Mᵀ` on one side and `Mᵀ M` on the other. -/
theorem trace_sq_comm' (A : Matrix m n R) (B : Matrix n m R) :
    trace ((A * B) * (A * B)) = trace ((B * A) * (B * A)) := by
  have h : (A * B) * (A * B) = A * (B * A * B) := by simp [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-- **The order-four obstruction has zero total.**  Summing the two corner contributions over the
blocks, each term cancels by `trace_sq_comm`, so the obstruction vector is orthogonal to
`(1, …, 1)` and lies in the trace-zero hyperplane. -/
theorem order_four_sum_zero {κ : Type*} [Fintype κ] (M : κ → Matrix m n R) :
    ∑ k, (trace ((((M k)ᵀ * (M k))) * (((M k)ᵀ * (M k)))) - trace (((M k) * (M k)ᵀ) * ((M k) * (M k)ᵀ))) = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← trace_sq_comm (M k)]
  ring

end OrderFour
