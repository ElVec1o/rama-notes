/-
Audit-session formalization: the correct proof that order three imposes nothing.

THE PROBLEM. Paper 2b (note.tex:2070-2078) argues that the order-three obstruction
vanishes "for every direction and not only for those on the cone" because the supports
of `D_k` and `X_k` are complementary: `D_k` lives on pairs split by `e_k`, while
`X_k` has "its two diagonal blocks fixed by order two and the canonical solution taking
the off-diagonal blocks to zero". `RamaLean/OrderThree.lean` encodes exactly that as the
hypothesis `hX : ∀ k i j, ¬(mem k i ↔ mem k j) → X k i j = 0`.

WHY IT FAILS. The split-pair entries of `X_k` are the only FREE ones (there the order-two
coefficient `1 - (P_k)_ii - (P_k)_jj` vanishes), so they are exactly what must absorb the
forced same-side contributions when `∑_k X_k = 0` is imposed. Measured on the Fano family:
for a cone direction, all 21 off-diagonal pairs need a nonzero cross entry, so NO solution
of order two satisfies `hX`. The lemma is true and inapplicable — the failure class
NOTES_FOR_PAL §4 records ("a true theorem with a hypothesis nothing satisfies").

THE REPAIR. The conclusion survives, with a different and better proof. Write the
order-three obstruction at vertex `j` as `R_j = ∑_k σ_k(j) (D_k X_k + X_k D_k)_jj` with
`σ_k(j) = 1 - 2(P_k)_jj`. Then EACH SUMMAND VANISHES, by the order-one equation alone:

  `∑_j (1 - 2(P_k)_jj) (D_k X_k + X_k D_k)_jj = 0`   whenever `P_k D_k + D_k P_k = D_k`,

for an ARBITRARY `X_k` — no support hypothesis, no idempotency, no tightness. In trace
form this is `trace (D X + X D) = 2 * trace (P * (D X + X D))`, proved below by cyclicity.

This is the order-three analogue of the trace law the author already found at order four
(`OrderFour.order_four_sum_zero`, `image_in_trace_zero`), and it explains the rank deficit
observed numerically: the free parameters of `X` reach exactly the sum-zero hyperplane of
the obstruction space (rank 6 of 7 at Fano), and the obstruction always lies in it.
-/
import Mathlib

open Matrix

namespace OrderThreeLaw

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

omit [DecidableEq n] in

/-- **The order-three trace law.**

If `D` satisfies the linearised constraint `P * D + D * P = D`, then for every `X`

  `trace (D * X + X * D) = 2 * trace (P * (D * X + X * D))`,

equivalently `∑_j (1 - 2 P_jj) (D X + X D)_jj = 0` when `P` is a coordinate projection.
So each block contributes nothing to the order-three obstruction, whatever `X` is.

No hypothesis on the support of `X`, and none on `P` beyond the constraint it satisfies
with `D`. This replaces the complementary-supports argument, whose hypothesis no actual
second-order correction satisfies. -/
theorem trace_order_three (P D X : Matrix n n R) (h : P * D + D * P = D) :
    trace (D * X + X * D) = 2 * trace (P * (D * X + X * D)) := by
  have key : trace (P * (D * X + X * D)) = trace (D * X) := by
    have h1 : P * (D * X + X * D) = P * D * X + P * X * D := by
      rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    have h2 : trace (P * X * D) = trace (D * P * X) := by
      rw [Matrix.trace_mul_comm (P * X) D, Matrix.mul_assoc]
    rw [h1, Matrix.trace_add, h2, ← Matrix.trace_add, ← Matrix.add_mul, h]
  rw [Matrix.trace_add, Matrix.trace_mul_comm X D, key]
  ring

end OrderThreeLaw

