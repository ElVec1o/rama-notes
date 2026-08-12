import Mathlib

/-!
# Why the coefficients are partial transversals, and why the first four are rigid

Two mechanisms behind Propositions `prop:transversal` and `prop:leadrigid` of the note. Neither
proposition is formalised whole, the mixed characteristic polynomial not being in Mathlib; what is
here is the step each one turns on, which in both cases is short and is where an error would hide.

## The multi-affine mechanism

`mu` is built by applying `∏ₖ (1 - ∂_{z_k})` to `det(yI + ∑ₖ z_k A_k)` at `z = 0`. Expanding the
determinant by rank ones attaches to each selection `T` of vectors the monomial `∏ₖ z_k^{t_k}`, with
`t_k` the number of vectors `T` takes from block `k`. So everything depends on what `(1 - ∂_z)`
does to `z^t` at the origin, and `one_sub_deriv_eval_zero` is the answer: `1`, then `-1`, then **zero
from `t = 2` on**. That single vanishing is what forces every surviving selection to take at most one
vector per block, which is what makes the coefficients partial transversals rather than arbitrary
selections. Without it the expansion has no combinatorial content at all.

## The rigidity mechanism

Expanding the Gram determinant at `s ≤ 3` produces only closed walks of length at most three, so `m₂`
and `m₃` involve only `∑ tr(A_k A_l)` and `∑ tr(A_k A_l A_m)`. Both are fixed by `∑ₖ A_k = a·1` and
idempotency, and the two identities are `sum_trace_pairs` and `sum_trace_triples`: the full ordered
sums collapse to `a²·card` and `a³·card` because they are traces of powers of `∑ₖ A_k`.

Passing from the ordered sums to sums over distinct indices needs one fact that is not bookkeeping:
every ordering of a triple of distinct blocks contributes the *same* value. That is
`trace_three_symm`, and it holds because the blocks are symmetric: `tr(ABC) = tr((ABC)ᵀ) = tr(CBA)`,
and `tr(CBA) = tr(ACB)` by cyclicity. Without it the six orderings would carry two different values
and `m₃` would not be determined.

At `s = 4` the Gram determinant carries a four-cycle, whose sum is `tr(A_k A_l A_m A_r)` with four
distinct indices, and the single relation `tr((∑ₖ A_k)⁴) = a⁴·card` cannot pin the three independent
cyclic classes. That is why the cut falls at four, and it is why `m₄` is the first coefficient
carrying a joint invariant; the no-go of `SpectralNoGo` says a proof must read exactly such an
invariant.

## Status

`one_sub_deriv_eval_zero`, `trace_three_symm`, `sum_trace_pairs` and `sum_trace_triples` are
`VERIFIED`. The propositions themselves are `PROVED` in the note and are not formalised whole; the
blocker is that Mathlib carries no mixed characteristic polynomial.
-/

namespace Transversal

open Polynomial Matrix Finset

/-- **The multi-affine mechanism.**  `(1 - ∂)` applied to `z^t` and evaluated at the origin is `1`
for `t = 0`, `-1` for `t = 1`, and zero from `t = 2` on.  The vanishing is what kills every selection
taking two or more vectors from one block, and so is what makes the coefficients of `μ` count partial
transversals. -/
theorem one_sub_deriv_eval_zero (t : ℕ) :
    ((X ^ t : ℝ[X]) - derivative (X ^ t)).eval 0
      = if t = 0 then 1 else if t = 1 then -1 else 0 := by
  match t with
  | 0 => simp
  | 1 => simp
  | (n + 2) => simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Every ordering of a triple contributes the same trace**, for symmetric blocks.  This is what
makes the six orderings of a triple of distinct indices collapse to one value, and without it `m₃`
would not be determined by the hypotheses. -/
theorem trace_three_symm (A B C : Matrix ι ι ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (hC : C.transpose = C) :
    trace (A * B * C) = trace (A * C * B) := by
  have h1 : trace ((A * B * C).transpose) = trace (A * B * C) := trace_transpose _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hA, hB, hC] at h1
  rw [← h1, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]

variable {κ : Type*} [Fintype κ]

/-- The full ordered sum of pairwise traces is a trace of a square, hence `a²` times the dimension.
Subtracting the `q b` diagonal terms leaves `∑_{k<l} tr(A_k A_l)` fixed. -/
theorem sum_trace_pairs (A : κ → Matrix ι ι ℝ) (a : ℝ) (hsum : ∑ k, A k = a • (1 : Matrix ι ι ℝ)) :
    ∑ k, ∑ l, trace (A k * A l) = a ^ 2 * (Fintype.card ι : ℝ) := by
  have h2 : ∀ k, ∑ l, trace (A k * A l) = a * trace (A k) := by
    intro k
    rw [← Matrix.trace_sum, ← Finset.mul_sum, hsum, Matrix.mul_smul, Matrix.mul_one, trace_smul,
      smul_eq_mul]
  simp_rw [h2]
  rw [← Finset.mul_sum, ← Matrix.trace_sum, hsum, trace_smul, smul_eq_mul, Matrix.trace_one]
  ring

/-- The same at order three, which together with `trace_three_symm` fixes `∑_{k<l<m}`. -/
theorem sum_trace_triples (A : κ → Matrix ι ι ℝ) (a : ℝ)
    (hsum : ∑ k, A k = a • (1 : Matrix ι ι ℝ)) :
    ∑ k, ∑ l, ∑ m, trace (A k * A l * A m) = a ^ 3 * (Fintype.card ι : ℝ) := by
  have h3 : ∀ k l, ∑ m, trace (A k * A l * A m) = a * trace (A k * A l) := by
    intro k l
    rw [← Matrix.trace_sum, ← Finset.mul_sum, hsum, Matrix.mul_smul, Matrix.mul_one, trace_smul,
      smul_eq_mul]
  simp_rw [h3, ← Finset.mul_sum]
  rw [sum_trace_pairs A a hsum]
  ring

end Transversal
