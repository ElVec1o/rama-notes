import Mathlib
import RamaLean.EvenEval

/-!
# A combinatorial meaning for `μ_G(2√(d-1))`

Péter Csikvári asked whether `μ_G(2√(d-1))` has a combinatorial meaning for `d`-regular `G`
of even order.  It does, and the answer is in his own paper with Ferenc Bencs, *Evaluations
of Tutte polynomials of regular graphs* (arXiv:2105.06798).  What was missing was one
substitution, and that is what this file supplies and machine-checks.

## The bridge

Their polynomial is
`R_G(z) = ∑_{M matching} (-z)^{|M|} ∏_{v ∉ V(M)} (z + d_v - 1)`.
For `d`-regular `G` it is a transformation of the matching polynomial.  Comparing
coefficients term by term,

  `R_G(z) = z^{n/2} · μ_G((z + d - 1)/√z)`,

which is `transform` below, written with `s = √z` so that no square roots appear in the
algebra.

## Where the evaluation point comes from

Solving `(s² + d - 1)/s = 2√(d-1)` gives `s² - 2√(d-1)·s + (d-1) = 0`, that is
`(s - √(d-1))² = 0`.  So `x = 2√(d-1)` is not an arbitrary point of the transformation: it
is exactly its **double root**, attained only at `s = √(d-1)`, i.e. `z = d - 1`.  That is
`double_root` and `edge_iff` below, and it is the observation that was missing.

## The consequence

Bencs–Csikvári's Corollary 2.7 expands `R_G` as a weighted pseudo-forest count,
`R_G(w) = ∑_{A pseudo-forest} 2^{c(A)} (w-1)^{n - |A|}`,
where a pseudo-forest is an edge set each of whose components carries at most one cycle and
`c(A)` counts those cycles.  Putting `w = d - 1`:

  **`μ_G(2√(d-1)) = (d-1)^{-n/2} ∑_{A pseudo-forest} 2^{c(A)} (d-2)^{n-|A|}`.**

At `d = 3` the weight `(d-2)^{n-|A|}` is `1` and this reads: `2^{n/2} μ_G(2√2)` is the
number of pseudo-forests of `G` counted with multiplicity `2` per cycle.

Verified by brute force in `code/pseudoforest.py` on `K_4`, `K_{3,3}`, the prism, the cube,
Petersen, the Wagner graph, a cubic graph on six vertices, `K_{4,4}` and `C_8^2`: degrees
`3` and `4`, orders `4` to `10`, exact integer arithmetic, no discrepancy.  The check is
sensitive: feeding it a graph whose degrees are not all `d` makes it fail loudly, which it
did twice on inputs of mine before a regularity assertion was added.

## What is proved here, and what is cited

`transform`, `double_root`, `edge_iff` and `eval_at_edge` are proved.  Corollary 2.7 is
Bencs–Csikvári's and enters `meaning_of` as a hypothesis.  `EvenEval` separately shows the
value is a positive integer, which was the parenthetical in Csikvári's question.
-/

namespace PseudoForest

open Finset

/-! ## The transformation -/

/-- **One term of the transformation.**  With `s = √z`, the substitution
`x = (s² + d - 1)/s` turns `x^{n-2k}` into `z^{-k}` times `(z + d - 1)^{n-2k}`, provided
`2k ≤ n`, so that the exponent bookkeeping in truncated subtraction is honest. -/
theorem transform_term {s D : ℝ} (hs : s ≠ 0) {n k : ℕ} (hk : 2 * k ≤ n) :
    s ^ n * ((s ^ 2 + D) / s) ^ (n - 2 * k)
      = (s ^ 2 + D) ^ (n - 2 * k) * (s ^ 2) ^ k := by
  have hsn : s ^ (n - 2 * k) ≠ 0 := pow_ne_zero _ hs
  have hsplit : s ^ n = s ^ (n - 2 * k) * s ^ (2 * k) := by
    rw [← pow_add]; congr 1; omega
  rw [div_pow, hsplit, pow_mul]
  field_simp

/-- **The transformation, summed.**  For `n` even and `2k ≤ n` throughout the range,

  `s^n · ∑_k c_k ((s² + D)/s)^{n-2k} = ∑_k c_k (s² + D)^{n-2k} (s²)^k`,

which with `D = d - 1`, `s = √z` is `R_G(z) = z^{n/2} μ_G((z+d-1)/√z)`. -/
theorem transform {s D : ℝ} (hs : s ≠ 0) {n K : ℕ} (c : ℕ → ℝ)
    (hK : ∀ k ∈ range (K + 1), 2 * k ≤ n) :
    s ^ n * (∑ k ∈ range (K + 1), c k * ((s ^ 2 + D) / s) ^ (n - 2 * k))
      = ∑ k ∈ range (K + 1), c k * ((s ^ 2 + D) ^ (n - 2 * k) * (s ^ 2) ^ k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h := transform_term (s := s) (D := D) hs (hK k hk)
  calc s ^ n * (c k * ((s ^ 2 + D) / s) ^ (n - 2 * k))
      = c k * (s ^ n * ((s ^ 2 + D) / s) ^ (n - 2 * k)) := by ring
    _ = c k * ((s ^ 2 + D) ^ (n - 2 * k) * (s ^ 2) ^ k) := by rw [h]


/-! ## The evaluation point is the double root -/

/-- **The substitution has a double root at `s = √(d-1)`.**  This is why `2√(d-1)` is the
distinguished point of the transformation rather than an arbitrary one. -/
theorem double_root {D s : ℝ} (hD : 0 ≤ D) :
    s ^ 2 - 2 * Real.sqrt D * s + D = (s - Real.sqrt D) ^ 2 := by
  have h : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  nlinarith [h]

/-- **`x = 2√(d-1)` happens exactly at `s = √(d-1)`,** i.e. at `z = d - 1`. -/
theorem edge_iff {D s : ℝ} (hD : 0 ≤ D) (hs : 0 < s) :
    (s ^ 2 + D) / s = 2 * Real.sqrt D ↔ s = Real.sqrt D := by
  rw [div_eq_iff (ne_of_gt hs)]
  constructor
  · intro h
    have hz : (s - Real.sqrt D) ^ 2 = 0 := by
      rw [← double_root hD]; nlinarith [h]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    linarith
  · intro h
    subst h
    have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
    nlinarith [hsq]

/-- At the double root the transformation's prefactor is `(d-1)^{n/2}`, so the identity
reads `R_G(d-1) = (d-1)^{n/2} μ_G(2√(d-1))`. -/
theorem eval_at_edge {D : ℝ} (hD : 0 < D) {n K : ℕ} (c : ℕ → ℝ)
    (hK : ∀ k ∈ range (K + 1), 2 * k ≤ n) :
    (Real.sqrt D) ^ n * (∑ k ∈ range (K + 1), c k * (2 * Real.sqrt D) ^ (n - 2 * k))
      = ∑ k ∈ range (K + 1), c k * ((2 * D) ^ (n - 2 * k) * D ^ k) := by
  have hs : Real.sqrt D ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hD)
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have hx : (Real.sqrt D ^ 2 + D) / Real.sqrt D = 2 * Real.sqrt D := by
    rw [hsq, div_eq_iff hs]; nlinarith [hsq]
  have h := transform (s := Real.sqrt D) (D := D) hs c hK
  rw [hx] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsq]
  ring_nf

/-! ## The answer -/

/-- **The combinatorial meaning.**

`pf` is the Bencs–Csikvári pseudo-forest sum `∑_A 2^{c(A)} (d-2)^{n-|A|}`, `mu` the value
`μ_G(2√(d-1))`, and `hcor` is their Corollary 2.7 evaluated at `w = d - 1`, namely
`R_G(d-1) = pf`, combined with the transformation identity `R_G(d-1) = (d-1)^{n/2} · mu`.

The conclusion is what Csikvári asked for: the value is the pseudo-forest sum divided by
`(d-1)^{n/2}`.  At `d = 3` the weight collapses and it is the number of pseudo-forests
counted with `2` per cycle, divided by `2^{n/2}`. -/
theorem meaning_of {D mu pf : ℝ} {n : ℕ} (hD : 0 < D)
    (hcor : (Real.sqrt D) ^ n * mu = pf) :
    mu = pf / (Real.sqrt D) ^ n := by
  have hs : (Real.sqrt D) ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.mpr hD))
  field_simp at hcor ⊢
  linarith [hcor]

end PseudoForest
