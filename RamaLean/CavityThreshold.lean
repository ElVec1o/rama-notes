import Mathlib

/-!
# Why the cavity induction stops at `2√a`

For a weighted `2`-plane family `A` on `ℝ^m` with `Adj(A) ⪯ aI`, the vertex recursion
`F_A = x·F_{A^(e)} - N_e` gives, for the ratio `R_e = F_A / F_{A^(e)}`,

  `R_e = x - ∑_k θ_k / R'_k - X_e / F_{A^(e)}`,

where `θ_k = ‖ι_e ω_k‖²`, so `∑_k θ_k = ⟨e, Adj(A) e⟩ ≤ a`, and `X_e` is the cross-term
remainder.  The induction on the dimension propagates the hypothesis `R ≥ x/2` provided
`X_e ≤ 0`, and it does so exactly on `x ≥ 2√a`.

Two facts carry that, and both are formalized here.

`cavity_step` is the single algebraic step: from `R'_k ≥ x/2 > 0`, `θ_k ≥ 0`,
`∑ θ_k ≤ a` and `X ≤ 0` one gets `R ≥ x - 2a/x`, and then `R ≥ x/2` as soon as
`4a ≤ x²`.

`threshold_iff` is the sharpness: `x - 2a/x ≥ x/2` holds *iff* `x ≥ 2√a`.  So the
constant is not an artifact of the estimate.  `double_root_at_threshold` says the same
thing structurally: `x/2` is where the two roots of `ρ² - xρ + a` collide, and at
`x = 2√a` that double root is `√a`, which is `x/2`.  For `x > 2√a` the admissible
thresholds form an interval and the argument has slack; at `x = 2√a` the interval is a
point and it has none.  That is why `2√a`, rather than the conjectured `2√(a-1)`, is
the ceiling of every argument of this shape.

Scope: the vertex recursion itself, and the sign of `X_e`, are not formalized here —
`cavity_step` takes the recursion in the form of the hypothesis `hR` and the sign as
`hX`.  What is proved is that those inputs do close the induction, and that they close
it precisely on `x ≥ 2√a`.
-/

namespace CavityThreshold

open Finset BigOperators

/-- **The threshold is sharp.**  For `x > 0` and `a ≥ 0`, the cavity step
`x - 2a/x ≥ x/2` holds exactly when `x ≥ 2√a`. -/
theorem threshold_iff {a x : ℝ} (hx : 0 < x) (ha : 0 ≤ a) :
    x - 2 * a / x ≥ x / 2 ↔ 2 * Real.sqrt a ≤ x := by
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hdiv : x - 2 * a / x ≥ x / 2 ↔ 4 * a ≤ x ^ 2 := by
    rw [ge_iff_le, ← sub_nonneg]
    have : x - 2 * a / x - x / 2 = (x ^ 2 - 4 * a) / (2 * x) := by
      field_simp; ring
    rw [this, le_div_iff₀ (by positivity), zero_mul, sub_nonneg]
  rw [hdiv]
  constructor
  · intro h
    nlinarith [hsq, hsn, hx, sq_nonneg (x - 2 * Real.sqrt a)]
  · intro h
    nlinarith [hsq, hsn, hx]

/-- At the threshold the quadratic `ρ² - xρ + a` has the double root `√a = x/2`:
the admissible thresholds for the induction degenerate from an interval to a point. -/
theorem double_root_at_threshold {a : ℝ} (ha : 0 ≤ a) (ρ : ℝ) :
    ρ ^ 2 - (2 * Real.sqrt a) * ρ + a = (ρ - Real.sqrt a) ^ 2 := by
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  nlinarith [hsq]

/-- **The induction step.**  If every child ratio is at least `x/2`, the weights are
nonnegative with total at most `a`, the cross-term remainder is nonpositive, and
`4a ≤ x²`, then the parent ratio is again at least `x/2`.

`R` is presented in the form the vertex recursion produces it:
`R = x - ∑ θ_k / R'_k - X / F`. -/
theorem cavity_step {ι : Type*} [Fintype ι] {a x X F R : ℝ} {θ R' : ι → ℝ}
    (hx : 0 < x)
    (hθ : ∀ k, 0 ≤ θ k) (hsum : ∑ k, θ k ≤ a)
    (hR' : ∀ k, x / 2 ≤ R' k)
    (hX : X ≤ 0) (hF : 0 < F)
    (hband : 4 * a ≤ x ^ 2)
    (hR : R = x - (∑ k, θ k / R' k) - X / F) :
    x / 2 ≤ R := by
  have hx2 : (0:ℝ) < x / 2 := by linarith
  -- each term `θ k / R' k` is at most `θ k * (2/x)`
  have h2x : (0:ℝ) ≤ 2 / x := by positivity
  have hterm : ∀ k, θ k / R' k ≤ θ k * (2 / x) := by
    intro k
    have hpos : 0 < R' k := lt_of_lt_of_le hx2 (hR' k)
    rw [div_le_iff₀ hpos]
    have hid : θ k * (2 / x) * (x / 2) = θ k := by field_simp
    calc θ k = θ k * (2 / x) * (x / 2) := hid.symm
      _ ≤ θ k * (2 / x) * R' k :=
          mul_le_mul_of_nonneg_left (hR' k) (mul_nonneg (hθ k) h2x)
  have hsum' : (∑ k, θ k / R' k) ≤ a * (2 / x) := by
    calc (∑ k, θ k / R' k) ≤ ∑ k, θ k * (2 / x) := Finset.sum_le_sum fun k _ => hterm k
      _ = (∑ k, θ k) * (2 / x) := by rw [Finset.sum_mul]
      _ ≤ a * (2 / x) := mul_le_mul_of_nonneg_right hsum h2x
  -- and the remainder only helps
  have hXF : 0 ≤ -(X / F) := by
    have : X / F ≤ 0 := div_nonpos_of_nonpos_of_nonneg hX hF.le
    linarith
  -- `x - 2a/x ≥ x/2` is exactly `4a ≤ x²`
  have hcore : x / 2 ≤ x - a * (2 / x) := by
    rw [← sub_nonneg]
    have hid : x - a * (2 / x) - x / 2 = (x ^ 2 - 4 * a) / (2 * x) := by
      field_simp; ring
    rw [hid]
    exact div_nonneg (by linarith) (by linarith)
  rw [hR]
  linarith

/-- **No slack can be propagated at the threshold.**  Suppose one tried to strengthen the
inductive hypothesis from `R ≥ x/2` to `R ≥ c·(x/2)` for some `c > 0`.  At `x = 2√a` the
recursion sustains that only if `c = 1`.

This matters because the slack is real: numerically `R_e/(x/2)` sits around `1.33`–`1.37`
over `3 ≤ a ≤ 5`, essentially independent of the graph and of the dimension.  The theorem
says the recursion cannot use any of it — the fixed point at the threshold is rigid,
which is `double_root_at_threshold` seen from the other side. -/
theorem no_slack_propagates {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (h : c * Real.sqrt a ≤ 2 * Real.sqrt a - a / (c * Real.sqrt a)) : c = 1 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hden : 0 < c * Real.sqrt a := mul_pos hc hsa
  -- clear the denominator
  have h' : c * Real.sqrt a * (c * Real.sqrt a)
      ≤ (2 * Real.sqrt a) * (c * Real.sqrt a) - a := by
    have := mul_le_mul_of_nonneg_right h hden.le
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hden)] at this
    linarith
  -- which is `a (c-1)² ≤ 0`
  have hkey : a * (c - 1) ^ 2 ≤ 0 := by nlinarith [hsq, hsa]
  have : (c - 1) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (c - 1), hkey, ha]
  have hz : (c - 1) ^ 2 = 0 := le_antisymm this (sq_nonneg _)
  have : c - 1 = 0 := by
    exact pow_eq_zero_iff two_ne_zero |>.mp hz
  linarith

end CavityThreshold
