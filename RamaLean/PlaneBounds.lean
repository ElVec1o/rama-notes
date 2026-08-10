import Mathlib
import RamaLean.MomentLadder

/-!
# The two unconditional bounds for the plane class

Everything the plane-class section establishes without hypotheses comes from two inequalities on
the first two coefficients, and until now those were carried in the paper as arithmetic in prose.
They are the section's only unconditional results, so they are the ones most worth having a
kernel check.

Writing `F_A = x^m - M_1x^{m-2} + M_2x^{m-4} - ⋯` and `y = x²`, the `M_r` are the elementary
symmetric functions of the `y`-roots and the power sums are `p_1 = M_1`, `p_2 = M_1² - 2M_2`.
Real-rootedness gives `y_max ≤ p_1` and `y_max² ≤ p_2`, which are `k = 1` and `k = 2` of
`MomentLadder.max_pow_le_sum`. Feeding in what the class supplies,

  `p_1 = ½ tr Adj(A) ≤ am/2`  and  `p_2 ≤ tr Adj(A)² - ∑_k c_k² ≤ a²m - S`,   `S = ∑_k c_k²`,

turns each into a bound on the dimension for which the band `y ≤ 4a` holds:

* `band_of_dim_le_eight` — `m ≤ 8`;
* `band_of_two_moment` — `m ≤ 16 + S/a²`.

`projection_range` then does the specialisation the paper quotes: on a projection family the
weights are one, so `S = q = am/2`, and the second condition collapses to `m ≤ 32a/(2a-1)`.
That is the bound which reproduces the known two-moment bound for projections and extends it to
all weighted plane families.

## Why the list stops at two

Not for want of rungs. The reach of the `k`-th rung grows without bound
(`MomentLadder.reach_unbounded`), so a third and fourth would cover far more dimension. What is
missing is an a priori bound on `p_k` for the class, and `MomentLadder.band_of_all_moments` shows
that any such bound holding at every rung with a constant free of `k` already gives the band it
would prove. The two bounds below are therefore not a first instalment; they are what the method
yields, and the dimension restriction on them is intrinsic.

## Status

`band_of_dim_le_eight`, `band_of_two_moment`, `projection_range` and `projection_bound` are
`VERIFIED`. The inequalities `p_1 ≤ am/2` and `p_2 ≤ a²m - S` are inputs here, proved in the
paper from `Adj(A) ⪯ aI` and the Grassmann form of the coefficients; what is checked is that they
give the stated dimension ranges.
-/

namespace PlaneBounds

/-- **The first bound.**  The largest `y`-root is at most the first power sum, which the class
bounds by `am/2`; so the band `y ≤ 4a` holds as soon as `m ≤ 8`. -/
theorem band_of_dim_le_eight {m a y : ℝ} (ha : 0 < a) (hp1 : y ≤ a * m / 2) (hm : m ≤ 8) :
    y ≤ 4 * a := by
  nlinarith [hp1, hm, ha]

/-- **The second bound.**  The square of the largest `y`-root is at most the second power sum,
which the class bounds by `a²m - S` with `S = ∑_k c_k²`; so the band holds as soon as
`m ≤ 16 + S/a²`.  The hypothesis `0 ≤ y` is what lets the squared bound be un-squared. -/
theorem band_of_two_moment {m a S y : ℝ} (ha : 0 < a) (hy : 0 ≤ y)
    (hp2 : y ^ 2 ≤ a ^ 2 * m - S) (hm : m ≤ 16 + S / a ^ 2) :
    y ≤ 4 * a := by
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hstep : (m - 16) * a ^ 2 ≤ S := (le_div_iff₀ ha2).mp (by linarith)
  have hsq : y ^ 2 ≤ (4 * a) ^ 2 := by nlinarith [hp2, hstep]
  have h4a : (0 : ℝ) ≤ 4 * a := by linarith
  nlinarith [hsq, hy, h4a]

/-- **The projection specialisation.**  On a projection family every weight is one, so
`S = q = am/2`, and the second condition is exactly `m ≤ 32a/(2a-1)`. -/
theorem projection_range {m a : ℝ} (ha : 1 ≤ a) :
    m ≤ 16 + (a * m / 2) / a ^ 2 ↔ m ≤ 32 * a / (2 * a - 1) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hd : (0 : ℝ) < 2 * a - 1 := by linarith
  have h2a : (0 : ℝ) < 2 * a := by linarith
  have e1 : (16 : ℝ) + (a * m / 2) / a ^ 2 = 16 + m / (2 * a) := by field_simp
  rw [e1, le_div_iff₀ hd]
  constructor
  · intro h
    have h' : (m - 16) * (2 * a) ≤ m := (le_div_iff₀ h2a).mp (by linarith)
    nlinarith [h']
  · intro h
    have h' : (m - 16) * (2 * a) ≤ m := by nlinarith [h]
    have : m - 16 ≤ m / (2 * a) := (le_div_iff₀ h2a).mpr h'
    linarith

/-- The specialisation as it is used: on a projection family, the band holds whenever
`m ≤ 32a/(2a-1)`. -/
theorem projection_bound {m a y : ℝ} (ha : 1 ≤ a) (hy : 0 ≤ y)
    (hp2 : y ^ 2 ≤ a ^ 2 * m - a * m / 2) (hm : m ≤ 32 * a / (2 * a - 1)) :
    y ≤ 4 * a :=
  band_of_two_moment (by linarith) hy hp2 ((projection_range ha).mpr hm)

end PlaneBounds
