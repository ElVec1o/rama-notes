import Mathlib

/-!
# The cavity ratio at the threshold is `1 + 1/(1+√a)`

Numerically the ratio `R_e = F_A / F_{A^(e)}` evaluated at `x = 2√a`, in units of the
threshold `x/2 = √a`, is a function of `a` alone: about `1.366` at `a = 3`, `1.333` at
`a = 4`, `1.309` at `a = 5`, independent of the graph and of the dimension.  This file
identifies that constant exactly.

The chain is:

* averaging the vertex identity over directions gives `𝔼_e F_{A^(e)} = F_A'/m`, so the
  direction-averaged ratio is `R̄ = m F_A / F_A'`, which is `1/G(x)` for `G` the Stieltjes
  transform of the empirical root measure of `F_A`;
* for a coordinate family `F_A` is the matching polynomial of the graph;
* for `a`-regular graphs of growing girth the matching measure converges to the
  Kesten–McKay measure of parameter `a`, whose Stieltjes transform is
  `G(z) = 2(a-1) / ((a-2) z + a √(z² - 4(a-1)))`;
* at `z = 2√a` the radical is exactly `2`, and the arithmetic collapses.

Only the last step is formalized here, and it is the only step that is arithmetic: the
first two are proved in the paper and the third is a cited theorem.  What comes out is

  `(1/G(2√a)) / √a = (√a + 2)/(√a + 1) = 1 + 1/(1 + √a)`,

so the cavity ratio exceeds its threshold by exactly `1/(1+√a)` — always positive, and
tending to `0` as `a → ∞`.  That the excess vanishes is the analytic shadow of the
bound `2√a` being asymptotically attained.

`CavityThreshold.no_slack_propagates` says none of this excess can be fed back into the
induction: the fixed point at the threshold is rigid.
-/

namespace KestenMcKay

/-- The Stieltjes transform of the Kesten–McKay measure of parameter `a`, in the form
`G(z) = 2(a-1) / ((a-2) z + a √(z² - 4(a-1)))`. -/
noncomputable def G (a z : ℝ) : ℝ :=
  2 * (a - 1) / ((a - 2) * z + a * Real.sqrt (z ^ 2 - 4 * (a - 1)))

/-- **The radical degenerates at the threshold.**  At `z = 2√a` the quantity
`z² - 4(a-1)` is exactly `4`, so its square root is `2`. -/
theorem radical_at_edge {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt ((2 * Real.sqrt a) ^ 2 - 4 * (a - 1)) = 2 := by
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h4 : (2 * Real.sqrt a) ^ 2 - 4 * (a - 1) = 4 := by nlinarith [hsq]
  rw [h4]
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- The Stieltjes transform at the threshold, in closed form. -/
theorem G_at_edge {a : ℝ} (ha : 0 ≤ a) :
    G a (2 * Real.sqrt a) = (a - 1) / ((a - 2) * Real.sqrt a + a) := by
  unfold G
  rw [radical_at_edge ha]
  rw [show (a - 2) * (2 * Real.sqrt a) + a * 2 = 2 * ((a - 2) * Real.sqrt a + a) by ring]
  rw [show 2 * (a - 1) = 2 * (a - 1) from rfl]
  rcases eq_or_ne ((a - 2) * Real.sqrt a + a) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- **The constant.**  In units of the threshold `√a`, the reciprocal of the Stieltjes
transform at the threshold is `(√a + 2)/(√a + 1)`, that is `1 + 1/(1 + √a)`. -/
theorem inv_G_div_edge {a : ℝ} (ha : 1 < a) :
    ((a - 2) * Real.sqrt a + a) / ((a - 1) * Real.sqrt a)
      = 1 + 1 / (1 + Real.sqrt a) := by
  set s := Real.sqrt a with hsdef
  have hs : s ^ 2 = a := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg a
  have hs1 : 1 < s := by nlinarith
  have hne1 : (1 : ℝ) + s ≠ 0 := by linarith
  have hne2 : (a - 1) * s ≠ 0 := by
    have h1 : (0:ℝ) < a - 1 := by linarith
    have h2 : (0:ℝ) < s := by linarith
    positivity
  have hrhs : 1 + 1 / (1 + s) = (2 + s) / (1 + s) := by field_simp; ring
  rw [hrhs, div_eq_div_iff hne2 hne1, ← hs]
  ring

/-- **The excess is exactly `1/(1+√a)`**: the cavity ratio sits that much above the
threshold the induction can propagate. -/
theorem excess_eq {a : ℝ} (ha : 1 < a) :
    ((a - 2) * Real.sqrt a + a) / ((a - 1) * Real.sqrt a) - 1
      = 1 / (1 + Real.sqrt a) := by
  rw [inv_G_div_edge ha]; ring

/-- The excess is positive for every `a > 1`. -/
theorem excess_pos {a : ℝ} (ha : 1 < a) :
    1 < ((a - 2) * Real.sqrt a + a) / ((a - 1) * Real.sqrt a) := by
  have h := excess_eq ha
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  have : 0 < 1 / (1 + Real.sqrt a) := by positivity
  linarith

/-- The excess is decreasing to `0`: it is below `ε` as soon as `√a > 1/ε`.  This is the
analytic shadow of the bound `2√a` being asymptotically attained. -/
theorem excess_lt {a ε : ℝ} (ha : 1 < a) (hε : 0 < ε) (h : 1 / ε < Real.sqrt a) :
    ((a - 2) * Real.sqrt a + a) / ((a - 1) * Real.sqrt a) - 1 < ε := by
  rw [excess_eq ha]
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 + Real.sqrt a)]
  have hme : 1 < Real.sqrt a * ε := (div_lt_iff₀ hε).mp h
  nlinarith [hε, hs, hme]

end KestenMcKay
