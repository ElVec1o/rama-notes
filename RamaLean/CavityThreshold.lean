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

/-- **The induction step, strengthened by the deficiency.**

`Tightness.adj_compressed` says the compressed family is not tight but deficient by
`F = ∑_k f_k f_kᵀ`.  Tracking that deficiency turns the hypothesis `R ≥ x/2` into
`R ≥ x/2 + 2d/x`, where `d = a - ⟨e, Adj e⟩ ≥ 0` is the local deficiency, and `d = 0`
recovers `cavity_step` and hence the band.

The point is what it does to the target.  With `g_k = ⟨f̂_k, F f̂_k⟩` the deficiency the
children inherit, the step closes provided

  `X ≤ (2F/x) ∑_k θ_k g_k/(a + g_k)`,

whose right-hand side is **strictly positive** (each `g_k ≥ θ_k > 0`).  So the strengthened
induction does not need `X_e ≤ 0`; it needs `X_e` below an explicit positive quantity.
And the estimate is not lossy: the two sides of the final comparison are *identically*
equal, so nothing is thrown away. -/
theorem cavity_step_deficient {ι : Type*} [Fintype ι] {a x X F R d : ℝ} {θ g R' : ι → ℝ}
    (hx : 0 < x) (ha : 0 < a) (hband : x ^ 2 = 4 * a)
    (hθ : ∀ k, 0 ≤ θ k) (hg : ∀ k, 0 ≤ g k)
    (hsum : ∑ k, θ k = a - d)
    (hR' : ∀ k, x / 2 + 2 * g k / x ≤ R' k)
    (hF : 0 < F)
    (hX : X ≤ (2 * F / x) * ∑ k, θ k * g k / (a + g k))
    (hR : R = x - (∑ k, θ k / R' k) - X / F) :
    x / 2 + 2 * d / x ≤ R := by
  have hxne : x ≠ 0 := hx.ne'
  have hag : ∀ k, 0 < a + g k := fun k => by have := hg k; linarith
  -- each child ratio is at least `2(a + g k)/x`
  have hchild : ∀ k, 2 * (a + g k) / x ≤ R' k := by
    intro k
    refine le_trans (le_of_eq ?_) (hR' k)
    field_simp
    linarith [hband]
  have hcpos : ∀ k, 0 < R' k := fun k =>
    lt_of_lt_of_le (div_pos (by linarith [hag k]) hx) (hchild k)
  have hterm : ∀ k, θ k / R' k ≤ θ k * x / (2 * (a + g k)) := by
    intro k
    have h3 : θ k * x * (2 * (a + g k) / x) ≤ θ k * x * R' k :=
      mul_le_mul_of_nonneg_left (hchild k) (mul_nonneg (hθ k) hx.le)
    have h4 : θ k * x * (2 * (a + g k) / x) = θ k * (2 * (a + g k)) := by
      field_simp
    rw [div_le_iff₀ (hcpos k), div_mul_eq_mul_div,
      le_div_iff₀ (by linarith [hag k] : (0:ℝ) < 2 * (a + g k))]
    linarith [h3, h4]
  have hsum' : (∑ k, θ k / R' k) ≤ ∑ k, θ k * x / (2 * (a + g k)) :=
    Finset.sum_le_sum fun k _ => hterm k
  have hXF : X / F ≤ (2 / x) * ∑ k, θ k * g k / (a + g k) := by
    rw [div_le_iff₀ hF]
    calc X ≤ (2 * F / x) * ∑ k, θ k * g k / (a + g k) := hX
      _ = (2 / x) * (∑ k, θ k * g k / (a + g k)) * F := by ring
  -- the two contributions add to exactly `(2/x) ∑ θ k`: nothing is thrown away
  have hexact : ∀ k, θ k * x / (2 * (a + g k)) + 2 / x * (θ k * g k / (a + g k))
      = 2 * θ k / x := by
    intro k
    have hne : (a + g k) ≠ 0 := (hag k).ne'
    have hden : (2:ℝ) * x * (a + g k) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hxne) hne
    have expand : θ k * x / (2 * (a + g k)) + 2 / x * (θ k * g k / (a + g k))
        = (θ k * x ^ 2 + 4 * (θ k * g k)) / (2 * x * (a + g k)) := by
      field_simp
      ring
    rw [expand, div_eq_div_iff hden hxne]
    linear_combination (θ k * x) * hband
  have hcombine : (∑ k, θ k * x / (2 * (a + g k)))
      + (2 / x) * ∑ k, θ k * g k / (a + g k) = ∑ k, 2 * θ k / x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hexact k
  have hx2a : x - 2 * a / x = x / 2 := by
    field_simp
    linarith [hband]
  have hsimp : (∑ k, 2 * θ k / x) = 2 * (a - d) / x := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  rw [hsimp] at hcombine
  have hsplit : 2 * (a - d) / x = 2 * a / x - 2 * d / x := by ring
  rw [hR]
  linarith [hsum', hXF, hcombine, hx2a, hsplit]

/-! ### An upper bound on the remainder

Applying the vertex identity a second time expresses each child polynomial as
`F''_k = (F' - q_k)/x` with `q_k = ⟨f̂_k, W^(e) f̂_k⟩`, so that

  `∑_k θ_k F''_k = (a F' - ∑_k θ_k q_k)/x = (a F' - tr(F W^(e)))/x`,

`F = ∑_k θ_k f̂_k f̂_kᵀ` being the deficiency of `Tightness.adj_compressed`, whose trace is
`a`.  Substituting into `X_e = N_e - ∑_k θ_k F''_k` gives the two-level identity

  `x X_e = tr(F W^(e)) - x⟨e, W e⟩ - a F'`.

Because `F` is a nonnegative combination of unit rank-ones, `tr(F W^(e)) ≤ a·λ_max(W^(e))`
with no spectral theory at all — it is just `∑ θ_k q_k ≤ (∑ θ_k) L`.  That yields the
first upper bound on `X_e` in this development, `remainder_upper` below.  Combined with
`cavity_step_deficient`, whose target is strictly positive, it reduces the band to a
spectral bound on the child's vertex matrix.
-/

/-- **The compression sum.**  If each child polynomial is `(F' - q_k)/x`, the weighted sum
collapses to a single trace against the deficiency. -/
theorem compression_sum {ι : Type*} [Fintype ι] {a x Fp : ℝ} {θ q Fpp : ι → ℝ}
    (hx : x ≠ 0) (hsum : ∑ k, θ k = a)
    (hFpp : ∀ k, Fpp k = (Fp - q k) / x) :
    (∑ k, θ k * Fpp k) = (a * Fp - ∑ k, θ k * q k) / x := by
  have : (∑ k, θ k * Fpp k) = ∑ k, (θ k * Fp - θ k * q k) / x := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hFpp k]
    field_simp
  rw [this, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]

/-- **The trace bound, elementarily.**  `tr(F W) ≤ a·L` when `F = ∑ θ_k f̂_k f̂_kᵀ` with
`θ_k ≥ 0` summing to `a` and every Rayleigh quotient `q_k = ⟨f̂_k, W f̂_k⟩` at most `L`.
Because `F` is presented as a nonnegative combination of unit rank-ones, this needs no
spectral theory. -/
theorem trace_le_of_rayleigh {ι : Type*} [Fintype ι] {a L : ℝ} {θ q : ι → ℝ}
    (hθ : ∀ k, 0 ≤ θ k) (hsum : ∑ k, θ k = a) (hq : ∀ k, q k ≤ L) :
    (∑ k, θ k * q k) ≤ a * L := by
  calc (∑ k, θ k * q k) ≤ ∑ k, θ k * L :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hq k) (hθ k)
    _ = a * L := by rw [← Finset.sum_mul, hsum]

/-- **An upper bound on the remainder.**  From the two-level identity
`x X = ∑_k θ_k q_k - x·We - a·F'` and the trace bound,

  `x X ≤ a L - x·We - a F'`,

`L` any upper bound for the child Rayleigh quotients, in particular `λ_max(W^(e))`.  This
is the first upper bound on `X_e` available: every earlier statement bounded it below or
computed it exactly. -/
theorem remainder_upper {ι : Type*} [Fintype ι] {a x L Fp We X : ℝ} {θ q : ι → ℝ}
    (hθ : ∀ k, 0 ≤ θ k) (hsum : ∑ k, θ k = a) (hq : ∀ k, q k ≤ L)
    (hid : x * X = (∑ k, θ k * q k) - x * We - a * Fp) :
    x * X ≤ a * L - x * We - a * Fp := by
  have := trace_le_of_rayleigh hθ hsum hq
  linarith [hid]

/-! ### The target in ratio form, and why Kesten–McKay satisfies it

`remainder_upper` reduces the band to a spectral bound on the child's vertex matrix,
`λ_max(W^(e)) ≤ x F_A/a - 3 F_{A^(e)}`.  Writing that in terms of the normalized cavity
ratios `r = R_e/(x/2)` and `r' = (max_{e'} R'_{e'})/(x/2)` — using
`λ_max(W^(e)) = F_{A^(e)} - x·min_{e'} F_{A''}` and `min F'' = F_{A^(e)}/max R'` — the
condition becomes `2/r' ≥ 4 - 2r`, that is

  `r' ≤ 1/(2 - r)`.                                                              (★)

`ratio_form` below is that equivalence.  What makes it interesting is that the
Kesten–McKay value of `KestenMcKay.inv_G_div_edge`, `r = r' = 1 + u` with
`u = 1/(1+√a)`, satisfies (★) *automatically*: `(1+u)(1-u) = 1 - u² ≤ 1`.  So the
target is not merely consistent with the Kesten–McKay picture, it is implied by it, with
slack exactly `u²/(1-u) = 1/(√a(1+√a))` — which vanishes like `1/a`, matching the
asymptotic tightness of the bound `2√a`.

This does not prove the band: `r` and `r'` are not known to equal their Kesten–McKay
values (that is `conj:km`, and its analogue one level down).  What it shows is that the
remaining gap is exactly the gap between the true ratios and the Kesten–McKay ones. -/

/-- **The target, in ratio form.**  For `r < 2` and `r' > 0`, the condition
`2/r' ≥ 4 - 2r` is `r' ≤ 1/(2 - r)`. -/
theorem ratio_form {r rp : ℝ} (hrp : 0 < rp) (hr : r < 2) :
    2 / rp ≥ 4 - 2 * r ↔ rp ≤ 1 / (2 - r) := by
  have h2r : 0 < 2 - r := by linarith
  rw [ge_iff_le, le_div_iff₀ hrp, le_div_iff₀ h2r]
  constructor <;> intro h <;> nlinarith [h]

/-- **`1 + u` always satisfies it.**  For `0 ≤ u < 1`, `1 + u ≤ 1/(1 - u)`, because
`(1+u)(1-u) = 1 - u² ≤ 1`. -/
theorem one_add_le_inv_one_sub {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    1 + u ≤ 1 / (1 - u) := by
  have hpos : 0 < 1 - u := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg u]

/-- The slack is exactly `u²/(1-u)`. -/
theorem inv_one_sub_sub_one_add {u : ℝ} (h1 : u < 1) :
    1 / (1 - u) - (1 + u) = u ^ 2 / (1 - u) := by
  have hne : (1 : ℝ) - u ≠ 0 := by intro h; linarith [h]
  field_simp
  ring

/-- The slack, computed. -/
theorem km_slack_calc {s : ℝ} (hs : 0 < s) :
    (1 / (1 + s)) ^ 2 / (1 - 1 / (1 + s)) = 1 / (s * (1 + s)) := by
  have h1 : (1:ℝ) + s ≠ 0 := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs
  have h2 : (1:ℝ) - 1 / (1 + s) = s / (1 + s) := by
    field_simp
    ring
  rw [h2, div_div_eq_mul_div, div_pow, one_pow]
  field_simp

/-- **The Kesten–McKay value satisfies the target, with explicit slack.**  With
`u = 1/(1+√a)`, taking `r = r' = 1 + u` gives `r' ≤ 1/(2 - r)`, and the slack is
`1/(√a(1+√a))`, which tends to `0` like `1/a`. -/
theorem km_satisfies_target {a : ℝ} (ha : 0 < a) :
    (1 + 1 / (1 + Real.sqrt a)) ≤ 1 / (2 - (1 + 1 / (1 + Real.sqrt a)))
    ∧ 1 / (2 - (1 + 1 / (1 + Real.sqrt a))) - (1 + 1 / (1 + Real.sqrt a))
        = 1 / (Real.sqrt a * (1 + Real.sqrt a)) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set u : ℝ := 1 / (1 + Real.sqrt a) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one (by linarith)]
    linarith
  have hrw : 2 - (1 + u) = 1 - u := by ring
  refine ⟨?_, ?_⟩
  · rw [hrw]; exact one_add_le_inv_one_sub hu0.le hu1
  · rw [hrw, inv_one_sub_sub_one_add hu1, hu]
    exact km_slack_calc hs

end CavityThreshold
