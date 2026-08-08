import Mathlib

/-!
# The crossing band, and a weighted mean

`InertiaSplit` runs through a feedback vertex set `W`, a forest `F = G - W` and the Schur
complement `S`.  That is a computational device, not part of the statement, and it costs
something real: `sup‖S‖` and the Lipschitz constant of the crossing eigenvalue both scale
like `1/μ_F(x)`, while the geometric mean `Δ` scales like `1/μ_F(x)`, so near a root of
`μ_F` inside a gap the estimate loses by a whole factor of `μ_F` and `G44` fails for reasons
that have nothing to do with the conjecture.

Dropping `W` removes that.  Writing `P_x(z) = det(x I - A_G(z)) = ∏_k (x - λ_k(z))` and
`N(z) = #{k : λ_k(z) > x}`, the sign of `P_x` is `(-1)^{N(z)}` and

  `μ_G(x) = ∫ P_x = I_even - I_odd`,

with no feedback vertex hypothesis, no restriction on `b`, and no `μ_F`.  It also makes the
Lipschitz constant exact rather than measured: `∂A/∂θ_j` has one entry of modulus one and its
conjugate, so its operator norm is `1`, and Weyl gives `L = √b` outright.

## The case that actually occurs

Let `κ` be the number of bands whose range contains `x`.  If `κ = 0` the determinant never
vanishes and the localization settles `x`.  Measured over residue points of many graphs,
`κ = 1` in every case: exactly one band crosses, and the minority-parity region has measure at
most `0.067`.

With `κ = 1` the problem collapses.  The factors other than the crossing one never vanish, so
`Q = ∏_{k ≠ k₀}(x - λ_k)` has constant sign `s`, and

  `μ_G(x) = s ∫ (x - λ_{k₀}(z)) |Q(z)| dz`.

So `μ_G(x) = 0` **iff `x` is the `|Q|`-weighted mean of the crossing band function**.  That is
`zero_iff_weighted_mean`.  The competition between two integrals of comparable size becomes a
single scalar question, and `code/kap.py` confirms the identity to `10⁻¹⁵` and puts the
weighted means at `-2.149, -1.483, 1.483, 2.143, 2.150` on gaps whose interiors are near
`±1.77`: far from `x`, and inside `spec(T)`.

## What this buys and what it costs

Gain: `mean_mem_Icc` recovers the localization in this case for free, since a weighted mean
lies in the range of the function averaged, so `x` outside the band range gives `μ_G(x) ≠ 0`
with no estimate at all.  Conjecture 10 at a `κ = 1` point becomes: **the `|Q|`-weighted mean
of the crossing band lies in `spec(T)`.**

Cost, stated plainly (difficulty is conserved): that statement is not proved here.  A weighted
mean lies in the convex hull of the range of `λ_{k₀}`, which is the band `B_{k₀}`, and
`B_{k₀}` is not contained in `spec(T)` precisely because `x` sits in `B_{k₀} \ spec(T)`.  So
the containment is not automatic and the remaining work is real.  What has changed is its
shape: one scalar in one interval, in place of two integrals of comparable size.  Over all
`2206` points with `κ = 1`, the weighted mean lies in `spec(T)` every time and is never closer
than `0.167` to `x` (`code/wmean_test.py`), so the statement survives a deliberate attempt to
break it; a single coincidence there would have refuted the conjecture outright.  The `183`
points with `κ ≥ 2` are not covered by anything here.
-/

namespace ParitySplit

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ## The algebraic split -/

/-- `∫ (x - g) w = x ∫ w - ∫ g w`.  The whole content of the reduction is that the crossing
factor is affine in the band function, so the integral is affine in `x`. -/
theorem integral_affine {μ : Measure X} {g w : X → ℝ} {x : ℝ}
    (hw : Integrable w μ) (hgw : Integrable (fun z => g z * w z) μ) :
    ∫ z, (x - g z) * w z ∂μ = x * (∫ z, w z ∂μ) - ∫ z, g z * w z ∂μ := by
  have h : ∀ z, (x - g z) * w z = x * w z - g z * w z := fun z => by ring
  simp_rw [h]
  rw [integral_sub (hw.const_mul x) hgw, integral_const_mul]

/-- **The vanishing criterion.**  With `w = |Q| ≥ 0` of positive total mass, the average of
`x - λ_{k₀}` against `w` vanishes exactly when `x` is the `w`-weighted mean of `λ_{k₀}`. -/
theorem zero_iff_weighted_mean {μ : Measure X} {g w : X → ℝ} {x : ℝ}
    (hw : Integrable w μ) (hgw : Integrable (fun z => g z * w z) μ)
    (hpos : 0 < ∫ z, w z ∂μ) :
    ∫ z, (x - g z) * w z ∂μ = 0 ↔ x = (∫ z, g z * w z ∂μ) / (∫ z, w z ∂μ) := by
  rw [integral_affine hw hgw, sub_eq_zero, eq_div_iff (ne_of_gt hpos)]

/-- Pulling the constant sign of `Q` out, so the criterion applies to `|Q|`. -/
theorem integral_sign_mul {μ : Measure X} {g w : X → ℝ} {s x : ℝ} :
    ∫ z, (x - g z) * (s * w z) ∂μ = s * ∫ z, (x - g z) * w z ∂μ := by
  have h : ∀ z, (x - g z) * (s * w z) = s * ((x - g z) * w z) := fun z => by ring
  simp_rw [h]
  exact integral_const_mul s _

/-- **`μ_G(x) ≠ 0` iff `x` is not the weighted mean**, in the form the application uses:
`P = (x - g) · (s · w)` with `s = ±1` the constant sign of `Q` and `w = |Q|`. -/
theorem ne_zero_iff_ne_weighted_mean {μ : Measure X} {g w : X → ℝ} {s x muG : ℝ}
    (hs : s ≠ 0) (hw : Integrable w μ) (hgw : Integrable (fun z => g z * w z) μ)
    (hpos : 0 < ∫ z, w z ∂μ)
    (hmu : muG = ∫ z, (x - g z) * (s * w z) ∂μ) :
    muG ≠ 0 ↔ x ≠ (∫ z, g z * w z ∂μ) / (∫ z, w z ∂μ) := by
  rw [hmu, integral_sign_mul, mul_ne_zero_iff]
  simp only [hs, ne_eq, not_false_eq_true, true_and]
  exact not_congr (zero_iff_weighted_mean hw hgw hpos)

/-! ## The weighted mean lies in the range, which recovers the localization -/

/-- A weighted mean lies between the bounds of the function averaged.  Applied to the crossing
band this says the mean is in `B_{k₀}`, so an `x` outside the band range can never be it: that
is the localization in the `κ = 1` case, obtained with no estimate. -/
theorem mean_mem_Icc {μ : Measure X} [IsProbabilityMeasure μ] {g w : X → ℝ} {a c : ℝ}
    (hw : Integrable w μ) (hgw : Integrable (fun z => g z * w z) μ)
    (hwpos : ∀ z, 0 ≤ w z) (hpos : 0 < ∫ z, w z ∂μ)
    (hlo : ∀ z, a ≤ g z) (hhi : ∀ z, g z ≤ c) :
    a ≤ (∫ z, g z * w z ∂μ) / (∫ z, w z ∂μ) ∧
      (∫ z, g z * w z ∂μ) / (∫ z, w z ∂μ) ≤ c := by
  constructor
  · rw [le_div_iff₀ hpos]
    have : ∫ z, a * w z ∂μ ≤ ∫ z, g z * w z ∂μ :=
      integral_mono (hw.const_mul a) hgw
        (fun z => mul_le_mul_of_nonneg_right (hlo z) (hwpos z))
    rwa [integral_const_mul] at this
  · rw [div_le_iff₀ hpos]
    have : ∫ z, g z * w z ∂μ ≤ ∫ z, c * w z ∂μ :=
      integral_mono hgw (hw.const_mul c)
        (fun z => mul_le_mul_of_nonneg_right (hhi z) (hwpos z))
    rwa [integral_const_mul] at this

/-- **Conjecture 10 at a `κ = 1` point, reduced.**  If `x` lies strictly outside the range of
the crossing band then `μ_G(x) ≠ 0`.  This is exactly the localization, recovered here without
the connectedness argument, and it is why the remaining work is confined to `x` inside the
band: there the mean could in principle be `x`, and ruling that out is what is left. -/
theorem ne_zero_of_outside_band {μ : Measure X} [IsProbabilityMeasure μ] {g w : X → ℝ}
    {s x muG a c : ℝ} (hs : s ≠ 0)
    (hw : Integrable w μ) (hgw : Integrable (fun z => g z * w z) μ)
    (hwpos : ∀ z, 0 ≤ w z) (hpos : 0 < ∫ z, w z ∂μ)
    (hlo : ∀ z, a ≤ g z) (hhi : ∀ z, g z ≤ c)
    (hmu : muG = ∫ z, (x - g z) * (s * w z) ∂μ)
    (hout : x < a ∨ c < x) : muG ≠ 0 := by
  rw [ne_zero_iff_ne_weighted_mean hs hw hgw hpos hmu]
  obtain ⟨h1, h2⟩ := mean_mem_Icc hw hgw hwpos hpos hlo hhi
  rcases hout with h | h
  · exact fun heq => absurd (heq ▸ h1) (not_le.mpr h)
  · exact fun heq => absurd (heq ▸ h2) (not_le.mpr h)

end ParitySplit
