import Mathlib

/-!
# Separating the band geometry from the weight

`ParitySplit` handles the case of one crossing band and turns Conjecture 10 there into a
statement about a weighted mean.  That statement mixes two very different things: where the
crossing band sits relative to `x`, and how much the remaining factors vary.  This file
separates them, and in doing so covers every crossing number rather than just one.

## The split

Let `K` be the set of bands whose range contains `x`, and put

  `π(z) = ∏_{k ∈ K} (x - λ_k(z))`,   `w(z) = |∏_{k ∉ K} (x - λ_k(z))|`.

The factors outside `K` never vanish, so their product has constant sign `s` and
`μ_G(x) = s ∫ π w`.  Writing `π = π₊ - π₋` and bounding `w` by its extremes **in each term
separately**,

  `∫ π w ≥ q_lo ∫ π₊ - q_hi ∫ π₋`,

so with `J₊ = ∫ π₊` and `J₋ = ∫ π₋` the condition

  `q_hi J₋ < q_lo J₊`,   equivalently   `J₊ / J₋ > Λ`,  `Λ = q_hi / q_lo`,

is sufficient for `μ_G(x) ≠ 0`.  That is `ne_zero_of_split`.

## Why this is worth having

`J₊` and `J₋` depend only on the crossing bands and not at all on the weight, and `Λ` depends
only on the weight and not at all on where `x` sits.  The two halves can be attacked
separately, which the weighted-mean form does not allow.

It also applies for every `|K|`.  The earlier reduction needed exactly one crossing band,
which is `92.3%` of the residue; this needs none.

The bound is not the wasteful one.  Applying `sup w` to the whole integrand loses four orders
of magnitude, since `sup w / inf w` reaches `5.4 · 10⁴`; here `inf w` is applied to the
majority term and `sup w` only to the minority term.

## Status

`ne_zero_of_split` is proved.  **The criterion is not always satisfied**, and that is settled
rather than open: over `149764` residue points from `40146` graphs on up to eight vertices it
fires `149511` times and fails `253` times, with worst margin `0.0616`
(`code/jsweep`, in Rust).  A sample of `208` points had shown it firing every time, which was
simply too small.

So the criterion is a sufficient condition covering `99.83%` of the residue, not a proof
strategy for all of it.  Two facts sharpen what is left.  Every failure has exactly one
crossing band: at `κ = 2` the criterion fires at all `9103` points, and no point with `κ ≥ 3`
occurs anywhere in the corpus.  And Conjecture 10 itself is untouched, the true ratio
`min(I₊,I₋)/max(I₊,I₋)` never exceeding `0.0233`, so at the failing points the conclusion
holds comfortably while this particular sufficient condition does not see it.  The worst case
is `n = 8`, `b = 3`, `κ = 1`, `x = 2.0607` on
`[(0,1),(0,2),(0,3),(0,4),(1,4),(2,5),(3,6),(3,7),(5,6),(5,7)]`.
-/

namespace CrossingSplit

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ## The positive and negative parts -/

/-- `π = π₊ - π₋` pointwise. -/
theorem sub_pos_parts (t : ℝ) : t = max t 0 - max (-t) 0 := by
  rcases le_total 0 t with h | h
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]

/-- The integral splits along the positive and negative parts of `π`. -/
theorem integral_split {μ : Measure X} {p w : X → ℝ}
    (h₁ : Integrable (fun z => max (p z) 0 * w z) μ)
    (h₂ : Integrable (fun z => max (-(p z)) 0 * w z) μ) :
    ∫ z, p z * w z ∂μ
      = ∫ z, max (p z) 0 * w z ∂μ - ∫ z, max (-(p z)) 0 * w z ∂μ := by
  rw [← integral_sub h₁ h₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show p z * w z = max (p z) 0 * w z - max (-(p z)) 0 * w z
  rw [← sub_mul, ← sub_pos_parts]

/-! ## The criterion -/

/-- **The split criterion.**  If the weight lies in `[q_lo, q_hi]` with `q_lo > 0`, and the
positive part of `π` beats the negative part by more than the ratio of the extremes of the
weight, then the weighted integral is positive.  No hypothesis on the number of crossing
bands appears. -/
theorem integral_pos_of_split {μ : Measure X} {p w : X → ℝ} {qlo qhi Jp Jm : ℝ}
    (h₁ : Integrable (fun z => max (p z) 0 * w z) μ)
    (h₂ : Integrable (fun z => max (-(p z)) 0 * w z) μ)
    (hJp : Integrable (fun z => max (p z) 0) μ)
    (hJm : Integrable (fun z => max (-(p z)) 0) μ)
    (hwlo : ∀ z, qlo ≤ w z) (hwhi : ∀ z, w z ≤ qhi)
    (hp : Jp = ∫ z, max (p z) 0 ∂μ) (hm : Jm = ∫ z, max (-(p z)) 0 ∂μ)
    (hcrit : qhi * Jm < qlo * Jp) :
    0 < ∫ z, p z * w z ∂μ := by
  have hlow : qlo * Jp ≤ ∫ z, max (p z) 0 * w z ∂μ := by
    rw [hp, ← integral_const_mul]
    refine integral_mono (hJp.const_mul qlo) h₁ fun z => ?_
    rw [mul_comm qlo]
    exact mul_le_mul_of_nonneg_left (hwlo z) (le_max_right _ _)
  have hhigh : ∫ z, max (-(p z)) 0 * w z ∂μ ≤ qhi * Jm := by
    rw [hm, ← integral_const_mul]
    refine integral_mono h₂ (hJm.const_mul qhi) fun z => ?_
    rw [mul_comm qhi]
    exact mul_le_mul_of_nonneg_left (hwhi z) (le_max_right _ _)
  rw [integral_split h₁ h₂]
  linarith

/-- **`μ_G(x) ≠ 0` from the split**, in the form the application uses: the constant sign `s`
of the non-crossing factors is nonzero and multiplies through. -/
theorem ne_zero_of_split {μ : Measure X} {p w : X → ℝ} {qlo qhi Jp Jm s muG : ℝ}
    (hs : s ≠ 0)
    (h₁ : Integrable (fun z => max (p z) 0 * w z) μ)
    (h₂ : Integrable (fun z => max (-(p z)) 0 * w z) μ)
    (hJp : Integrable (fun z => max (p z) 0) μ)
    (hJm : Integrable (fun z => max (-(p z)) 0) μ)
    (hwlo : ∀ z, qlo ≤ w z) (hwhi : ∀ z, w z ≤ qhi)
    (hp : Jp = ∫ z, max (p z) 0 ∂μ) (hm : Jm = ∫ z, max (-(p z)) 0 ∂μ)
    (hcrit : qhi * Jm < qlo * Jp)
    (hmu : muG = s * ∫ z, p z * w z ∂μ) : muG ≠ 0 := by
  rw [hmu]
  exact mul_ne_zero hs
    (ne_of_gt (integral_pos_of_split h₁ h₂ hJp hJm hwlo hwhi hp hm hcrit))

/-- The criterion in ratio form, which is how it is measured: `J₊ / J₋ > Λ`. -/
theorem crit_of_ratio {qlo qhi Jp Jm : ℝ} (hqlo : 0 < qlo) (hJm : 0 < Jm)
    (h : qhi / qlo < Jp / Jm) : qhi * Jm < qlo * Jp := by
  rw [div_lt_div_iff₀ hqlo hJm] at h
  linarith

end CrossingSplit
