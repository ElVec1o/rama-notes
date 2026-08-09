import Mathlib

/-!
# The weight ratio is band geometry

`CrossingSplit` reduces Conjecture 10 at a residue point to `J₊/J₋ > Λ`, where
`Λ = sup w / inf w` and `w = |∏_{k ∉ K}(x - λ_k)|` runs over the bands that do **not** cross
`x`.  This file removes `w` from the statement.

## The bound

A product is bounded above by the product of the upper bounds of its factors and below by the
product of the lower bounds, so

  `Λ ≤ ∏_{k ∉ K} ( sup_z |x - λ_k(z)| / inf_z |x - λ_k(z)| )`.

For a band that does not cross `x`, the range `B_k = [lo_k, hi_k]` lies entirely on one side,
and each factor is exactly

  `(x - lo_k)/(x - hi_k) = 1 + (hi_k - lo_k)/(x - hi_k) = 1 + width_k / dist(x, B_k)`,

with the mirror formula when the band lies above `x`.  Hence

  `Λ ≤ ∏_{k ∉ K} ( 1 + width_k / dist(x, B_k) )`,

which mentions only the band ranges of the abelian cover.  Combined with `CrossingSplit`, the
criterion becomes a statement purely about band geometry:

  `J₊/J₋ > ∏_{k ∉ K} ( 1 + width_k / dist(x, B_k) )`   implies   `μ_G(x) ≠ 0`.

## What this settles and what it does not

It settles the weight half of the crux as an explicit formula in the band ranges, in the same
currency as `J₊/J₋`, so the two halves can be compared directly instead of one being an opaque
supremum.  It does not bound `Λ` by a constant, and cannot: bands close to `x` give large
factors and there are up to `n - 1` of them.  Measured values of `Λ` reach `5.4 · 10⁴` already
at six vertices.

**The bound is too lossy to close the criterion by itself, and this is measured, not
suspected.**  The only thing discarded is the correlation between bands, since `sup ∏ ≤ ∏ sup`
is an equality only when the extrema align; that costs a median factor `4.73` and up to `28.7`
(`code/jsplit.py`).  Over `208` residue points the criterion with the true `Λ` fires every
time, worst margin `2.149`, while the criterion with this product in place of `Λ` fires `207`
times and **fails once**, at `J₊/J₋ = 1213` against a product of `2298`.

The failing point is the one where `x` sits closest to the edge of the crossing band, minority
measure `0.0171`.  That is not a coincidence: `x` near a band edge makes `J₊/J₋` large, but it
is also where a second band tends to be close to `x`, which makes the product large.  The two
halves grow together, so decoupling them costs exactly where the margin is thinnest.  Closing
the criterion needs either a `Λ` bound that keeps some correlation between bands, or a lower
bound on `J₊/J₋` sharper than the minority measure alone provides.
-/

namespace WeightBound

open Finset

/-! ## Products of bounded factors -/

/-- A product of factors lying in `[lo i, hi i]` lies between the two products.  Positivity of
the lower bounds is what makes the upper half work. -/
theorem prod_mem_Icc {ι : Type*} (s : Finset ι) (f lo hi : ι → ℝ)
    (hlo : ∀ i ∈ s, 0 < lo i) (h1 : ∀ i ∈ s, lo i ≤ f i) (h2 : ∀ i ∈ s, f i ≤ hi i) :
    ∏ i ∈ s, lo i ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ ∏ i ∈ s, hi i := by
  constructor
  · exact Finset.prod_le_prod (fun i hi' => le_of_lt (hlo i hi')) h1
  · exact Finset.prod_le_prod (fun i hi' => le_trans (le_of_lt (hlo i hi')) (h1 i hi')) h2

/-- **The weight ratio is at most the product of the per-band ratios.**  `qhi/qlo ≤ ∏ hi/lo`,
which is the statement that no cancellation between bands is being used. -/
theorem ratio_le_prod {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) :
    (∏ i ∈ s, hi i) / (∏ i ∈ s, lo i) = ∏ i ∈ s, (hi i / lo i) := by
  rw [Finset.prod_div_distrib]

/-! ## The per-band factor -/

/-- For a band lying strictly below `x`, the ratio of the far distance to the near distance is
`1 + width / dist`. -/
theorem factor_below (x lok hik : ℝ) (h : hik < x) :
    (x - lok) / (x - hik) = 1 + (hik - lok) / (x - hik) := by
  have hne : x - hik ≠ 0 := by linarith
  field_simp
  ring

/-- The mirror statement for a band lying strictly above `x`. -/
theorem factor_above (x lok hik : ℝ) (h : x < lok) :
    (hik - x) / (lok - x) = 1 + (hik - lok) / (lok - x) := by
  have hne : lok - x ≠ 0 := by linarith
  field_simp
  ring

/-! ## The criterion in band-geometry form -/

/-- **The criterion with the weight eliminated.**  If `J₊/J₋` exceeds the product of the
per-band ratios, it exceeds `Λ`, and `CrossingSplit` applies.  Everything on the right is a
band width over a distance to `x`. -/
theorem crit_of_band_geometry {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    {qlo qhi Jp Jm : ℝ}
    (hlo : ∀ i ∈ s, 0 < lo i) (hle : ∀ i ∈ s, lo i ≤ hi i)
    (hqlo : ∏ i ∈ s, lo i ≤ qlo) (hqhi : qhi ≤ ∏ i ∈ s, hi i)
    (hgeom : ∏ i ∈ s, (hi i / lo i) < Jp / Jm) :
    qhi / qlo < Jp / Jm := by
  have hprodlo : (0 : ℝ) < ∏ i ∈ s, lo i := Finset.prod_pos hlo
  have hprodhi : (0 : ℝ) < ∏ i ∈ s, hi i :=
    Finset.prod_pos (fun i h => lt_of_lt_of_le (hlo i h) (hle i h))
  have h1 : qhi / qlo ≤ (∏ i ∈ s, hi i) / (∏ i ∈ s, lo i) :=
    div_le_div₀ hprodhi.le hqhi hprodlo hqlo
  rw [ratio_le_prod s lo hi] at h1
  exact lt_of_le_of_lt h1 hgeom

end WeightBound
