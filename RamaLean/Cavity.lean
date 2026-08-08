import Mathlib

/-!
# The cavity contract

`code/universal_cover.py` and `code/covercheck` compute `spec(T)` and the gap label by
iterating the non-backtracking cavity equations of the universal cover,

  `h_{u→v}(z) = (z - ∑_{w ∼ u, w ≠ v} h_{w→u}(z))⁻¹`,
  `G_vv(z)    = (z - ∑_{u ∼ v} h_{u→v}(z))⁻¹`,

at `z = E + iη` with `η > 0`, and reading the density of states off `-Im G_vv / π`.

Those programs are evidence, not proof, and their validity rests on one structural fact
that has nothing to do with floating point: **the cavity map preserves the lower half
plane.**  If every incoming message has non-positive imaginary part and `Im z > 0`, then
`z - ∑ h` sits strictly in the upper half plane, so it is nonzero, the reciprocal is
defined, and its imaginary part is strictly negative.  Hence the iteration never divides by
zero, never leaves the region, and the density it reports is never negative.

This file is the contract (I4): the finitely many statements through which the numerical
work is consumed, stated and proved before anything is built on them.  It says nothing
about convergence, which is where the real analytic content of the cavity method lies and
which is not claimed here.

* `inv_im_neg` — inverting a point of the open upper half plane lands strictly below the
  real axis.
* `sum_im_nonpos` — a finite sum of messages stays in the closed lower half plane.
* `cavity_step` — one application of the map, from closed lower half plane messages to a
  strictly lower half plane output.  This is the invariance.
* `cavity_denom_ne_zero` — the denominator is never zero, so the iteration is total.
* `density_nonneg` — the reported density is non-negative, which is the sanity check the
  programs' validity gate enforces numerically.
-/

namespace Cavity

open Finset

/-- Inverting a point strictly above the real axis lands strictly below it. -/
theorem inv_im_neg {w : ℂ} (hw : 0 < w.im) : (w⁻¹).im < 0 := by
  have hne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hns : 0 < Complex.normSq w := Complex.normSq_pos.mpr hne
  rw [Complex.inv_im]
  exact div_neg_of_neg_of_pos (by linarith) hns

/-- A finite sum of messages in the closed lower half plane stays there. -/
theorem sum_im_nonpos {ι : Type*} (s : Finset ι) (h : ι → ℂ)
    (hh : ∀ i ∈ s, (h i).im ≤ 0) : (∑ i ∈ s, h i).im ≤ 0 := by
  classical
  rw [Complex.im_sum]
  exact Finset.sum_nonpos fun i hi => hh i hi

/-- **The denominator is never zero.**  With `Im z > 0` and all messages in the closed
lower half plane, `z - ∑ h` lies strictly in the open upper half plane, so the cavity map
is total: the iteration cannot divide by zero. -/
theorem cavity_denom_ne_zero {ι : Type*} (s : Finset ι) (h : ι → ℂ) {z : ℂ}
    (hz : 0 < z.im) (hh : ∀ i ∈ s, (h i).im ≤ 0) : z - ∑ i ∈ s, h i ≠ 0 := by
  intro hzero
  have him : 0 < (z - ∑ i ∈ s, h i).im := by
    rw [Complex.sub_im]
    have := sum_im_nonpos s h hh
    linarith
  rw [hzero] at him
  simp at him

/-- **The invariance.**  One step of the cavity map sends messages in the closed lower half
plane to a message strictly in the open lower half plane, whenever `Im z > 0`.  This is
what makes the iteration in `code/universal_cover.py` and `code/covercheck` well posed, and
it holds for every graph and every `η > 0`. -/
theorem cavity_step {ι : Type*} (s : Finset ι) (h : ι → ℂ) {z : ℂ}
    (hz : 0 < z.im) (hh : ∀ i ∈ s, (h i).im ≤ 0) :
    ((z - ∑ i ∈ s, h i)⁻¹).im < 0 := by
  refine inv_im_neg ?_
  rw [Complex.sub_im]
  have := sum_im_nonpos s h hh
  linarith

/-- The invariance in the form the iteration uses it: the region
`{w : Im w ≤ 0}` is preserved. -/
theorem cavity_maps_into {ι : Type*} (s : Finset ι) (h : ι → ℂ) {z : ℂ}
    (hz : 0 < z.im) (hh : ∀ i ∈ s, (h i).im ≤ 0) :
    ((z - ∑ i ∈ s, h i)⁻¹).im ≤ 0 :=
  le_of_lt (cavity_step s h hz hh)

/-- **The reported density is non-negative.**  `-Im G / π` with `G` the resolvent produced
by the cavity map is a density, not a signed quantity.  The programs' validity gate checks
numerically that it also integrates to one; that it never goes negative is structural. -/
theorem density_nonneg {ι : Type*} (s : Finset ι) (h : ι → ℂ) {z : ℂ}
    (hz : 0 < z.im) (hh : ∀ i ∈ s, (h i).im ≤ 0) :
    0 ≤ -((z - ∑ i ∈ s, h i)⁻¹).im / Real.pi := by
  have hstep := cavity_step s h hz hh
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnum : 0 < -((z - ∑ i ∈ s, h i)⁻¹).im := by linarith
  exact le_of_lt (div_pos hnum hpi)

end Cavity
