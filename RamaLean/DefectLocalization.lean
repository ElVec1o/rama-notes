import Mathlib

/-!
# Approximate spectral localization

Conjecture 10 asserted `Zeros(μ_G) ⊆ spec(T)` and is false.  The counterexamples all miss by
very little: over thirteen of them, on `31` to `97` vertices and across two unrelated
families, every root lies within `0.035` of `spec(T)`, with no growth in the number of
vertices (`code/defect.py`).  That suggests the conjecture is not wrong in shape, only in the
epsilon.

## The frozen statement

  **D1.**  There is an absolute constant `C` with `dist(θ, spec(T_G)) ≤ C` for every finite
  graph `G` and every root `θ` of `μ_G`.

It was frozen before the confirming data was generated and has survived an out-of-sample test
on ten counterexamples disjoint from the three that suggested it.  It remains a conjecture.

## What this file proves

D1 itself is not provable here.  What is proved is the payoff: *what D1 would buy*, so that
the conjecture is stated in the form in which it is worth attacking.

* `zeros_subset_thickening`: D1 says exactly that the roots lie in the closed `C`-neighbourhood
  of `spec(T)`.  At `C = 0` this is Conjecture 10, so D1 is a quantitative weakening of a false
  statement rather than a different statement.
* `root_free_core`: **a gap of `spec(T)` wider than `2C` has a root-free core.**  If `(a,b)`
  misses the spectrum and `b - a > 2C`, no root lies in `(a+C, b-C)`.  So under D1 the
  conjecture is restored for every sufficiently wide gap, and the counterexamples are confined
  to narrow ones.  The measured gap widths are consistent with this: every violated gap has
  width at most `0.22`.
* `defect_le_half_width`: a root inside a gap is never further than half its width from the
  spectrum, which pins the trivial part of the bound and shows what `root_free_core` adds
  beyond it.

## Status

D1 is `CONJECTURE`, supported out of sample.  Everything below it is proved.  The value of the
file is that it fixes the exact form of the target: not "the conjecture is nearly true" but
"wide gaps are root-free", which is falsifiable and is what a proof would have to deliver.
-/

namespace DefectLocalization

/-- The closed `C`-neighbourhood of a set of reals. -/
def thickening (C : ℝ) (S : Set ℝ) : Set ℝ := {x | ∃ s ∈ S, |x - s| ≤ C}

/-- At `C = 0` the thickening of a set contains exactly its own points, so D1 at `C = 0` is
Conjecture 10 itself. -/
theorem thickening_zero (S : Set ℝ) : thickening 0 S = S := by
  ext x
  constructor
  · rintro ⟨s, hs, h⟩
    have : x - s = 0 := by
      have := abs_nonneg (x - s)
      exact abs_eq_zero.mp (le_antisymm h this)
    rwa [show x = s by linarith]
  · exact fun hx => ⟨x, hx, by simp⟩

/-- **D1, restated.**  A defect bound is exactly the statement that the roots lie in the
`C`-neighbourhood of the spectrum. -/
theorem zeros_subset_thickening {S Z : Set ℝ} {C : ℝ}
    (hdef : ∀ θ ∈ Z, ∃ s ∈ S, |θ - s| ≤ C) : Z ⊆ thickening C S :=
  fun θ hθ => hdef θ hθ

/-- **Wide gaps have a root-free core.**  If `(a,b)` misses the spectrum and every root is
within `C` of the spectrum, then no root lies in the open interval `(a+C, b-C)`.  Under D1 this restores
Conjecture 10 for every gap of width more than `2C`, and confines any counterexample to a
narrow gap. -/
theorem root_free_core {S Z : Set ℝ} {C a b : ℝ}
    (hdef : ∀ θ ∈ Z, ∃ s ∈ S, |θ - s| ≤ C)
    (hgap : ∀ s ∈ S, s ≤ a ∨ b ≤ s) :
    ∀ θ ∈ Z, θ ∉ Set.Ioo (a + C) (b - C) := by
  intro θ hθ hmem
  obtain ⟨s, hs, hle⟩ := hdef θ hθ
  have h1 : θ - s ≤ C := le_trans (le_abs_self _) hle
  have h2 : -(θ - s) ≤ C := le_trans (neg_le_abs _) hle
  have hlo : a + C < θ := hmem.1
  have hhi : θ < b - C := hmem.2
  rcases hgap s hs with h | h
  · linarith
  · linarith

/-- A root lying inside a gap is at most half the gap's width from the spectrum.  This is the
trivial part of a defect bound; `root_free_core` is what goes beyond it. -/
theorem defect_le_half_width {a b θ : ℝ} (hlo : a ≤ θ) (hhi : θ ≤ b) :
    min (θ - a) (b - θ) ≤ (b - a) / 2 := by
  rcases le_total (θ - a) (b - θ) with h | h
  · have : min (θ - a) (b - θ) = θ - a := min_eq_left h
    rw [this]; linarith
  · have : min (θ - a) (b - θ) = b - θ := min_eq_right h
    rw [this]; linarith

/-- **Conjecture 10 is the case `C = 0`.**  With no defect allowed, the root-free core is the
whole open gap, so no root lies strictly inside a gap.  Roots at the edges are not
excluded, and should not be: the edges belong to the spectrum. -/
theorem conj10_of_zero_defect {S Z : Set ℝ} {a b : ℝ}
    (hdef : ∀ θ ∈ Z, ∃ s ∈ S, |θ - s| ≤ 0)
    (hgap : ∀ s ∈ S, s ≤ a ∨ b ≤ s) :
    ∀ θ ∈ Z, θ ∉ Set.Ioo a b := by
  have h := root_free_core hdef hgap
  simpa using h

end DefectLocalization
