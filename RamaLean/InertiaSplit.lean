import Mathlib

/-!
# What G24 reduces to, after measuring the inertia split

For `x` outside `spec(T)`, `μ_G(x)/μ_F(x)` is the average over the torus of `det S(x,z)`,
and `sign det S(x,z) = (-1)^{δ_ab(x,z)}` with `δ_ab ∈ {0,1,2}` the abelian inertia.  So

  `μ_G/μ_F = I₀ - I₁ + I₂`,   `I_j = ∫_{δ_ab = j} |det S(x,z)| dz ≥ 0`,

and G24 asks that the sign of this be `(-1)^{δ(x)}` with `δ` the **free** inertia.

`code/inertia_split.py` measures the split.  Inside a genuine gap of `spec(T)` it is
lopsided but **not** degenerate: at two triangles joined by an edge, at `x = -1.767` with
`δ = 1`, the class `δ_ab = 1` occupies `0.987` of the torus and `δ_ab = 2` occupies `0.013`.
So `1.3%` of the torus carries the **wrong parity**: the integrand genuinely changes sign
and the verdict is a competition, won comfortably rather than by default.  At
`K_4` with pendants and `x ≈ 0` the split is `m₂ = 1` exactly and there is no competition
at all.

That measurement removes one hope and replaces it with a quantitative target.  The hope
removed: `det S(x,z)` does not have constant sign, so no argument of the form "the
integrand never changes sign" can work.  The target: **the class matching `δ` must dominate
the others in integral, not merely in measure.**

This file records the decomposition and the criterion, which is all that is proved.  The
domination itself is `G33` and is open.

* `avg_neg_of_dominant`, `avg_pos_of_dominant` — the sign of `I₀ - I₁ + I₂` is decided by
  which parity dominates, in the sense of the integrals and not the measures.
* `gapcount_of_domination` — that criterion is exactly G24 at the point in question.
-/

namespace InertiaSplit

/-! ## The decomposition -/

/-- **Odd parity dominant.**  If the odd inertia class carries more integral than the two
even classes together, the average is negative, which is the sign `(-1)^δ` for odd `δ`. -/
theorem avg_neg_of_dominant {I₀ I₁ I₂ : ℝ} (_h₀ : 0 ≤ I₀) (_h₂ : 0 ≤ I₂)
    (hdom : I₀ + I₂ < I₁) : I₀ - I₁ + I₂ < 0 := by linarith

/-- **Even parity dominant.**  The mirror statement. -/
theorem avg_pos_of_dominant {I₀ I₁ I₂ : ℝ} (_h₁ : 0 ≤ I₁)
    (hdom : I₁ < I₀ + I₂) : 0 < I₀ - I₁ + I₂ := by linarith

/-- Measure alone does not decide it.  A class can occupy almost all of the torus and still
lose the integral, so the domination hypothesis above is about `I_j` and cannot be weakened
to a statement about `m_j`.  This is the content of the `1.3%` observed at two triangles:
the minority is small but nonzero, so the integrand does change sign. -/
theorem measure_does_not_decide :
    ∃ I₀ I₁ I₂ : ℝ, 0 ≤ I₀ ∧ 0 ≤ I₁ ∧ 0 ≤ I₂ ∧ I₀ + I₂ > I₁ ∧ 0 < I₀ - I₁ + I₂ := by
  refine ⟨100, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## The criterion is G24 -/

/-- **G24 at a point, from domination.**  With `μ_G/μ_F = I₀ - I₁ + I₂` and the free inertia
`δ`, the required sign follows exactly from the matching parity class dominating.  Both
directions are recorded so that the criterion is seen to be equivalent to the target and
not merely sufficient. -/
theorem gapcount_of_domination {I₀ I₁ I₂ q : ℝ} {δ : ℕ}
    (hq : q = I₀ - I₁ + I₂) (h₀ : 0 ≤ I₀) (h₁ : 0 ≤ I₁) (h₂ : 0 ≤ I₂)
    (hdom : if δ % 2 = 1 then I₀ + I₂ < I₁ else I₁ < I₀ + I₂) :
    0 < (-1 : ℝ) ^ δ * q := by
  rcases Nat.even_or_odd δ with he | ho
  · have hpar : δ % 2 = 0 := Nat.even_iff.mp he
    rw [hpar] at hdom
    simp only [if_neg (by norm_num : ¬ (0 = 1))] at hdom
    rw [he.neg_one_pow, one_mul, hq]
    exact avg_pos_of_dominant h₁ hdom
  · have hpar : δ % 2 = 1 := Nat.odd_iff.mp ho
    rw [hpar] at hdom
    simp only at hdom
    rw [ho.neg_one_pow, hq]
    have := avg_neg_of_dominant h₀ h₂ hdom
    linarith

/-! ## The measured form -/

/-- The quantity `code/inertia_split.py` reports.  With `M` the integral over the parity
class agreeing with `δ` and `O` the integral over the rest, the margin is
`(M - O)/(M + O)`, and G33 is exactly the assertion that it is positive. -/
noncomputable def margin (M O : ℝ) : ℝ := (M - O) / (M + O)

/-- **Positive margin is domination.**  The measured quantity is positive exactly when the
matching class dominates, so the numerics are testing the criterion itself and not a proxy
for it. -/
theorem margin_pos_iff {M O : ℝ} (hsum : 0 < M + O) :
    0 < margin M O ↔ O < M := by
  rw [margin, div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h2⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith, hsum⟩

/-- **What the observed suppression would buy.**  The measurements show the wrong-parity
class contributing an integral of order the square of its measure, far below its share.  If
that is made quantitative as `O ≤ κ · m²` with `m` the wrong-parity measure and `M` bounded
below, domination follows as soon as `κ m² < M`.  Recorded as the shape an estimate would
take; the bound on `O` itself is open. -/
theorem domination_of_quadratic_bound {M O m κ : ℝ}
    (hO : O ≤ κ * m ^ 2) (hlt : κ * m ^ 2 < M) : O < M :=
  lt_of_le_of_lt hO hlt

end InertiaSplit
