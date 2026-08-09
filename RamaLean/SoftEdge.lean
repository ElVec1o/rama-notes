import Mathlib

/-!
# The biregular margin vanishes at the soft-edge rate

For a `(δ,q)`-biregular graph the universal cover is the `(δ,q)`-biregular tree, whose spectrum
is `{0}` together with `±[g, √(δ-1)+√(q-1)]` for `g = √(q-1) - √(δ-1)`.  The biregular case of
Conjecture 10, which is exactly Song, Fan and Miao's Problem 1, therefore says

  `x_min(μ_G) ≥ g`  for every `(δ,q)`-biregular `G`,

with `x_min` the smallest positive root.  The *margin* is `x_min - g`.

`CompleteBipartiteMargin` proves the margin positive for `K_{δ,q}`, with limit
`√(δ-1) - h_δ/2 ≈ 0.55`.  But the complete bipartite graph is **not** extremal: random
`(δ,q)`-biregular graphs do worse, and worse as they grow.  For `(3,6)` the minimum margin over
twelve samples falls monotonically across fourteen sizes, `0.5301` at `n = 12` down to `0.2009`
at `n = 51`, and a log-log fit gives

  `margin ≈ 2.78 · n^(-0.6675)`,  `R² = 0.9999`,

with `(3,9)` giving `-0.6331` at `R² = 0.9995` (`code/softedge.py`).  On that evidence the
exponent was read as `-2/3`, the soft-edge scale of random matrix theory.

**That reading was too strong, and eight families correct it.**  With a generator that does not
reject (a deterministic biregular base plus degree-preserving double-edge swaps) and a
vectorised bitmask permanent, the fit runs over `d = 3,4,5,6` at `R² ≥ 0.999` throughout, and
the exponent is *not* universal.  It tracks the aspect ratio `q/d`:

  `q/d = 2` (four families): `-0.6703 ± 0.015`
  `q/d = 3` (three families): `-0.6267 ± 0.007`
  `q/d = 4` (one family):     `-0.6102`

`-2/3` is right for `q = 2d` and wrong elsewhere, and three checks say the dependence is real.
Local exponents between consecutive sizes do not converge across aspect ratios: their spread is
`0.016` at small `r` and `0.021` at large `r`, so it is not a correction-term artefact.  It is
also not a matter of which size variable is used, since `n`, `r`, `m` and the edge count are
all proportional at fixed `(d,q)`, so the exponent against any of them is identical.  And it is
not a sampling artefact: the margin is estimated as a minimum over random graphs, whose upward
bias grows with `r`, but moving from three to sixteen samples shifts the exponent by at most
`0.005`, and the unbiased sample-*mean* estimator shows the same spread across families
(`± 0.016`) as the minimum does (`± 0.018`).  Extending to `q/d = 5, 6` the exponent flattens
near `-0.62` rather than continuing to drift, so the picture is two regimes: `-2/3` at
`q = 2d`, and about `-0.62` for `q ≥ 3d` (`code/softedge3.py`).  The constant behaves the same way: with the
exponent fixed at `-2/3`, `C/(√(d-1)+√(q-1))` has mean `0.766` but a 6% spread that is again
monotone in `q/d` (`code/softedge2.py`).

## Why the exponent matters

Whatever its exact value, it is positive, and that is what changes the character of the problem:

* the margin **tends to zero**, so no size-free bound can ever prove Problem 1 or D3;
* it tends to zero **from above**, so both are true and merely tight;
* the right statement is a **Friedman-type edge theorem**: the roots of `μ_G` fill out the
  spectrum of the universal cover without escaping it, exactly as the eigenvalues of a random
  `d`-regular graph fill out `[-2√(d-1), 2√(d-1)]` without escaping.

That is the Alon-Boppana analogy the note already draws, now with a measured rate.

## What this file proves

The exponent is measured, not proved, so it enters as a hypothesis in the only form that
matters structurally: that the margin tends to zero.  From that, `no_uniform_lower_bound` says a
quantity positive at every size can still admit no uniform positive lower bound.  This is the
precise sense in which the conjecture is *true but tight*, and it is a genuine constraint on any
proof: every argument that produces a constant independent of `n`, as the Gershgorin bound of
`CompleteBipartiteMargin` does, is thereby known to be insufficient in general.

`power_law_tendsto_zero` records that an inverse power law has exactly this shape, and
`exponent_floor` sharpens the constraint: no lower bound may decay *slower* than the measured
upper bound, so a proof must reach the measured exponent and not merely some power.

## Status

`no_uniform_lower_bound`, `power_law_tendsto_zero`, `exponent_floor`, `inf_not_attained` and
`edge_unimprovable` are `VERIFIED`.  That
the margin obeys a power law is `HEURISTIC` but strong: eight families, `d = 3` to `6`, thirteen
or fourteen sizes each, `R² ≥ 0.999` throughout.  That the exponent is exactly `-2/3` is
`FALSE` as a universal claim; it holds for `q = 2d` and drifts to about `-0.61` at `q = 4d`.
That the margin stays positive, which is D3 restricted to biregular graphs, is a `CONJECTURE`.
-/

namespace SoftEdge

open Filter Topology

/-- **True at every size, yet not uniformly true.**  If a margin is strictly positive for every
graph but tends to zero with size, then no positive constant bounds it below.  So a conjecture
of the form "the margin is positive" can hold while every size-free proof of it fails. -/
theorem no_uniform_lower_bound {marg : ℕ → ℝ}
    (hpos : ∀ n, 0 < marg n)
    (hlim : Tendsto marg atTop (𝓝 0)) :
    (∀ n, 0 < marg n) ∧ ¬ ∃ c, 0 < c ∧ ∀ n, c ≤ marg n := by
  refine ⟨hpos, ?_⟩
  rintro ⟨c, hc, hcle⟩
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hc).exists
  exact absurd (hcle n) (not_le.mpr hn)

/-- An inverse power law is positive at every size and tends to zero: the shape the measured
margin has, with `a = 2/3`. -/
theorem power_law_tendsto_zero {C a : ℝ} (_hC : 0 < C) (ha : 0 < a) :
    Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  simpa using h.const_mul C

/-- The two together: a power-law margin is positive at every size and admits no uniform
positive lower bound.  This is the exact sense in which the biregular case of Conjecture 10 is
true but tight. -/
theorem power_law_pos_not_uniform {C a : ℝ} (hC : 0 < C) (ha : 0 < a)
    (hpos : ∀ n : ℕ, 0 < C * (n : ℝ) ^ (-a)) :
    (∀ n : ℕ, 0 < C * (n : ℝ) ^ (-a)) ∧
      ¬ ∃ c, 0 < c ∧ ∀ n : ℕ, c ≤ C * (n : ℝ) ^ (-a) :=
  no_uniform_lower_bound hpos (power_law_tendsto_zero hC ha)

/-- **The exponent is a floor on any proof.**  If the margin is bounded above by `C n^(-α)`,
then no lower bound `c n^(-β)` with `β < α` can hold: a slower-decaying lower bound would
eventually exceed the upper bound.  So a proof of Problem 1 must produce a bound decaying at
least as fast as the measured rate, which rules out every argument that stops short of it. -/
theorem exponent_floor {C c α β : ℝ} (hC : 0 < C) (hc : 0 < c) (hlt : β < α)
    (h : ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ (-β) ≤ C * (n : ℝ) ^ (-α)) : False := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(α - β))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hsmall, hn1⟩ :=
    ((hlim.eventually_lt_const (div_pos hc hC)).and (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hrw : (n : ℝ) ^ (-β) * (n : ℝ) ^ (-(α - β)) = (n : ℝ) ^ (-α) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hb := h n hn1
  have hcomm : C * (n : ℝ) ^ (-α) = (C * (n : ℝ) ^ (-(α - β))) * (n : ℝ) ^ (-β) := by
    rw [← hrw]; ring
  rw [hcomm] at hb
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-β) := Real.rpow_pos_of_pos hn0 _
  have hle : c ≤ C * (n : ℝ) ^ (-(α - β)) := le_of_mul_le_mul_right hb hpos
  have : c / C ≤ (n : ℝ) ^ (-(α - β)) := by
    rw [div_le_iff₀ hC]; linarith [hle]
  exact absurd hsmall (not_lt.mpr this)

/-! ## The Friedman picture: sharp, attained only in the limit -/

/-- **The edge is the infimum and is never reached.**  If the margin is strictly positive at
every size but tends to zero, the spectral edge `g` is the greatest lower bound of the smallest
positive roots and is not among them.  This is the exact shape of a Friedman-type theorem: the
roots fill out `spec(T)` right up to its edge without ever escaping. -/
theorem inf_not_attained {a : ℕ → ℝ} {g : ℝ}
    (hgt : ∀ n, g < a n) (hlim : Tendsto a atTop (𝓝 g)) :
    IsGLB (Set.range a) g ∧ g ∉ Set.range a := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact (hgt n).le
  · intro b hb
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hb ⟨n, rfl⟩)
  · rintro ⟨n, hn⟩
    exact absurd hn (hgt n).ne'

/-- **The bound is unimprovable.**  No constant above the spectral edge bounds the smallest
positive roots from below, so `g` is not merely a bound but the best one.  Together with
`inf_not_attained` this says the conjecture, if true, is sharp in both directions: `g` always
works and nothing larger ever does. -/
theorem edge_unimprovable {a : ℕ → ℝ} {g : ℝ}
    (hlim : Tendsto a atTop (𝓝 g)) :
    ∀ g', g < g' → ∃ n, a n < g' := by
  intro g' hg'
  exact (hlim.eventually_lt_const hg').exists

/-- **Problem 1, restated as a margin.**  The biregular case of Conjecture 10 says the smallest
positive root clears the inner edge of the biregular tree spectrum.  Recorded so that the
target of the measurement is unambiguous. -/
def BiregularMarginPositive (xmin g : ℕ → ℝ) : Prop := ∀ n, g n < xmin n

/-- A positive margin at every size is exactly Problem 1, whatever the rate at which it decays;
the decay constrains proofs, not truth. -/
theorem problem1_iff_margin {xmin g : ℕ → ℝ} :
    BiregularMarginPositive xmin g ↔ ∀ n, 0 < xmin n - g n := by
  constructor
  · exact fun h n => sub_pos.mpr (h n)
  · exact fun h n => sub_pos.mp (h n)

end SoftEdge
