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

with `(3,9)` giving `-0.6331` at `R² = 0.9995` (`code/softedge.py`).  The exponent is `-2/3`.

## Why the exponent matters

`n^(-2/3)` is the soft-edge scale of random matrix theory, the rate at which extreme
eigenvalues approach a spectral edge.  Read that way the picture is:

* the margin **tends to zero**, so no size-free bound can ever prove Problem 1 or D3;
* it tends to zero **from above**, so both are true and merely tight;
* the right statement is a **Friedman-type edge theorem**: the roots of `μ_G` fill out the
  spectrum of the universal cover without escaping it, exactly as the eigenvalues of a random
  `d`-regular graph fill out `[-2√(d-1), 2√(d-1)]` without escaping.

That is the Alon-Boppana analogy the note already draws, now with an exponent on it.

## What this file proves

The exponent is measured, not proved, so it enters as a hypothesis in the only form that
matters structurally: that the margin tends to zero.  From that, `no_uniform_lower_bound` says a
quantity positive at every size can still admit no uniform positive lower bound.  This is the
precise sense in which the conjecture is *true but tight*, and it is a genuine constraint on any
proof: every argument that produces a constant independent of `n`, as the Gershgorin bound of
`CompleteBipartiteMargin` does, is thereby known to be insufficient in general.

`power_law_tendsto_zero` records that an inverse power law has exactly this shape.

## Status

`no_uniform_lower_bound` and `power_law_tendsto_zero` are `VERIFIED`.  That the margin obeys
`n^(-2/3)` is `HEURISTIC`, on fourteen sizes in one family and six in another, with the fit
quality quoted above.  That it stays positive, which is D3 restricted to biregular graphs, is a
`CONJECTURE`.
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
