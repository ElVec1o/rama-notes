import Mathlib
import RamaLean.KestenMcKay

/-!
# From matching moments to the cavity ratio, quantitatively

`KestenMcKay` computes the constant `1 + 1/(1+√a)` from the Stieltjes transform of the
Kesten–McKay measure, and leaves one step cited: that the matching measure of an
`a`-regular graph of growing girth converges to Kesten–McKay.  This file removes the
citation, replacing a limit by an explicit finite bound.

## Why a bound is available at all

The evaluation point is `x = 2√a`, and Heilmann–Lieb puts every root of `μ_G` in
`[-ρ, ρ]` with `ρ = 2√(a-1)`.  Since `a - 1 < a`, the point sits **strictly outside** the
support, at distance `2(√a - √(a-1)) > 0`.  So the Stieltjes transform is evaluated off the
spectrum, where a moment expansion converges geometrically with ratio

  `ρ/x = √(a-1)/√a = √(1 - 1/a) < 1`.

Nothing degenerates.  This is the whole reason the argument can be made finite.

## The mechanism, and whose it is

The locality of root moments is due to Abért–Hubai for the chromatic polynomial and to
Csikvári–Frenkel in the generality used here: for a monic multiplicative graph polynomial
of bounded exponential type, the power sum `p_j(G)` is a fixed linear combination of counts
of **connected** subgraphs of `G`.  The matching polynomial is such a polynomial.

Consequently, in an `a`-regular graph the number of copies of a fixed tree is `|V(G)|` times
a function of `a` alone, and evaluating the same combination on the `a`-regular tree gives
the Kesten–McKay moment.  The threshold is set by when a subgraph can fail to be a forest:
in Godsil's formulation the matching-measure moments count closed **tree-like** walks, the
trace of such a walk of length `j` has at most `j/2` edges, and any subgraph with fewer than
`girth(G)` edges is a forest.  Hence

  **`p_j(G)/|V(G)| = m_j(KM_a)` for every `j < 2·girth(G)`,**

an exact identity for a finite graph, with no limit in it.  The threshold `2·girth` is
tight, not merely sufficient: `code/moment_girth.py` computes both sides exactly and finds
the first differing moment at exactly `2·girth` in every case where one exists, for `K_4`,
`K_5`, `K_{3,3}`, `K_{4,4}`, the cube, Petersen and Heawood.

What this file proves is the analytic half: matching moments up to order `k` force the
Stieltjes transforms to agree to within an explicit exponentially small error, hence force
the cavity ratio to.  The combinatorial half is the cited theorem above.

## What is proved here

* `geom_remainder` — the exact finite geometric identity with remainder.  No infinite
  series appears anywhere, which is what keeps everything effective.
* `remainder_le` — the remainder is at most `ρ^{k+1} / (x^{k+1}(x-ρ))`.
* `stieltjes_close` — matching moments to order `k` give
  `|G₁(x) - G₂(x)| ≤ 2ρ^{k+1}/(x^{k+1}(x-ρ))`.
* `inv_close` — and therefore the reciprocals, which are the cavity ratios, agree to
  within that over the square of a lower bound on the transforms.

The constants are not optimised.  Using `|m_j| ≤ ρ^j` throws away the `j^{-3/2}` decay of
the Kesten–McKay moments at the edge, so the bound runs two to three orders above the truth:
at `a = 3` the observed errors are `3.2·10^{-3}` for the cube, `9.2·10^{-4}` for Petersen and
`2.2·10^{-4}` for Heawood, against bounds of `0.62`, `0.41` and `0.28`.  What the bound does
give, and the citation did not, is a rate that is exponential in the girth and a statement
with no limit in it.
-/

namespace MomentTransfer

open Finset

/-! ## The exact geometric remainder -/

/-- **Finite geometric expansion with remainder.**  For `t ≠ x` and `x ≠ 0`,

  `1/(x - t) = ∑_{j<k+1} t^j/x^{j+1} + t^{k+1}/(x^{k+1}(x-t))`.

This is an identity, not an approximation: the right side does not depend on `k`, which is
how the induction below proves it. -/
theorem geom_remainder {x t : ℝ} (hxt : x - t ≠ 0) (hx : x ≠ 0) (k : ℕ) :
    1 / (x - t)
      = (∑ j ∈ range (k + 1), t ^ j / x ^ (j + 1))
        + t ^ (k + 1) / (x ^ (k + 1) * (x - t)) := by
  induction k with
  | zero =>
      simp only [zero_add, range_one, sum_singleton, pow_zero, pow_one, one_div]
      field_simp
      ring
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hxn : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
      have hxn2 : x ^ (n + 2) ≠ 0 := pow_ne_zero _ hx
      rw [ih]
      field_simp
      ring

/-! ## The remainder is small off the support -/

/-- **The remainder bound.**  A root at distance at most `ρ` from the origin, with the
evaluation point `x` strictly beyond `ρ`, contributes a remainder of size at most
`ρ^{k+1}/(x^{k+1}(x-ρ))`. -/
theorem remainder_le {ρ x t : ℝ} (hρ : 0 ≤ ρ) (hx : ρ < x) (ht : |t| ≤ ρ) (k : ℕ) :
    |t ^ (k + 1) / (x ^ (k + 1) * (x - t))| ≤ ρ ^ (k + 1) / (x ^ (k + 1) * (x - ρ)) := by
  have hx0 : 0 < x := lt_of_le_of_lt hρ hx
  have hxk : 0 < x ^ (k + 1) := by positivity
  have hxρ : 0 < x - ρ := by linarith
  have htρ : t ≤ ρ := le_trans (le_abs_self t) ht
  have hxt : 0 < x - t := by linarith
  have hnum : |t| ^ (k + 1) ≤ ρ ^ (k + 1) := pow_le_pow_left₀ (abs_nonneg t) ht _
  have hden : x ^ (k + 1) * (x - ρ) ≤ x ^ (k + 1) * (x - t) := by
    have : x - ρ ≤ x - t := by linarith
    exact mul_le_mul_of_nonneg_left this (le_of_lt hxk)
  rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hx0, abs_of_pos hxt]
  refine div_le_div₀ (by positivity) hnum (by positivity) hden

/-! ## Matching moments force matching transforms -/

/-- **The transfer.**  Two Stieltjes transforms whose measures are supported in `[-ρ,ρ]`
and whose moments agree to order `k` differ by at most `2ρ^{k+1}/(x^{k+1}(x-ρ))` at any
`x > ρ`.

The moment data enters only through `hmatch`; the decomposition hypotheses are what
`geom_remainder` supplies for each measure, and the remainder hypotheses are what
`remainder_le` supplies.  The standing assumptions `0 ≤ ρ < x` are not needed for the
inequality itself, only for the two remainder hypotheses to be the ones `remainder_le`
proves, so they are omitted here. -/
theorem stieltjes_close {ρ x : ℝ} {k : ℕ}
    {m₁ m₂ : ℕ → ℝ} {S₁ S₂ r₁ r₂ : ℝ}
    (hmatch : ∀ j ∈ range (k + 1), m₁ j = m₂ j)
    (hS₁ : S₁ = (∑ j ∈ range (k + 1), m₁ j / x ^ (j + 1)) + r₁)
    (hS₂ : S₂ = (∑ j ∈ range (k + 1), m₂ j / x ^ (j + 1)) + r₂)
    (hr₁ : |r₁| ≤ ρ ^ (k + 1) / (x ^ (k + 1) * (x - ρ)))
    (hr₂ : |r₂| ≤ ρ ^ (k + 1) / (x ^ (k + 1) * (x - ρ))) :
    |S₁ - S₂| ≤ 2 * (ρ ^ (k + 1) / (x ^ (k + 1) * (x - ρ))) := by
  have hsum : (∑ j ∈ range (k + 1), m₁ j / x ^ (j + 1))
      = ∑ j ∈ range (k + 1), m₂ j / x ^ (j + 1) :=
    Finset.sum_congr rfl fun j hj => by rw [hmatch j hj]
  have hdiff : S₁ - S₂ = r₁ - r₂ := by rw [hS₁, hS₂, hsum]; ring
  rw [hdiff]
  calc |r₁ - r₂| ≤ |r₁| + |r₂| := abs_sub _ _
    _ ≤ 2 * (ρ ^ (k + 1) / (x ^ (k + 1) * (x - ρ))) := by linarith

/-- **And therefore the ratios.**  The cavity ratio is `1/G`, so a bound on the transforms
becomes a bound on the ratios, divided by the square of any positive lower bound on them. -/
theorem inv_close {S₁ S₂ c ε : ℝ} (hc : 0 < c) (h₁ : c ≤ S₁) (h₂ : c ≤ S₂)
    (h : |S₁ - S₂| ≤ ε) : |1 / S₁ - 1 / S₂| ≤ ε / c ^ 2 := by
  have hS₁ : 0 < S₁ := lt_of_lt_of_le hc h₁
  have hS₂ : 0 < S₂ := lt_of_lt_of_le hc h₂
  have hrw : 1 / S₁ - 1 / S₂ = (S₂ - S₁) / (S₁ * S₂) := by field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0:ℝ) < S₁ * S₂)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have habs : |S₂ - S₁| = |S₁ - S₂| := abs_sub_comm _ _
  have hcc : c ^ 2 ≤ S₁ * S₂ := by nlinarith
  nlinarith [abs_nonneg (S₂ - S₁), h, habs, hcc]

/-! ## The geometric ratio at the evaluation point -/

/-- **Why the bound decays.**  With `ρ = 2√(a-1)` and `x = 2√a` the ratio `ρ/x` is
`√(1 - 1/a) < 1`, so the transfer bound is exponentially small in the order of matching
moments, hence in the girth. -/
theorem edge_ratio_lt_one {a : ℝ} (ha : 1 < a) :
    2 * Real.sqrt (a - 1) < 2 * Real.sqrt a := by
  have h : Real.sqrt (a - 1) < Real.sqrt a :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

/-- The evaluation point is strictly outside the Heilmann–Lieb support, with a gap that is
positive for every `a > 1`.  This is the hypothesis `hx` of `stieltjes_close`. -/
theorem edge_gap_pos {a : ℝ} (ha : 1 < a) :
    0 < 2 * Real.sqrt a - 2 * Real.sqrt (a - 1) := by
  have := edge_ratio_lt_one ha
  linarith

end MomentTransfer
