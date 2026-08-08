import Mathlib
import RamaLean.ShellBound

/-!
# The geometric mean closes the gap

`ShellBound` makes the upper half of the estimate unconditional:
`I_wrong ≤ M L c^{-1/b} m^{1+1/b}`, which at `b = 2` is `m^{3/2}`.  What remained was a lower
bound on `I_right`, and the obvious candidate turns out to be circular.

## Why the obvious route fails

Splitting the average by inertia class gives `μ_G/μ_F = I₀ - I₁ + I₂` **identically**, so
`I_right - I_wrong = |μ_G/μ_F|`.  Bounding `I_right` below by `|μ_G/μ_F|` therefore assumes
precisely the sign that is to be proved, and no independent lower bound on `|μ_G(x)|` is
available inside a gap: Heilmann–Lieb gives root-free intervals only outside `[-ρ,ρ]`, which
is the region where the conjecture is already known.  `code/jensen_route.py` confirms the
identity numerically, to `10^{-15}`.

## The substitute

Jensen, in the form that the arithmetic mean dominates the geometric mean, gives

  `I_total = ∫ |det S| ≥ exp(∫ log |det S|) =: Δ`,

and `Δ` is a Mahler measure of the abelian cover.  It owes nothing to the sign of `μ_G`, so
this is not circular.  Since `I_total = I_right + I_wrong`,

  `I_right ≥ Δ - I_wrong`,   and domination follows as soon as `Δ > 2 I_wrong`.

The geometric mean was identified in `InertiaSplit`'s companion note as the *source* of the
obstruction, the quantity the free side computes while `μ_G` computes an arithmetic mean.
It reappears here as the *tool*.

Measured across both internal gaps of two triangles joined by an edge, `Δ` sits between
`0.759` and `0.823` while `I_wrong` runs from `10^{-4}` to `10^{-2}`, so `Δ/(2 I_wrong)` runs
between `41` and `3927`.  The margin is not marginal.

## Status

`amgm_finite` and `jensen_lower_bound` are proved: the discrete arithmetic-geometric mean
inequality in the form the numerics use, and the assembly.  What is open is a lower bound on
`Δ` itself, uniform enough to beat `m^{3/2}`.  That is `G44`, and unlike its predecessors it
is a question about a Mahler measure, where coefficient bounds of Mahler type are available
and are not circular.
-/

namespace JensenRoute

open Finset

/-! ## Arithmetic dominates geometric -/

/-- **The discrete arithmetic-geometric mean inequality**, in the uniform-weight form the
numerical integration uses: the average of nonnegative numbers is at least the product of
their `1/N` powers. -/
theorem amgm_finite {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hs : s.Nonempty) :
    ∏ i ∈ s, f i ^ ((s.card : ℝ)⁻¹) ≤ ∑ i ∈ s, (s.card : ℝ)⁻¹ * f i := by
  have hpos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  refine Real.geom_mean_le_arith_mean_weighted s _ f (fun i _ => by positivity) ?_ hf
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ## The assembly -/

/-- **Domination from the geometric mean.**  If the total integral is at least `Δ`, splits
as `I_right + I_wrong`, and the wrong part is at most `B` with `Δ > 2B`, then the right part
strictly dominates.  This is the criterion of `InertiaSplit`, reached without any appeal to
the sign of `μ_G`. -/
theorem jensen_lower_bound {Ir Iw Δ B : ℝ}
    (htot : Δ ≤ Ir + Iw) (hub : Iw ≤ B) (hmargin : 2 * B < Δ) : Iw < Ir := by
  linarith

/-- The same with the shell bound substituted, so the hypothesis is the one that remains
open: `Δ` must beat twice the `m^{3/2}` bound. -/
theorem domination_of_mahler {Ir Iw Δ m c M L : ℝ}
    (htot : Δ ≤ Ir + Iw)
    (hshell : Iw ≤ M * L * Real.sqrt (m / c) * m)
    (hmargin : 2 * (M * L * Real.sqrt (m / c) * m) < Δ) : Iw < Ir :=
  jensen_lower_bound htot hshell hmargin

end JensenRoute
