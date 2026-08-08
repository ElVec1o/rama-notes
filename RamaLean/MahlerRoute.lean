import Mathlib
import RamaLean.JensenRoute

/-!
# What `Δ` is, and what a lower bound on it would need

`JensenRoute` reduces feedback vertex number two to one inequality, `Δ > 2 I_wrong`, with
`Δ = exp(∫ log |det S(x,z)| dz)`.  This file identifies `Δ` and records the classical route
to bounding it below, marking exactly which step is not yet in hand.

## `Δ` is a Mahler measure

The Schur complement satisfies `det(x I - A_G(z)) = μ_F(x) · det S(x,z)`, since the forest
block carries no torus variable once the spanning tree is chosen inside `F`.  Taking `log`,
averaging over `T^b` and exponentiating,

  `Δ = M(P_x) / |μ_F(x)|`,   `P_x(z) = det(x I - A_G(z))`,

with `M` the Mahler measure.  That is `mahler_of_factor` below.  Nothing here depends on the
sign of `μ_G`, which is what makes the route non-circular.

## The classical bound, and the gap

For a Laurent polynomial, the Mahler measure is at least the absolute value of the
coefficient at any **vertex** of the Newton polytope; iterating the one-variable Jensen
formula gives it.  For `P_x` the torus variables enter only through cotree edges, and a
permutation traverses a given cotree edge at most once in each direction, so each exponent
lies in `{-1,0,1}` and the Newton polytope sits inside `[-1,1]^b`.

What is missing is the identification of a vertex coefficient that is bounded below away
from zero, uniformly in `x` across a gap.  The extreme coefficient counts permutations
traversing every cotree edge in one direction, weighted by `x` to the number of fixed points,
and whether that count can vanish through cancellation is not settled here.  That is `G47`.

## Status

`mahler_of_factor` and `delta_lower_of_mahler` are proved.  The vertex-coefficient bound
enters as a hypothesis, and the identification of a nonvanishing vertex coefficient is open.
Measured values of `Δ` are stable near `0.78` across a gap while `I_wrong` varies by two
orders of magnitude, which is why the margin is large; but stability observed is not
stability proved.
-/

namespace MahlerRoute

/-! ## `Δ` as a Mahler measure over `μ_F` -/

/-- **The factorisation, at the level of the averaged logarithm.**  If
`log|P| = log|μF| + log|detS|` pointwise and the average of `log|detS|` is `L`, then
`exp` of the average of `log|P|` is `|μF|` times `exp L`.  Stated on the averages so that no
integration theory is needed: the content is that `μ_F` is constant in `z`. -/
theorem mahler_of_factor {avgP avgS lmu : ℝ} (h : avgP = lmu + avgS) :
    Real.exp avgP = Real.exp lmu * Real.exp avgS := by
  rw [h, Real.exp_add]

/-- Consequently `Δ = M / |μ_F|`, with `M = exp(avg log|P|)` the Mahler measure. -/
theorem delta_eq {M Δ mu : ℝ} (hmu : 0 < mu) (h : M = mu * Δ) : Δ = M / mu := by
  rw [h]
  field_simp

/-! ## From a Mahler bound to the margin -/

/-- **The route, assembled.**  A lower bound `M ≥ A` on the Mahler measure gives
`Δ ≥ A / |μ_F(x)|`, and the margin condition of `JensenRoute` follows as soon as that beats
twice the shell bound.  The hypothesis `hM` is the classical vertex-coefficient bound and
`hbeat` is what remains to be checked. -/
theorem delta_lower_of_mahler {M Δ mu A B : ℝ} (hmu : 0 < mu)
    (hfac : M = mu * Δ) (hM : A ≤ M) (hbeat : 2 * B < A / mu) : 2 * B < Δ := by
  have hΔ : Δ = M / mu := delta_eq hmu hfac
  have : A / mu ≤ M / mu := by gcongr
  rw [hΔ]
  linarith

/-- **Closing feedback vertex number two, granted the two open inputs.**  With the
unconditional shell bound on `I_wrong`, a Mahler lower bound `A`, and `A/|μ_F| > 2B`, the
domination criterion holds and with it `GAPCOUNT` at the point in question. -/
theorem domination_of_mahler_bound {Ir Iw Δ M mu A B : ℝ} (hmu : 0 < mu)
    (htot : Δ ≤ Ir + Iw) (hub : Iw ≤ B)
    (hfac : M = mu * Δ) (hM : A ≤ M) (hbeat : 2 * B < A / mu) : Iw < Ir :=
  JensenRoute.jensen_lower_bound htot hub (delta_lower_of_mahler hmu hfac hM hbeat)

end MahlerRoute
