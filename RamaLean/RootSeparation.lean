import Mathlib

/-!
# A separation of matching roots from zero, and what it proves

`BiregularBlocking.branch_root_sep` separates roots of the branch factor from zero, but is
vacuous exactly when `F 0 = 0`, which is Hall's case.  The repair is to divide out the zero:
if `F = X^m G` with `G 0 ≠ 0`, the nonzero roots of `F` are the roots of `G`, and `G` is what
should be bounded.  For Hall's branch `F = X⁵(X⁴ - 16X² + 55)`, so `G 0 = 55` and the
obstruction disappears.

## The bound

`cauchy_lower` is the classical Cauchy estimate in the form needed: for a polynomial written
by its coefficients, with nonzero constant term and all other coefficients bounded by `M`,
every root satisfies

  `|θ| ≥ |c₀| / (|c₀| + M)`.

Applied to the matching polynomial this becomes a statement purely about matching numbers.
Writing `ν` for the matching number of `G` and `m_k` for the number of `k`-matchings,
`μ_G(x) = ± x^{n-2ν} · g(x²)` where `g` has constant term `± m_ν`, so every **nonzero** root
`θ` of `μ_G` satisfies

  `θ² ≥ m_ν / (m_ν + max_{k<ν} m_k)`,

which is `matching_root_sep`.

## Why this is not just an obstruction

The inequality is one-sided in the useful direction.  For an `(a,b)`-biregular graph
Conjecture 10 is equivalent to the absence of a nonzero root below
`τ = |√(a-1) - √(b-1)|` (`BiregularBlocking.biregular_reduction`), so whenever the bound
reaches `τ` the conjecture is **proved** for that graph, unconditionally and with no appeal to
Angel–Friedman–Hoory.  That is `sfm_of_separation`.

`code/rootsep.py` runs it: the bound proves Song–Fan–Miao for three of nine biregular graphs
tested, the smaller ones.  It decays with size, `0.63, 0.45, 0.28` against a fixed
`τ = 0.318` for `(3,4)`-biregular as the graph grows, so it settles small cases and not large
ones.  That is a partial positive result, and it is labelled as partial.
-/

namespace RootSeparation

open Finset

/-! ## The Cauchy estimate -/

/-- **Roots are bounded away from zero by the constant coefficient.**  If `∑_{j≤d} c_j θ^j = 0`
with `c₀ ≠ 0` and `|c_j| ≤ M` for `j ≥ 1`, then `|θ| ≥ |c₀| / (|c₀| + M)`.

The proof splits on whether `|θ| < 1`.  Above one the bound is trivial since the right side is
at most one; below one the tail is summed geometrically. -/
theorem cauchy_lower {d : ℕ} (c : ℕ → ℝ) (θ M : ℝ) (hMnn : 0 ≤ M)
    (hM : ∀ j, 1 ≤ j → j ≤ d → |c j| ≤ M)
    (hroot : ∑ j ∈ range (d + 1), c j * θ ^ j = 0) :
    |c 0| / (|c 0| + M) ≤ |θ| := by
  rcases eq_or_ne (c 0) 0 with h0 | h0
  · simp [h0, abs_nonneg]
  have habs : 0 < |c 0| := abs_pos.mpr h0
  have hden : 0 < |c 0| + M := by linarith
  rcases le_or_gt 1 |θ| with hθ | hθ
  · have : |c 0| / (|c 0| + M) ≤ 1 := by
      rw [div_le_one hden]; linarith
    linarith
  -- below one: bound the tail against a geometric sum
  set r := |θ| with hr
  set G := ∑ j ∈ range d, r ^ j with hG
  have hrnn : (0 : ℝ) ≤ r := abs_nonneg θ
  have hone : 0 < 1 - r := by simp only [hr]; linarith
  have htail : |c 0| ≤ M * (r * G) := by
    have hsplit : (∑ j ∈ range d, c (j + 1) * θ ^ (j + 1)) + c 0 = 0 := by
      have h := hroot
      rw [Finset.sum_range_succ'] at h
      simpa using h
    have hc : c 0 = -∑ j ∈ range d, c (j + 1) * θ ^ (j + 1) := by linarith
    rw [hc, abs_neg]
    calc |∑ j ∈ range d, c (j + 1) * θ ^ (j + 1)|
        ≤ ∑ j ∈ range d, |c (j + 1) * θ ^ (j + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ range d, |c (j + 1)| * r ^ (j + 1) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_pow]
      _ ≤ ∑ j ∈ range d, M * r ^ (j + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjd : j + 1 ≤ d := Finset.mem_range.mp hj
          exact mul_le_mul_of_nonneg_right (hM (j + 1) (by omega) hjd)
            (pow_nonneg hrnn _)
      _ = M * (r * G) := by
          rw [hG, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  -- telescoping: (1 - r) * G = 1 - r ^ d
  have hgm : G * (r - 1) = r ^ d - 1 := geom_sum_mul r d
  have hGtel : (1 - r) * G = 1 - r ^ d := by nlinarith [hgm]
  have hpow : (0 : ℝ) ≤ r ^ d := pow_nonneg hrnn d
  have key : |c 0| * (1 - r) ≤ M * r := by
    have h1 : |c 0| * (1 - r) ≤ (M * (r * G)) * (1 - r) :=
      mul_le_mul_of_nonneg_right htail (le_of_lt hone)
    have h2 : (M * (r * G)) * (1 - r) = M * r * ((1 - r) * G) := by ring
    rw [h2, hGtel] at h1
    have h3 : 0 ≤ M * r * r ^ d := mul_nonneg (mul_nonneg hMnn hrnn) hpow
    have h4 : M * r * (1 - r ^ d) = M * r - M * r * r ^ d := by ring
    linarith [h1, h3, h4]
  rw [div_le_iff₀ hden]
  have hexp : |c 0| * (1 - r) = |c 0| - |c 0| * r := by ring
  have hgoal : |θ| * (|c 0| + M) = |c 0| * r + M * r := by rw [← hr]; ring
  rw [hgoal]
  linarith [key, hexp]

/-! ## In terms of matching numbers -/

/-- **Separation of matching roots from zero.**  With `mν` the number of maximum matchings and
`M` a bound on all the other matching numbers, a nonzero root `θ` of the matching polynomial
satisfies `θ² ≥ mν / (mν + M)`.  The hypothesis `hroot` is the even part of the matching
polynomial evaluated at `θ²`, which is where the matching numbers appear as coefficients. -/
theorem matching_root_sep {d : ℕ} (m : ℕ → ℝ) (θ M : ℝ) (hMnn : 0 ≤ M)
    (hM : ∀ j, 1 ≤ j → j ≤ d → |m j| ≤ M)
    (hroot : ∑ j ∈ range (d + 1), m j * (θ ^ 2) ^ j = 0) :
    |m 0| / (|m 0| + M) ≤ θ ^ 2 := by
  have h := cauchy_lower m (θ ^ 2) M hMnn hM hroot
  rwa [abs_of_nonneg (sq_nonneg θ)] at h

/-! ## What it proves -/

/-- **Song–Fan–Miao for a single graph, unconditionally.**  Combined with
`BiregularBlocking.biregular_reduction`, a graph whose separation bound reaches `τ²` has no
nonzero root below `τ`, so Conjecture 10 holds for it with no appeal to
Angel–Friedman–Hoory. -/
theorem sfm_of_separation {d : ℕ} (m : ℕ → ℝ) (θ M τ : ℝ) (hMnn : 0 ≤ M) (hτ : 0 ≤ τ)
    (hM : ∀ j, 1 ≤ j → j ≤ d → |m j| ≤ M)
    (hroot : ∑ j ∈ range (d + 1), m j * (θ ^ 2) ^ j = 0)
    (hbound : τ ^ 2 ≤ |m 0| / (|m 0| + M)) :
    τ ≤ |θ| := by
  have h := matching_root_sep m θ M hMnn hM hroot
  have hsq : τ ^ 2 ≤ θ ^ 2 := le_trans hbound h
  have h2 : τ ^ 2 ≤ |θ| ^ 2 := by rwa [sq_abs]
  nlinarith [abs_nonneg θ, hτ, h2]

end RootSeparation
