import Mathlib

/-!
# The moment ladder, and the reach of a dimension-restricted bound

The two unconditional bounds for the plane class come from the first two power sums of the
`y`-roots, where `y = x²` and `F_A(x) = x^m - M_1x^{m-2} + M_2x^{m-4} - ⋯`, so that the `M_r` are
the elementary symmetric functions of the `y`.  This file records the scheme they belong to and
what it can reach.

## The ladder

For nonnegative `y` and any `k ≥ 1`,

  `y_max^k ≤ ∑_i y_i^k = p_k`,

so any a-priori bound `p_k ≤ B^k` forces `y_max ≤ B`.  Taking `B = 4a` is the band
`|x| ≤ 2√a`.  Writing `p_k = (m/2)c_k^k`, the band therefore holds whenever

  `m ≤ 2(4a/c_k)^k`,

which is `reach_of_moment`.  The note's two bounds are `k = 1` and `k = 2` of this, with
`c_1 = a` and `c_2 = √(a(2a-1))`, giving `m ≤ 8` and `m ≤ 32a/(2a-1)`.

## What the ladder reaches

Measured on the class, `c_k^k` is the number of closed walks of length `2k` from a root of the
`a`-regular tree: `c_1 = a`, `c_2 = √(a(2a-1))`, and so on (`code/moments2.py`).  That count grows
like `(4(a-1))^k k^{-3/2}`, the base being the square of the tree's spectral radius, whereas the
target is `(4a)^k`.  The ratio is `(a/(a-1))^k` up to a polynomial factor, so the reachable
dimension grows without bound: at `a = 3` the measured reach is `146`, `509` and `1489` at
`k = 5, 7, 9`, against the `8` and `18` of the first two rungs.

**So the dimension restriction is not intrinsic to the method; it is an artefact of stopping at
two moments.**  What removing it requires is an a-priori bound `p_k ≤ (m/2)W_{2k}` for the whole
plane class, with `W_{2k}` the tree walk count.  For graphs that is Godsil's path-tree argument,
the path tree being a subtree of the universal cover so its walk counts are dominated.  For
noncommuting plane families it is open, and it is the natural next target: it would replace every
dimension-restricted bound at once.

## Status

`max_pow_le_sum`, `le_of_power_sum_le` and `reach_of_moment` are `VERIFIED`.  The identification
of `c_k^k` with the tree walk count is `HEURISTIC`, measured; the moment bound for the plane
class is a `CONJECTURE`.
-/

namespace MomentLadder

open Finset

/-- The largest entry, raised to any power, is at most the corresponding power sum. -/
theorem max_pow_le_sum {ι : Type*} [Fintype ι] (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i)
    (i₀ : ι) (k : ℕ) :
    (y i₀) ^ k ≤ ∑ i, (y i) ^ k := by
  refine single_le_sum (f := fun i => (y i) ^ k) (fun i _ => pow_nonneg (hy i) k) (mem_univ i₀)

/-- **A bound on one power sum bounds every entry.**  If `∑ y_i^k ≤ B^k` with `B ≥ 0` and
`k ≥ 1`, then every `y_i ≤ B`.  This is the step the two unconditional bounds use at `k = 1`
and `k = 2`, and it is available at every `k`. -/
theorem le_of_power_sum_le {ι : Type*} [Fintype ι] (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i)
    {B : ℝ} (hB : 0 ≤ B) {k : ℕ} (hk : 0 < k) (h : ∑ i, (y i) ^ k ≤ B ^ k) (i₀ : ι) :
    y i₀ ≤ B := by
  have h1 : (y i₀) ^ k ≤ B ^ k := le_trans (max_pow_le_sum y hy i₀ k) h
  exact le_of_pow_le_pow_left₀ hk.ne' hB h1

/-- **The reach of the `k`-th rung.**  If the `k`-th power sum is `(m/2)c^k` and the band needs
it at most `(4a)^k`, the bound covers dimension `m` exactly when `m ≤ 2(4a/c)^k`.  The reach
therefore grows geometrically in `k` at rate `4a/c`, which exceeds one whenever `c < 4a`. -/
theorem reach_of_moment {m a c : ℝ} (hc : 0 < c) (k : ℕ)
    (h : (m / 2) * c ^ k ≤ (4 * a) ^ k) :
    m ≤ 2 * ((4 * a) / c) ^ k := by
  have hck : 0 < c ^ k := pow_pos hc k
  have hmul : m * c ^ k = 2 * ((m / 2) * c ^ k) := by ring
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ hck, hmul]
  linarith

/-- **The restriction is removable when `c < 4a`.**  If the per-moment constant stays below the
target, the reachable dimension exceeds any given bound for `k` large, since `(4a/c)^k` is
unbounded.  This is the shape the measurements exhibit, with `c` increasing to `4(a-1)`. -/
theorem reach_unbounded {a c : ℝ} (hc : 0 < c) (hlt : c < 4 * a) (M : ℝ) :
    ∃ k : ℕ, M < 2 * ((4 * a) / c) ^ k := by
  have h1 : 1 < (4 * a) / c := (one_lt_div hc).mpr hlt
  have ht := tendsto_pow_atTop_atTop_of_one_lt h1
  obtain ⟨k, hk⟩ := (ht.eventually_gt_atTop (max M 0 / 2)).exists
  refine ⟨k, ?_⟩
  have : max M 0 / 2 < ((4 * a) / c) ^ k := hk
  have hM : M ≤ max M 0 := le_max_left _ _
  linarith

end MomentLadder
