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

So the *reach* of the scheme is unbounded, and removing the dimension restriction needs only an
a-priori bound on `p_k` for the whole plane class.  The rest of this file is about whether such
a bound is available, and the answer is no: the reach grows with `k`, but so does the strength
of the input it consumes, and in the limit the two coincide.

## The tree bound is false off the coordinate case

The natural candidate was `p_k ≤ (m/2)W_{2k}` itself, with `W_{2k}` the tree walk count.  For
graphs that is Godsil's path-tree argument, the path tree being a subtree of the universal cover
so its walk counts are dominated.  **For noncommuting plane families it is false**
(`code/momentbound.py`, verified in `code/p16verify.py`): coordinate families obey it, with
equality at `k = 1, 2`, while weighted families with `Adj(A) = aI` exact to machine precision
exceed it by `1.008` at `m = 6`, `1.134` at `m = 8` and `1.315` at `m = 10`, all at `a = 3`.
The excess grows with both `k` and `m`, so no constant-factor version survives either.  The
separation is exactly the coordinate structure: the path-tree argument is unavailable off that
case, and the measurement says nothing replaces it verbatim.

## Only the rate matters, and that is what closes it

The refutation looks at first like it costs a constant rather than the method, since the ladder
never needed the walk count, only its growth rate: `W_{2k}^{1/k} → 4(a-1)`, the square of the
tree's spectral radius, while the target is `(4a)^k`.  An excess

  `p_k ≤ (m/2) R^k W_{2k}`

gives reach `m ≤ 2(4a/(4(a-1)R))^k`, unbounded in `k` exactly when

  `R < a/(a-1)`

(`rate_lt_target`, `reach_unbounded_of_rate`), which is `1.5` at `a = 3` and `1.333` at `a = 4`;
at or above the threshold every rung collapses to the same trivial bound
(`reach_trivial_of_rate`).  Measured, `R_m` sits far inside: `0.97, 1.02, 1.05, 1.07, 1.09` at
`m = 6, 8, 10, 12, 14`, `a = 3` (`code/excessrate.py`).  But it grows monotonically in `m`, and
the increments decay about like `0.28/m`, which integrates to a logarithmic divergence crossing
`1.5` near `m ≈ 60`.  The measurement does not settle it either way.

**What settles it is that `R_m` is not an independent quantity.**  At fixed `m` the power sums
are dominated by the largest root, `p_k ≍ y_max^k`, so `r_k^{1/k} → y_max/(4(a-1))` and the
criterion `R < a/(a-1)` reads `y_max < 4a`: the band itself.  `band_of_all_moments` proves the
general form — a bound `p_k ≤ C·c^k` holding at every rung, with `C` free of `k`, already gives
`y_max ≤ c` outright — and `uniform_input_is_the_band` specialises it to this scheme.

So there is no rate `R` that is simultaneously weak enough to be provable by other means and
strong enough to give the band: at `R < a/(a-1)` the hypothesis is strictly stronger than the
conclusion, and at `R ≥ a/(a-1)` the reach is trivial.  **The dimension restriction is intrinsic
to any uniform-in-`k` use of the ladder.**  What remains is a bound at one finite `k`, which
buys the finite range `2(4a/c)^k` and nothing more; the only natural candidate there, the tree
count, is refuted above.

## Status

`max_pow_le_sum`, `le_of_power_sum_le`, `reach_of_moment`, `reach_unbounded`, `rate_lt_target`,
`reach_unbounded_of_rate`, `reach_trivial_of_rate`, `band_of_all_moments` and
`uniform_input_is_the_band` are `VERIFIED`.  The identification of `c_k^k` with the tree walk
count is `HEURISTIC`, measured.  The tree moment bound `R = 1` is `REFUTED` for the plane class,
by measurement.  The no-go for uniform-in-`k` rates is `VERIFIED`, not measured; a bound at a
single finite `k` beyond the two already in the note remains `OPEN`.
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

/-! ## The excess rate, and the threshold it must beat

The tree bound `p_k ≤ (m/2)W_{2k}` is the case `R = 1` below, and it is false for the plane
class.  What the ladder actually needs is only that the excess grows at a rate `R` slow enough
that `R` times the tree rate `4(a-1)` still falls short of the target `4a`. -/

/-- **The threshold.**  With the tree rate `4(a-1)`, an excess rate `R` keeps the ladder's base
above one exactly when `R < a/(a-1)`.  This is `1.5` at `a = 3` and `4/3` at `a = 4`. -/
theorem rate_lt_target {a R : ℝ} (ha : 1 < a) :
    R * (4 * (a - 1)) < 4 * a ↔ R < a / (a - 1) := by
  have h1 : (0 : ℝ) < a - 1 := by linarith
  rw [lt_div_iff₀ h1]
  have e : R * (4 * (a - 1)) = 4 * (R * (a - 1)) := by ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- **Below the threshold the ladder still reaches every dimension.**  If the plane class
satisfies `p_k ≤ (m/2)R^k W_{2k}` with `W_{2k}^{1/k} → 4(a-1)` and `R < a/(a-1)`, the reachable
dimension `2(4a/(4(a-1)R))^k` exceeds any bound for `k` large.  So refuting the tree bound
`R = 1` costs the method a constant, not its unbounded reach. -/
theorem reach_unbounded_of_rate {a R : ℝ} (ha : 1 < a) (hR : 0 < R)
    (hlt : R < a / (a - 1)) (M : ℝ) :
    ∃ k : ℕ, M < 2 * ((4 * a) / (R * (4 * (a - 1)))) ^ k := by
  have h1 : (0 : ℝ) < a - 1 := by linarith
  have hc : 0 < R * (4 * (a - 1)) := by positivity
  exact reach_unbounded hc ((rate_lt_target ha).mpr hlt) M

/-- **At or above the threshold the ladder is closed.**  Every rung then gives the same trivial
bound `m ≤ 2`, since the base is at most one, so no amount of climbing helps.  This is the
no-go the measurement has to rule out. -/
theorem reach_trivial_of_rate {a R : ℝ} (ha : 1 < a) (hge : a / (a - 1) ≤ R) (k : ℕ) :
    ((4 * a) / (R * (4 * (a - 1)))) ^ k ≤ 1 := by
  have h1 : (0 : ℝ) < a - 1 := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hR : 0 < R := lt_of_lt_of_le (div_pos ha0 h1) hge
  have hc : 0 < R * (4 * (a - 1)) := by positivity
  have h2 : a ≤ R * (a - 1) := by rwa [div_le_iff₀ h1] at hge
  have hle : 4 * a ≤ R * (4 * (a - 1)) := by nlinarith
  exact pow_le_one₀ (by positivity) ((div_le_one hc).mpr hle)

/-! ## The no-go: at a uniform rate the input is the conclusion

Everything above is about what a bound at ONE rung buys.  The following says what a bound at
EVERY rung buys, and the answer is: exactly itself.  The dimension factor `m/2` in front is
harmless, being a constant in `k`, so it washes out of the geometric comparison. -/

/-- **A moment bound held at every rung is the band it would prove.**  If `∑ y_i^k ≤ C c^k` for
every `k ≥ 1`, with `C` not depending on `k`, then `y_i ≤ c` outright.

This is the no-go for the ladder.  The input `p_k ≤ (m/2)(R·4(a-1))^k` is `C = m/2` and
`c = 4(a-1)R`, so holding it at every rung already gives `y_max ≤ 4(a-1)R`; and the rate
condition `R < a/(a-1)` that makes the reach unbounded (`reach_unbounded_of_rate`) is precisely
`4(a-1)R < 4a`, that is the band.  So no uniform-in-`k` input of this shape is weaker than the
conclusion it is supposed to establish.  The method has content only at finite `k`, where the
reach `2(4a/c)^k` is finite, and the dimension restriction is intrinsic to that. -/
theorem band_of_all_moments {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    {C c : ℝ} (hc : 0 < c)
    (h : ∀ k : ℕ, 1 ≤ k → ∑ i, (y i) ^ k ≤ C * c ^ k) (i₀ : Fin n) :
    y i₀ ≤ c := by
  rcases le_or_gt (y i₀) c with hok | hcon
  · exact hok
  exfalso
  have h1 : 1 < y i₀ / c := (one_lt_div hc).mpr hcon
  have ht := tendsto_pow_atTop_atTop_of_one_lt h1
  obtain ⟨k, hkC, hk1⟩ :=
    ((ht.eventually_gt_atTop C).and (Filter.eventually_ge_atTop 1)).exists
  have hck : 0 < c ^ k := pow_pos hc k
  have hle : (y i₀) ^ k ≤ C * c ^ k := le_trans (max_pow_le_sum y hy i₀ k) (h k hk1)
  have hbad : (y i₀ / c) ^ k ≤ C := by rw [div_pow, div_le_iff₀ hck]; exact hle
  linarith

/-- The contrapositive, as the ladder actually meets it: to reach the band `y_max ≤ 4a` from a
uniform rate one needs `R ≤ a/(a-1)`, and at that rate the input already says `y_max ≤ 4a`.
There is no `R` that is both provable-because-weaker and useful-because-strong. -/
theorem uniform_input_is_the_band {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    {C a R : ℝ} (ha : 1 < a) (hR : 0 < R)
    (h : ∀ k : ℕ, 1 ≤ k → ∑ i, (y i) ^ k ≤ C * (R * (4 * (a - 1))) ^ k) (i₀ : Fin n) :
    y i₀ ≤ R * (4 * (a - 1)) := by
  have h1 : (0 : ℝ) < a - 1 := by linarith
  exact band_of_all_moments y hy (by positivity) h i₀

end MomentLadder
