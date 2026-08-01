import Mathlib

/-!
# The `ab` bound from the product representation

For rank-`b` orthogonal projections `P_1, …, P_q` on `ℝ^p` with `∑ P_k = a I`, the mixed
characteristic polynomial has the representation

  `y^(q-p) μ(y) = 𝔼_S ∏_k (y - a · s_k(S))`,

where `S` is a determinantal sample and `s_k(S) ∈ {0, …, b}` counts how many of block `k`'s slots
it uses.  Every factor is then strictly positive once `y > ab`, so the whole expectation is, and
`μ` has no root there.  That is the content of `no_root_above` below: a convex combination of
products of positive numbers is positive.

The bound is sharp in a useful place.  Writing `m = (a-1)(b-1)` and `hi = (√(a-1)+√(b-1))²` for the
upper edge of the `(a,b)`-biregular band, `edge_gap` records

  `ab - hi = (√m - 1)²  ≥ 0`,

so `ab` overshoots the conjectured edge by exactly `(√m - 1)²`, and at `a = b = 2` — where `m = 1`
and the gap vanishes — the two coincide and the upper edge is proved outright.  Compared with the
Marchenko–Pastur edge `(√a + √b)²`, which is the only bound the barrier method supplies for
projection families, `ab` is the better of the two exactly when `1/√a + 1/√b > 1`.
-/

namespace ProductBound

open Finset BigOperators

/-- **No root above `ab`.**  If the weights are nonnegative and the occupancy numbers never exceed
`b`, then for `y > ab` every factor `y - a·s` is positive, so the weighted sum of products is
strictly positive and `y` cannot be a root. -/
theorem no_root_above {Ω : Type*} [Fintype Ω] {q : ℕ}
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∃ ω, 0 < w ω)
    (s : Ω → Fin q → ℕ) (a y : ℝ) (b : ℕ)
    (ha : 0 < a) (hs : ∀ ω k, s ω k ≤ b) (hy : a * b < y) :
    0 < ∑ ω, w ω * ∏ k, (y - a * (s ω k : ℝ)) := by
  classical
  have hfac : ∀ ω k, 0 < y - a * (s ω k : ℝ) := by
    intro ω k
    have h1 : (s ω k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hs ω k
    nlinarith [ha, hy, h1]
  have hprod : ∀ ω, 0 < ∏ k, (y - a * (s ω k : ℝ)) :=
    fun ω => Finset.prod_pos fun k _ => hfac ω k
  obtain ⟨ω₀, hω₀⟩ := hw1
  refine Finset.sum_pos' (fun ω _ => mul_nonneg (hw ω) (hprod ω).le) ⟨ω₀, Finset.mem_univ ω₀, ?_⟩
  exact mul_pos hω₀ (hprod ω₀)

/-- **The overshoot.**  `ab` exceeds the upper band edge by exactly `(√((a-1)(b-1)) - 1)²`.
Stated in the square-root coordinates `u = √(a-1)`, `v = √(b-1)`. -/
theorem edge_gap (u v : ℝ) :
    (u ^ 2 + 1) * (v ^ 2 + 1) - (u + v) ^ 2 = (u * v - 1) ^ 2 := by ring

/-- The gap is nonnegative, so `ab` is always at least the upper band edge: the bound is valid but
lossy, and lossless exactly when `√((a-1)(b-1)) = 1`. -/
theorem edge_gap_nonneg (u v : ℝ) :
    (u + v) ^ 2 ≤ (u ^ 2 + 1) * (v ^ 2 + 1) := by
  nlinarith [sq_nonneg (u * v - 1)]

/-- **The case `a = b = 2`.**  There `u = v = 1`, the gap `(uv - 1)²` vanishes, and `ab = 4` is
exactly the upper band edge.  Together with nonnegativity of the roots this proves the band. -/
theorem edge_gap_eq_zero_iff (u v : ℝ) :
    (u ^ 2 + 1) * (v ^ 2 + 1) = (u + v) ^ 2 ↔ u * v = 1 := by
  rw [← sub_eq_zero, edge_gap, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

/-- At `a = b = 2` the bound closes the upper edge exactly. -/
theorem edge_gap_two : ((1:ℝ) ^ 2 + 1) * ((1:ℝ) ^ 2 + 1) = ((1:ℝ) + 1) ^ 2 := by norm_num

/-! ## The `b = 2` reduction

At `b = 2` the profile compression collapses to a single variable: writing `n₂` for the number of
doubly-occupied blocks and `Ψ(u) = 𝔼 u^{n₂}`, one has `μ(y) = (y-a)^p Ψ(θ(y))` with
`θ(y) = 1 - a²/(y-a)²`.  Real-rootedness forces `Ψ` to be a product of independent Bernoulli
factors, and the extreme roots come out as `a(1 ± √π)` where `π` is the largest Bernoulli
parameter.

The band at `b = 2` is `[(√(a-1)-1)², (√(a-1)+1)²] = [a - 2√(a-1), a + 2√(a-1)]`, so both edges
reduce to the *same* inequality on `π`, namely `a√π ≤ 2√(a-1)`, i.e. `π ≤ 4(a-1)/a²`.  That the
two edges give one condition is the reflection of `SignReflection` seen on this side.
-/

/-- The `(a,2)`-biregular band edges in closed form: `(√(a-1) ± 1)² = a ± 2√(a-1)`. -/
theorem band_edge_eq {a : ℝ} (ha : 1 ≤ a) :
    (Real.sqrt (a - 1) + 1) ^ 2 = a + 2 * Real.sqrt (a - 1)
    ∧ (Real.sqrt (a - 1) - 1) ^ 2 = a - 2 * Real.sqrt (a - 1) := by
  have h : Real.sqrt (a - 1) ^ 2 = a - 1 := Real.sq_sqrt (by linarith)
  constructor <;> nlinarith [h]

/-- **The `b = 2` reduction.**  The upper edge, the lower edge, and the inequality
`π ≤ 4(a-1)/a²` are all the same condition.  The two edges coinciding is the reflection
`y ↦ 2a - y` seen through the substitution `θ`. -/
theorem band_iff_pi {a p : ℝ} (ha : 1 ≤ a) (ha0 : 0 < a) (hp : 0 ≤ p) :
    (a * (1 + Real.sqrt p) ≤ (Real.sqrt (a - 1) + 1) ^ 2 ↔ p ≤ 4 * (a - 1) / a ^ 2)
    ∧ ((Real.sqrt (a - 1) - 1) ^ 2 ≤ a * (1 - Real.sqrt p) ↔ p ≤ 4 * (a - 1) / a ^ 2) := by
  obtain ⟨hup, hlo⟩ := band_edge_eq ha
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hsn : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hr : Real.sqrt (a - 1) ^ 2 = a - 1 := Real.sq_sqrt (by linarith)
  have hrn : 0 ≤ Real.sqrt (a - 1) := Real.sqrt_nonneg _
  -- both edges reduce to `a √p ≤ 2 √(a-1)`
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have key : (a * Real.sqrt p ≤ 2 * Real.sqrt (a - 1)) ↔ p ≤ 4 * (a - 1) / a ^ 2 := by
    rw [le_div_iff₀ ha2]
    constructor
    · intro h
      have h2 := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ a * Real.sqrt p) h
      nlinarith [h2, hs, hr]
    · intro h
      by_contra hc
      push_neg at hc
      have h2 := mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (a - 1)) hc
      nlinarith [h2, hs, hr]
  have hexp : a * (1 + Real.sqrt p) = a + a * Real.sqrt p := by ring
  have hexp' : a * (1 - Real.sqrt p) = a - a * Real.sqrt p := by ring
  refine ⟨?_, ?_⟩
  · rw [hup, hexp]
    constructor <;> intro h
    · exact key.mp (by linarith)
    · linarith [key.mpr h]
  · rw [hlo, hexp']
    constructor <;> intro h
    · exact key.mp (by linarith)
    · linarith [key.mpr h]

/-! ### The weaker bound and what it would buy

`INEQ-2` asks for `π ≤ 4(a-1)/a² = (4/a)(1 - 1/a)`.  The strictly weaker `π ≤ 4/a` already gives a
bound better than both estimates currently available for projection families at `b = 2`: it beats
the Marchenko–Pastur edge `(√a + √2)²` for every `a`, and the product bound `ab = 2a` as soon as
`a ≥ 5`.  It falls short of the true edge by `2(√a - √(a-1)) ~ 1/√a`, so it is asymptotically
sharp.  The implication is recorded here so that a proof of the weaker inequality immediately
yields the corresponding theorem.
-/

/-- The weaker hypothesis `π ≤ 4/a` gives `λ_max ≤ a + 2√a`. -/
theorem weak_bound {a p : ℝ} (ha0 : 0 < a) (hp : 0 ≤ p) (h : p ≤ 4 / a) :
    a * (1 + Real.sqrt p) ≤ a + 2 * Real.sqrt a := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hle : Real.sqrt p ≤ 2 / Real.sqrt a := by
    rw [show (2:ℝ) / Real.sqrt a = Real.sqrt (4 / a) by
      rw [show (4:ℝ) / a = 2 ^ 2 / Real.sqrt a ^ 2 by rw [hsq]; norm_num,
        ← div_pow, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt h
  have : a * Real.sqrt p ≤ a * (2 / Real.sqrt a) := by
    exact mul_le_mul_of_nonneg_left hle ha0.le
  have hid : a * (2 / Real.sqrt a) = 2 * Real.sqrt a := by
    field_simp
    nlinarith [hsq, hsa]
  nlinarith [this, hid]

/-- `a + 2√a` is below the product bound `2a` exactly when `a > 4`. -/
theorem weak_beats_ab {a : ℝ} (ha : 4 < a) : a + 2 * Real.sqrt a < 2 * a := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  nlinarith [hsq, hsa]

/-- `a + 2√a` is below the Marchenko–Pastur edge `(√a + √2)²` for every `a > 0`. -/
theorem weak_beats_mp {a : ℝ} (ha : 0 < a) :
    a + 2 * Real.sqrt a < (Real.sqrt a + Real.sqrt 2) ^ 2 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 1 < Real.sqrt 2 := by
    nlinarith [h2, Real.sqrt_nonneg 2]
  nlinarith [hsq, h2, hsa, h2p]

/-! ### Comparison with the barrier bound of Xu, Xu and Zhu

For rank-`b` projections with `∑ P_k = aI`, normalising by `a` puts the family in the
Weaver form `∑ X_k = I`, `rank X_k ≤ b`, `ε = b/a`, and Theorem 1.9 of Xu–Xu–Zhu (2021)
gives `λ_max ≤ a(√(1 - ε/(b-1)) + √ε)²` whenever `ε ≤ (b-1)²/b`.  At `b = 2` that is

  `λ_max ≤ a + 2√(2a - 4)`,   valid for `a ≥ 4`.

The two lemmas below place it against the bounds of this section.  `xxz_le_ab` says it is
at least as good as `ab = 2a` everywhere it applies, with equality only at `a = 4` — so
`ab` is the better bound only where the barrier hypothesis fails, namely `a < 4`.
`target_le_xxz` says the target `a + 2√a` of `weak_bound` is in turn better than it for
`a > 4`, so proving that target would improve on the state of the art exactly there. -/

/-- The barrier bound `a + 2√(2a-4)` is at most the product bound `2a`, with equality
exactly at `a = 4`; the gap is `(a-4)²` under the square root comparison. -/
theorem xxz_le_ab {a : ℝ} (ha : 4 ≤ a) :
    a + 2 * Real.sqrt (2 * a - 4) ≤ 2 * a := by
  have h0 : (0:ℝ) ≤ 2 * a - 4 := by linarith
  have hs : Real.sqrt (2 * a - 4) ^ 2 = 2 * a - 4 := Real.sq_sqrt h0
  have hn : 0 ≤ Real.sqrt (2 * a - 4) := Real.sqrt_nonneg _
  nlinarith [hs, hn, sq_nonneg (a - 4), sq_nonneg (Real.sqrt (2 * a - 4) - 2)]

/-- Equality holds exactly at `a = 4`. -/
theorem xxz_eq_ab_iff {a : ℝ} (ha : 4 ≤ a) :
    a + 2 * Real.sqrt (2 * a - 4) = 2 * a ↔ a = 4 := by
  have h0 : (0:ℝ) ≤ 2 * a - 4 := by linarith
  have hs : Real.sqrt (2 * a - 4) ^ 2 = 2 * a - 4 := Real.sq_sqrt h0
  have hn : 0 ≤ Real.sqrt (2 * a - 4) := Real.sqrt_nonneg _
  constructor
  · intro h; nlinarith [hs, hn, sq_nonneg (a - 4)]
  · intro h; subst h; norm_num

/-- The target `a + 2√a` is at least as strong as the barrier bound for `a ≥ 4`. -/
theorem target_le_xxz {a : ℝ} (ha : 4 ≤ a) :
    a + 2 * Real.sqrt a ≤ a + 2 * Real.sqrt (2 * a - 4) := by
  have : Real.sqrt a ≤ Real.sqrt (2 * a - 4) := Real.sqrt_le_sqrt (by linarith)
  linarith

end ProductBound
