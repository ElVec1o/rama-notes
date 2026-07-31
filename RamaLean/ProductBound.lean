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

end ProductBound
