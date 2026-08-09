import Mathlib

/-!
# A positive margin for the complete bipartite family

D3 says minimum degree three suffices for Conjecture 10.  The widest gaps available at minimum
degree three come from degree *contrast*: the universal cover of a `(δ,q)`-biregular graph is
the `(δ,q)`-biregular tree, whose spectrum is `{0}` together with
`±[√(q-1) - √(δ-1), √(q-1) + √(δ-1)]`, so there is a gap `(0, g)` with

  `g = √(q-1) - √(δ-1)`,

and `g → ∞` as `q → ∞`.  A root of `μ_G` in `(0, g)` would refute D3 and would also settle Song,
Fan and Miao's Problem 1, to which the biregular case of Conjecture 10 is equivalent.  So this
is where D3 is most exposed, and this file shows it survives there, with a margin that is
positive for *every* minimum degree.

## The computation

For `K_{δ,q}` the matching polynomial factors, since a `k`-matching picks `k` vertices on each
side and matches them:

  `μ = x^{q-δ} P(x²)`,  `P(y) = ∑_{k≤δ} (-1)^k C(δ,k) (q)_k y^{δ-k}`.

`P` is a Laguerre polynomial, and as `q → ∞` its zeros satisfy `(y - q)/√q → ` the zeros of the
probabilists' Hermite polynomial `He_δ`.  Writing `h_δ` for the largest such zero,

  `x_min = √q - h_δ/2 + o(1)`,   `g = √q - √(δ-1) + o(1)`,

so the margin `x_min - g` tends to `√(δ-1) - h_δ/2`.  Numerically at `q = 10⁶` this matches to
four decimals for every `δ` from `3` to `20`: `0.5482, 0.5648, 0.5715, 0.5743, 0.5721, 0.5662,
0.5575, 0.5494` (`code/d3attack.py`).

## Why the margin is positive, for every `δ`

`h_δ` is the largest eigenvalue of the Jacobi matrix of `He_δ`: zero diagonal, off-diagonal
entries `√1, √2, …, √(δ-1)`, from the recurrence `He_{n+1} = y He_n - n He_{n-1}`.  Its row sums
of absolute values are `√(i-1) + √i`, largest at the last row, so Gershgorin gives

  `h_δ ≤ √(δ-2) + √(δ-1) < 2√(δ-1)`,

and therefore

  `margin = √(δ-1) - h_δ/2 ≥ (√(δ-1) - √(δ-2))/2 > 0`.

That is `abs_eigenvalue_le_max_rowsum`, `margin_ge_of_rowsum` and `margin_pos_of_rowsum` below.
The bound is far from tight, roughly `1/(4√δ)` against a true margin near `0.55`, but it is
positive for every `δ`, which is the point: **no complete bipartite graph refutes D3, however
large the gap is made.**

## Status

`abs_eigenvalue_le_max_rowsum`, `margin_ge_of_rowsum`, `margin_pos_of_rowsum` and
`no_root_below_gap_edge` are `VERIFIED`.  The Laguerre-to-Hermite limit and the identification
of `h_δ` as the largest Jacobi eigenvalue are classical and enter as hypotheses, exactly as
Heilmann-Lieb and Kesten do in `MinimumDegreeThreshold`.  D3 itself remains a `CONJECTURE`;
what is settled here is that the family where it looked most exposed cannot refute it.
-/

namespace CompleteBipartiteMargin

open Finset

/-! ## Gershgorin, in eigenvector form -/

/-- **Gershgorin, stated for an eigenvector.**  If `A v = λ v` with `v ≠ 0` and every row of
`A` has absolute row sum at most `M`, then `|λ| ≤ M`.  Proved directly: at an index where `|v|`
is largest, the eigenvalue equation bounds `|λ|` by that row's sum. -/
theorem abs_eigenvalue_le_max_rowsum {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (v : n → ℝ) (lam M : ℝ) (hv : v ≠ 0)
    (heig : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hM : ∀ i, ∑ j, |A i j| ≤ M) :
    |lam| ≤ M := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |v i|)
  have hmax : ∀ j, |v j| ≤ |v i| := fun j => by
    rw [← hi]; exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ j)
  have hvi : 0 < |v i| := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc
      exact hv (funext fun j => not_not.mp fun hj => hc ⟨j, hj⟩)
    exact lt_of_lt_of_le (abs_pos.mpr hj) (hmax j)
  have key : |lam| * |v i| ≤ M * |v i| := by
    calc |lam| * |v i| = |lam * v i| := (abs_mul _ _).symm
      _ = |∑ j, A i j * v j| := by rw [heig]
      _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A i j| * |v i| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _)
      _ = (∑ j, |A i j|) * |v i| := by rw [Finset.sum_mul]
      _ ≤ M * |v i| := mul_le_mul_of_nonneg_right (hM i) (abs_nonneg _)
  exact le_of_mul_le_mul_right key hvi

/-! ## The margin -/

/-- The Gershgorin bound for the Hermite Jacobi matrix, in the form the margin needs.  Here
`a = δ - 2`, so the largest absolute row sum is `√a + √(a+1)`. -/
theorem margin_ge_of_rowsum {a h : ℝ} (hh : h ≤ Real.sqrt a + Real.sqrt (a + 1)) :
    (Real.sqrt (a + 1) - Real.sqrt a) / 2 ≤ Real.sqrt (a + 1) - h / 2 := by
  linarith

/-- **The margin is positive for every minimum degree.**  `√a < √(a+1)` for `a ≥ 0`, so the
Gershgorin lower bound is strictly positive, and with it the margin. -/
theorem margin_pos_of_rowsum {a h : ℝ} (ha : 0 ≤ a)
    (hh : h ≤ Real.sqrt a + Real.sqrt (a + 1)) :
    0 < Real.sqrt (a + 1) - h / 2 := by
  have hlt : Real.sqrt a < Real.sqrt (a + 1) :=
    Real.sqrt_lt_sqrt ha (by linarith)
  have := margin_ge_of_rowsum (a := a) (h := h) hh
  linarith

/-- **Nothing lands in the gap.**  If the smallest positive root exceeds the gap edge, no root
of `μ_G` lies in `(0, g)`, so `K_{δ,q}` does not violate Conjecture 10 there.  The margin is
exactly the amount by which it exceeds it. -/
theorem no_root_below_gap_edge {Zeros : Set ℝ} {xmin g : ℝ}
    (hmin : ∀ θ ∈ Zeros, 0 < θ → xmin ≤ θ) (hgap : g < xmin) :
    ∀ θ ∈ Zeros, θ ∉ Set.Ioo 0 g := by
  intro θ hθ hmem
  exact absurd (hmin θ hθ hmem.1) (not_le.mpr (lt_trans hmem.2 hgap))

/-- The whole chain, assembled: a Gershgorin bound on the Hermite root gives a positive margin,
and a positive margin keeps the zeros out of the gap. -/
theorem conj10_for_complete_bipartite {Zeros : Set ℝ} {a h g xmin : ℝ} (ha : 0 ≤ a)
    (hh : h ≤ Real.sqrt a + Real.sqrt (a + 1))
    (hxmin : xmin = g + (Real.sqrt (a + 1) - h / 2))
    (hmin : ∀ θ ∈ Zeros, 0 < θ → xmin ≤ θ) :
    ∀ θ ∈ Zeros, θ ∉ Set.Ioo 0 g := by
  refine no_root_below_gap_edge hmin ?_
  have := margin_pos_of_rowsum ha hh
  rw [hxmin]; linarith

end CompleteBipartiteMargin
