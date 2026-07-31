import Mathlib

/-!
# The positivity behind the `E₄` identity

The extremal computation for rank-two projection families rests on one inequality. Writing
`g_{ij} = tr(P_i P_j)` and `h_{ij} = tr((P_i P_j)²)`, the identity

  `E₄ = q⁴/16 - q³/4 + q/2 + ¼ Σ_{i≠j} (g_{ij}² - h_{ij})`

has all its summands nonnegative, and that is what pins `E₄` to its minimum. The reason is that
`X = P_j P_i P_j` is positive semidefinite with `tr((P_i P_j)^m) = tr(X^m)` for every `m ≥ 1`, so
`g_{ij}² - h_{ij} = (tr X)² - tr X²`, and for a positive semidefinite `X` with eigenvalues
`λ_1, …, λ_n ≥ 0` this is

  `(Σ λ_r)² - Σ λ_r² = 2 Σ_{r < s} λ_r λ_s ≥ 0`.

That last step is the content, and it is what is formalized here: `sq_sum_sub_sum_sq` gives the
identity over any finite index set, and `sum_sq_le_sq_sum` the inequality under nonnegativity.

Scope: the passage from `X` to its eigenvalue list — that a real positive semidefinite matrix has
nonnegative eigenvalues summing to its trace, with `tr X² = Σ λ_r²` — is standard spectral theory
(`Matrix.PosSemidef.eigenvalues_nonneg`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`) and is not
reproved here. `trace_sq_le_sq_trace` states the matrix corollary with those two spectral facts as
explicit hypotheses, so the logical dependence is visible rather than hidden.
-/

namespace TracePSD

open Finset BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- **The exact difference.**  Over any finite index set, the square of the sum minus the sum of
squares is the sum of all off-diagonal products. -/
theorem sq_sum_sub_sum_sq (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
  have hsplit : ∀ i ∈ s, ∑ j ∈ s, f i * f j = f i ^ 2 + ∑ j ∈ s.erase i, f i * f j := by
    intro i hi
    rw [← Finset.sum_erase_add s _ hi]
    ring
  calc (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, f i * f j) - ∑ i ∈ s, f i ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
    _ = (∑ i ∈ s, (f i ^ 2 + ∑ j ∈ s.erase i, f i * f j)) - ∑ i ∈ s, f i ^ 2 := by
        rw [Finset.sum_congr rfl hsplit]
    _ = ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
        rw [Finset.sum_add_distrib]; ring

/-- **The inequality.**  For nonnegative reals the sum of squares never exceeds the square of the
sum, since by `sq_sum_sub_sum_sq` the gap is a sum of products of nonnegative numbers. -/
theorem sum_sq_le_sq_sum {s : Finset ι} {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hgap : 0 ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j :=
    Finset.sum_nonneg fun i hi =>
      Finset.sum_nonneg fun j hj =>
        mul_nonneg (hf i hi) (hf j (Finset.mem_of_mem_erase hj))
  have := sq_sum_sub_sum_sq s f
  linarith [hgap, this]

/-- **The matrix corollary.**  For a positive semidefinite `X`, `tr(X²) ≤ (tr X)²`.

The two spectral inputs are hypotheses rather than reproved: `heig` that the eigenvalues are
nonnegative (`Matrix.PosSemidef.eigenvalues_nonneg`), `htr` that the trace is their sum
(`Matrix.IsHermitian.trace_eq_sum_eigenvalues`), and `htr2` that the trace of the square is the sum
of their squares. Stated this way the dependence on standard spectral theory is explicit. -/
theorem trace_sq_le_sq_trace {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} {lam : n → ℝ}
    (heig : ∀ i, 0 ≤ lam i)
    (htr : X.trace = ∑ i, lam i)
    (htr2 : (X * X).trace = ∑ i, (lam i) ^ 2) :
    (X * X).trace ≤ X.trace ^ 2 := by
  rw [htr, htr2]
  exact sum_sq_le_sq_sum fun i _ => heig i

/-- The form in which the `E₄` computation consumes it: `g² - h ≥ 0`. -/
theorem g_sq_sub_h_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} {lam : n → ℝ} {g h : ℝ}
    (heig : ∀ i, 0 ≤ lam i)
    (hg : g = ∑ i, lam i) (hh : h = ∑ i, (lam i) ^ 2) :
    0 ≤ g ^ 2 - h := by
  rw [hg, hh]
  have := sum_sq_le_sq_sum (s := (Finset.univ : Finset n)) (f := lam) fun i _ => heig i
  linarith

end TracePSD
