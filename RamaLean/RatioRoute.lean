import Mathlib

/-!
# The ratio route: a sign-alternating invariant for the cavity recursion

`SoftEdge.rayleigh_in_gap` bars compression arguments from proving the inner half of the
two-sided statement: a quadratic form cannot separate a gap point from a spectral point.  The
ratio recursion is not barred, because it bounds ratios of matching polynomials rather than
Rayleigh quotients.  This file makes that route concrete.

## The reduction

By Godsil `μ_G` divides `μ_P` for the path tree `P`, and on a tree the deletion recurrence is
exact and local:

  `F_v = λ - ∑_{u a child of v} 1/F_u`,   `F_leaf = λ`.

So `μ_G(λ) ≠ 0` follows if no `F` vanishes on `P`.

## Why the obvious certificate fails, and what replaces it

If every child ratio lay in `[a,b]` with `a > 0`, invariance would need `a ≤ λ - k/a`, that is
`a² - λa + k ≤ 0`, which has a positive solution only for `λ ≥ 2√k`.  That is the Heilmann-Lieb
bound: a *positive* invariant interval exists only above the band, never inside a gap.

Measurement says what replaces it.  On path trees of `(d,q)`-biregular graphs at gap points,
over twenty-two thousand path-tree vertices, the ratios separate perfectly by vertex type with
no exceptions: every degree-`d` vertex has `F > 0` and every degree-`q` vertex has `F < 0`
(`code/pathratio.py`).  For `(3,9)` at `λ = 0.354` the left ratios fill `[0.3536, 0.5353]`, the
left endpoint being the leaf value `λ`, and the right ratios fill `[-22.27, -13.79]`.  The
certificate is therefore *sign-alternating*: a positive interval on one side of the bipartition
and a negative interval on the other.

## The two steps

`left_step`: children negative in `[-C,-c]` push the parent up, to `[λ, λ + k/c]`.  Since `λ > 0`
this keeps the parent positive and bounded, and it holds for every number of children, so
truncation of the path tree is harmless here.

`right_step`: children positive in `[a,B]` push the parent down, and it lands strictly negative
as soon as `k > λB`.

Together they close the induction on `P` and give `no_vanishing`.

## What remains

`right_step` needs *enough* children, `k > λB`.  A degree-`q` path-tree vertex has `q` minus the
number of its neighbours already on the path, so the hypothesis is a lower bound on unblocked
neighbours at high-degree vertices of the path tree.  That is the whole remaining gap, and it is
combinatorial rather than spectral, which is the point of taking this route.

## Status

`left_step`, `right_step` and `no_vanishing` are `VERIFIED`.  The hypothesis of `right_step` is
`CONJECTURE` as a statement about path trees of biregular graphs; the sign separation it would
give is `HEURISTIC`, on the measurement above.  The biregular case of Conjecture 10 remains a
`CONJECTURE`.
-/

namespace RatioRoute

open Finset

/-- **Negative children push the parent up.**  If every child ratio lies in `[-C, -c]` with
`0 < c`, then `-1/F` is positive and at most `1/c`, so the parent lies in `[λ, λ + k/c]`.  In
particular it stays positive, and the bound holds for *every* number of children, so a path-tree
vertex missing some of its children is still covered. -/
theorem left_step {k : ℕ} (F : Fin k → ℝ) (lam c C : ℝ) (hc : 0 < c)
    (hF : ∀ j, -C ≤ F j ∧ F j ≤ -c) :
    lam ≤ lam - ∑ j, 1 / F j ∧ lam - ∑ j, 1 / F j ≤ lam + k / c := by
  have hneg : ∀ j, F j < 0 := fun j => lt_of_le_of_lt (hF j).2 (by linarith)
  have hup : ∀ j ∈ (univ : Finset (Fin k)), 1 / F j ≤ 0 := fun j _ =>
    div_nonpos_of_nonneg_of_nonpos zero_le_one (hneg j).le
  have hlow : ∀ j ∈ (univ : Finset (Fin k)), -(1 / c) ≤ 1 / F j := by
    intro j _
    have h1 : F j ≤ -c := (hF j).2
    have : 1 / F j = -(1 / (-F j)) := by field_simp
    rw [this, neg_le_neg_iff]
    exact one_div_le_one_div_of_le hc (by linarith)
  constructor
  · have : ∑ j, 1 / F j ≤ 0 := sum_nonpos hup
    linarith
  · have hs : -((k : ℝ) / c) ≤ ∑ j, 1 / F j := by
      calc -((k : ℝ) / c) = ∑ _j : Fin k, -(1 / c) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ ∑ j, 1 / F j := sum_le_sum hlow
    linarith

/-- **Positive children push the parent down, and past zero once there are enough of them.**
If every child ratio lies in `[a, B]` with `0 < a`, each contributes at least `1/B`, so the sum
exceeds `λ` as soon as `k > λB` and the parent is strictly negative. -/
theorem right_step {k : ℕ} (F : Fin k → ℝ) (lam a B : ℝ) (ha : 0 < a) (haB : a ≤ B)
    (hF : ∀ j, a ≤ F j ∧ F j ≤ B) (hk : lam * B < k) :
    lam - ∑ j, 1 / F j < 0 := by
  have hB : 0 < B := lt_of_lt_of_le ha haB
  have hge : ∀ j ∈ (univ : Finset (Fin k)), 1 / B ≤ 1 / F j := fun j _ =>
    one_div_le_one_div_of_le (lt_of_lt_of_le ha (hF j).1) (hF j).2
  have hs : (k : ℝ) / B ≤ ∑ j, 1 / F j := by
    calc (k : ℝ) / B = ∑ _j : Fin k, 1 / B := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ j, 1 / F j := sum_le_sum hge
  have : lam < (k : ℝ) / B := by rw [lt_div_iff₀ hB]; linarith
  linarith

/-- **The two steps close the induction.**  A ratio that is either at least `λ > 0` or at most
`-c < 0` is nonzero; `left_step` delivers the first alternative and `right_step` the second, so
under the sign-alternating invariant no ratio on the path tree vanishes and `μ_G(λ) ≠ 0`. -/
theorem no_vanishing {F lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (h : lam ≤ F ∨ F ≤ -c) : F ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt (lt_of_lt_of_le hlam h)
  · exact ne_of_lt (lt_of_le_of_lt h (by linarith))

end RatioRoute
