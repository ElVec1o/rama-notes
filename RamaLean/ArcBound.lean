import Mathlib

/-!
# Long cycles carry no second-order information

The counting step behind the four-block ceiling. Expanding a cyclic trace
`tr(A_{k₁} ⋯ A_{k_m})` to second order, the terms with two `D`s at positions `p < p'` have
coefficient

  `1_{u ∈ I₁} 1_{v ∈ I₂} + 1_{v ∈ I₁} 1_{u ∈ I₂}`

at the coordinate `z^{uv}_{k_p k_{p'}}`, where `I₁` and `I₂` are the intersections of the blocks
along the two arcs between the positions. For that to be nonzero one needs a point lying in every
block of an arc.

In a tight family `∑ₖ Pₖ = a·1`, so every point lies in exactly `a` blocks. If `u` lies in every
block of arc 1, and the block at position `p` or `p'` that contains `u` is not on that arc, then arc
1 has at most `a - 1` blocks; likewise for `v` and arc 2. Since the word has
`m = 2 + |arc₁| + |arc₂|` blocks,

  **`m ≤ 2a`, and a cyclic word longer than that has an identically vanishing second-order row.**

At `a = 2` the bound is `4`, which is the four-block ceiling outright: nothing beyond four blocks can
contribute. At `a ≥ 3` the bound is weaker than the observed ceiling and the remaining gap is a
linear dependence rather than a vanishing, which is recorded as open in `code/ceiling.py`.

## What is formalised

`card_le_of_mem_all` is the pigeonhole in the form used: a family of distinct blocks all containing a
given point, together with one further block containing it and not among them, has at most `a - 1`
members when the point lies in exactly `a` blocks. `arc_bound` assembles the two arcs into `m ≤ 2a`.
Both are statements about finite sets and carry no analysis.

The expansion that produces the coefficient is not formalised: it needs the mixed characteristic
polynomial, which Mathlib does not carry. That is the same blocker recorded throughout this
subtree.

## Status

`card_le_of_mem_all` and `arc_bound` are `VERIFIED`.
-/

namespace ArcBound

open Finset

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
/-- **The pigeonhole.**  If exactly `a` blocks contain the point, `arc` is a set of blocks all
containing it, and `w` is a further block containing it but outside `arc`, then `arc` has at most
`a - 1` members. -/
theorem card_le_of_mem_all (containing arc : Finset κ) (w : κ) (a : ℕ)
    (hcard : containing.card = a) (harc : arc ⊆ containing)
    (hw : w ∈ containing) (hwn : w ∉ arc) :
    arc.card ≤ a - 1 := by
  have h : insert w arc ⊆ containing := insert_subset hw harc
  have hc : (insert w arc).card = arc.card + 1 := card_insert_of_notMem hwn
  have := card_le_card h
  omega

omit [Fintype κ] in
/-- **The arc bound.**  A cyclic word contributing to the second order splits into two blocks at the
distinguished positions and two arcs, each of which is bounded by the pigeonhole above. So the word
has at most `2a` blocks, and any longer word contributes nothing. -/
theorem arc_bound (cu cv arc₁ arc₂ : Finset κ) (x y : κ) (a : ℕ)
    (hu : cu.card = a) (hv : cv.card = a)
    (h₁ : arc₁ ⊆ cu) (h₂ : arc₂ ⊆ cv)
    (hx : x ∈ cu) (hxn : x ∉ arc₁) (hy : y ∈ cv) (hyn : y ∉ arc₂) :
    2 + arc₁.card + arc₂.card ≤ 2 * a := by
  have b₁ := card_le_of_mem_all cu arc₁ x a hu h₁ hx hxn
  have b₂ := card_le_of_mem_all cv arc₂ y a hv h₂ hy hyn
  have ha : 0 < a := by rw [← hu]; exact Finset.card_pos.mpr ⟨x, hx⟩
  omega

end ArcBound
