import Mathlib

/-!
# The cokernel of the order-four map, and when it is one-dimensional

Order four of the deformation is solvable when the obstruction lies in the image of

  `L_D : Y ↦ (2 ∑ₖ σₖ(j) (D_k Y_k)_{jj})_j`.

`OrderFour` shows the image lies in the trace-zero hyperplane and the obstruction lies there too,
so what remains is whether the image *fills* it, that is whether the cokernel is spanned by
`(1, …, 1)`. This file is the reason it usually is.

## The condition

A vector `w` annihilates the image exactly when, for every pair of indices `i, j` and every pair of
blocks `k, l` separating them,

  `(w i - w j) * (σ_k(i) D_k(i,j) - σ_l(i) D_l(i,j)) = 0`.

So `w i = w j` as soon as two separating blocks disagree at `(i,j)`. Join `i` to `j` whenever they
do; then `w` is constant on each component, and

  `rank L_D = n - (number of components)`.

In particular the cokernel is one-dimensional, and order four is solvable, exactly when that graph
is connected. Checked against the computed rank on 32 directions across two families, agreeing in
every case including the degenerate one where the graph is empty and the rank collapses to 1
(`code/tangentcone.py`).

`sep_forces_eq` is the scalar step and `const_of_adj_eq` the passage from edges to components; the
two together are the argument.

## Status

`sep_forces_eq` and `const_of_adj_eq` are `VERIFIED`. That the graph is connected for a given
direction is a property of that direction, checked per case and not claimed in general; the cross
basis directions are exactly the case where it fails.
-/

namespace CokernelRank

variable {V : Type*}

/-- **The scalar step.**  Two blocks separating `i` from `j` and disagreeing there force `w` to
agree there.  This is the whole content of the cokernel condition at one pair. -/
theorem sep_forces_eq (wi wj a b : ℝ) (h : (wi - wj) * (a - b) = 0) (hab : a ≠ b) : wi = wj := by
  rcases mul_eq_zero.mp h with h1 | h2
  · linarith
  · exact absurd (sub_eq_zero.mp h2) hab

/-- **From edges to components.**  A function agreeing across every edge of a preconnected graph
is constant.  Applied to the graph that joins `i` to `j` when two separating blocks disagree, this
says the cokernel consists of the constants alone. -/
theorem const_of_adj_eq {G : SimpleGraph V} (hG : G.Preconnected) (f : V → ℝ)
    (h : ∀ u v, G.Adj u v → f u = f v) : ∀ u v, f u = f v := by
  intro u v
  obtain ⟨p⟩ := hG u v
  induction p with
  | nil => rfl
  | cons hadj q ih => exact (h _ _ hadj).trans ih

/-- The conclusion in the form it is used: if the separation graph is preconnected then every
annihilator of the image is constant, so the cokernel is at most one-dimensional and the image
contains the whole trace-zero hyperplane. -/
theorem cokernel_const {G : SimpleGraph V} (hG : G.Preconnected) (w : V → ℝ)
    (hsep : ∀ u v, G.Adj u v → ∃ a b : ℝ, (w u - w v) * (a - b) = 0 ∧ a ≠ b) :
    ∀ u v, w u = w v := by
  refine const_of_adj_eq hG w fun u v huv => ?_
  obtain ⟨a, b, hzero, hne⟩ := hsep u v huv
  exact sep_forces_eq (w u) (w v) a b hzero hne

end CokernelRank
