import Mathlib

/-!
# Cover counts: `M = |E| d` and `p₂ = P d`

The last step of paper 4's `prop:top` left by hand was the identification of the two
deterministic quantities of a `d`-sheeted cover `H` of `G`:

  `|E(H)| = |E(G)| · d`,        `p₂(H) = P · d`,   `P = ∑_v C(deg v, 2)`,

`p₂` being the number of `2`-paths, i.e. of adjacent edge pairs.  Both are instances of
one fact, and neither needs the covering structure itself — only that the vertex map has
all fibres of size `d` and preserves degrees, which is what a cover gives.

`sum_over_fibers` is that fact: any quantity accumulated over vertices as a function of
the degree is multiplied by exactly `d`.  Taking `φ = id` gives `∑_w deg w = d ∑_v deg v`,
hence `|E(H)| = d |E(G)|` after halving; taking `φ = (· .choose 2)` gives `p₂(H) = P d`.
Both are corollaries below.

With this, the only ingredient of `prop:top` still outside Lean is the degree bookkeeping
that decides which inclusion–exclusion terms of `ConflictIE.mCount_eq_ie` can reach order
`d^{k-1}`.
-/

namespace CoverCounts

open Finset

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]

/-- **Fibre counting.**  If every fibre of `π` has size `d`, then summing any function of
`π w` over `W` multiplies the corresponding sum over `V` by `d`. -/
theorem sum_over_fibers (π : W → V) (d : ℕ)
    (hfib : ∀ v, (univ.filter (fun w => π w = v)).card = d) (F : V → ℕ) :
    ∑ w, F (π w) = d * ∑ v, F v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := π) (fun w _ => mem_univ (π w))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]),
    Finset.sum_const, hfib v, smul_eq_mul]

/-- The degree sum of a cover is `d` times that of the base. -/
theorem degree_sum (π : W → V) (d : ℕ)
    (hfib : ∀ v, (univ.filter (fun w => π w = v)).card = d)
    (deg : V → ℕ) (degW : W → ℕ) (hdeg : ∀ w, degW w = deg (π w)) :
    ∑ w, degW w = d * ∑ v, deg v := by
  rw [Finset.sum_congr rfl fun w _ => hdeg w]
  exact sum_over_fibers π d hfib deg

/-- **`M = |E| d`.**  Since the degree sum is twice the edge count on both sides, the
cover has `d` times as many edges. -/
theorem edge_count (π : W → V) (d M E : ℕ)
    (hfib : ∀ v, (univ.filter (fun w => π w = v)).card = d)
    (deg : V → ℕ) (degW : W → ℕ) (hdeg : ∀ w, degW w = deg (π w))
    (hE : ∑ v, deg v = 2 * E) (hM : ∑ w, degW w = 2 * M) :
    M = E * d := by
  have h := degree_sum π d hfib deg degW hdeg
  rw [hM, hE] at h
  have h2 : 2 * M = 2 * (E * d) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

/-- **`p₂ = P d`.**  The number of `2`-paths, `∑_v C(deg v, 2)`, is also multiplied by
exactly `d`. -/
theorem twoPath_count (π : W → V) (d : ℕ)
    (hfib : ∀ v, (univ.filter (fun w => π w = v)).card = d)
    (deg : V → ℕ) (degW : W → ℕ) (hdeg : ∀ w, degW w = deg (π w)) :
    (∑ w, (degW w).choose 2) = d * ∑ v, (deg v).choose 2 := by
  rw [Finset.sum_congr rfl fun w _ => by rw [hdeg w]]
  exact sum_over_fibers π d hfib (fun v => (deg v).choose 2)

/-- The two counts together, in the form paper 4 uses them: `M = E d` and `p₂ = P d`. -/
theorem cover_counts (π : W → V) (d M E : ℕ)
    (hfib : ∀ v, (univ.filter (fun w => π w = v)).card = d)
    (deg : V → ℕ) (degW : W → ℕ) (hdeg : ∀ w, degW w = deg (π w))
    (hE : ∑ v, deg v = 2 * E) (hM : ∑ w, degW w = 2 * M) :
    M = E * d ∧ (∑ w, (degW w).choose 2) = (∑ v, (deg v).choose 2) * d := by
  refine ⟨edge_count π d M E hfib deg degW hdeg hE hM, ?_⟩
  rw [twoPath_count π d hfib deg degW hdeg, Nat.mul_comm]

end CoverCounts
