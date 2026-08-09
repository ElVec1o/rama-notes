import Mathlib

/-!
# The threshold is the minimum degree, and it sits at three

Conjecture 10 is false, and three hypotheses were tried to repair it.  Minimum degree two
failed, bounded maximum degree failed, and 2-connectedness (C1) failed to the 2-cut engine of
`SeparationOrder`.  A `k`-cut search then found nothing at `k = 3, 4, 5`, which suggested
3-connectedness, C2.

C2 is the wrong statement of the right idea, because it is confounded.  A graph of vertex
connectivity `κ` has minimum degree at least `κ`, so demanding 3-connectedness silently demands
minimum degree three, and every counterexample ever found has minimum degree at most two:
Hall's has leaves, the `31`-vertex graph has degree-2 vertices, and so do all three graphs that
refuted C1.

The two readings were separated by running the *same* engine with the *only* change being the
minimum degree.  Two hubs and `p` branches attached to both is the construction that killed C1;
with branches of minimum degree three (ladders, prisms, `K_{3,q}` blocks) it produces `102`
graphs of minimum degree three and vertex connectivity **two**, a separating pair in every one,
of which `77` have a gap of width at least `0.05` and several have gaps wider than `2.9`.  For
comparison the three C1 counterexamples sit in gaps of width `0.066` to `0.148`.  Not one root
lands in a gap (`code/mindeg3.py`).

  **D3.**  Every finite graph of minimum degree at least three satisfies
  `Zeros(μ_G) ⊆ spec(T_G)`.

D3 implies C2, since `κ ≥ 3` forces `δ ≥ 3`, and it is the weaker and more natural hypothesis:
it is local, where connectivity is global.  Minimum degree two is `FALSE`, by the `31`-vertex
graph.  So if D3 holds the threshold is *exactly* three, which is `threshold_is_three`.

## What is proved here

`conj10_of_regular`: **Conjecture 10 is true for regular graphs**, and for a reason that costs
nothing.  Heilmann and Lieb put every root of `μ_G` in `[-2√(Δ-1), 2√(Δ-1)]`; Kesten computes
the spectrum of the `d`-regular tree as exactly `[-2√(d-1), 2√(d-1)]`; and for a `d`-regular
graph the universal cover *is* the `d`-regular tree.  The two intervals coincide, so there is
nothing to violate.  Both classical facts enter as hypotheses, since neither is proved here;
what is proved is that they close the regular case.

This is worth recording because it locates the whole content of the conjecture in the
irregular case, and it is consistent with the measurements: every regular graph tested has
*no gap at all* in `spec(T)` (`code/gapscale.py`).

`threshold_is_three`: given D3 and a counterexample of minimum degree two, three is the least
sufficient minimum-degree threshold.  The hypothesis is discharged by the `31`-vertex graph.

## Status

`conj10_of_regular` and `threshold_is_three` are `VERIFIED`.  `D3` is a `CONJECTURE`, on
evidence that is out of sample and, unlike the evidence for C1 and C2, deliberately filtered so
that a graph with no gap cannot pad the negative.  It has not yet been attacked as hard as C1
was, and C1 lasted three hours.
-/

namespace MinimumDegreeThreshold

/-! ## The regular case is trivial -/

/-- **Conjecture 10 holds for regular graphs.**  If every root lies in `[-R, R]` and the
spectrum of the universal cover *is* `[-R, R]`, there is nothing to violate.  For a `d`-regular
graph both hold with `R = 2√(d-1)`, the first by Heilmann and Lieb and the second by Kesten,
and the universal cover is the `d`-regular tree.  Both classical inputs are hypotheses. -/
theorem conj10_of_regular {Zeros Spec : Set ℝ} {R : ℝ}
    (hHL : ∀ θ ∈ Zeros, |θ| ≤ R)
    (hKesten : Spec = Set.Icc (-R) R) :
    Zeros ⊆ Spec := by
  intro θ hθ
  rw [hKesten, Set.mem_Icc]
  exact abs_le.mp (hHL θ hθ)

/-- The same, with the radius written out: `R = 2√(d-1)` for a `d`-regular graph. -/
theorem conj10_of_regular_explicit {Zeros Spec : Set ℝ} (d : ℕ)
    (hHL : ∀ θ ∈ Zeros, |θ| ≤ 2 * Real.sqrt ((d : ℝ) - 1))
    (hKesten : Spec = Set.Icc (-(2 * Real.sqrt ((d : ℝ) - 1)))
                              (2 * Real.sqrt ((d : ℝ) - 1))) :
    Zeros ⊆ Spec :=
  conj10_of_regular hHL hKesten

/-! ## The threshold -/

variable {Γ : Type*}

/-- **D3.**  Minimum degree three suffices.  Stated over an abstract carrier so that the
statement does not depend on a particular encoding of graphs. -/
def D3 (MinDeg : Γ → ℕ) (Violates : Γ → Prop) : Prop :=
  ∀ G, 3 ≤ MinDeg G → ¬ Violates G

/-- Minimum degree two does **not** suffice: the `31`-vertex graph with degrees in `{2,3}`
carries a root of `μ_G` in a gap of `spec(T)`.  This is the hypothesis discharged by that
graph, and it is what makes the threshold sharp rather than merely sufficient. -/
def MinDegTwoFails (MinDeg : Γ → ℕ) (Violates : Γ → Prop) : Prop :=
  ∃ G, 2 ≤ MinDeg G ∧ Violates G

/-- **The threshold is exactly three.**  If minimum degree three suffices and some graph of
minimum degree two violates the conjecture, then three is the *least* sufficient
minimum-degree threshold: no smaller bound works, and three does. -/
theorem threshold_is_three {MinDeg : Γ → ℕ} {Violates : Γ → Prop}
    (hD3 : D3 MinDeg Violates) (hcex : MinDegTwoFails MinDeg Violates) :
    IsLeast {k | ∀ G, k ≤ MinDeg G → ¬ Violates G} 3 := by
  refine ⟨hD3, ?_⟩
  rintro k hk
  obtain ⟨G, hdeg, hv⟩ := hcex
  by_contra hlt
  have hk2 : k ≤ 2 := by omega
  exact hk G (le_trans hk2 hdeg) hv

/-- D3 implies C2, since vertex connectivity `κ` forces minimum degree at least `κ`.  So the
3-connected statement is a corollary of the minimum-degree one, and not an independent fact. -/
theorem C2_of_D3 {MinDeg Conn : Γ → ℕ} {Violates : Γ → Prop}
    (hmono : ∀ G, Conn G ≤ MinDeg G) (hD3 : D3 MinDeg Violates) :
    ∀ G, 3 ≤ Conn G → ¬ Violates G :=
  fun G h => hD3 G (le_trans h (hmono G))

end MinimumDegreeThreshold
