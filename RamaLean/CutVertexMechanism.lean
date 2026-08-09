import Mathlib

/-!
# The cut vertex is one mechanism, not the mechanism

Every counterexample to Conjecture 10 known before this file was built the same way: a cut vertex `v` whose
removal leaves `p` isomorphic branches `H`, so that the vertex-deletion recurrence factors the
matching polynomial and a root can be placed by tuning `p` and `H`.  This file isolates that
factorisation, which is the engine, and records what it needs.

## The factorisation

Deleting `v` leaves `p` disjoint copies of `H`, and deleting `v` together with one neighbour
leaves one copy of `H - v` and `p - 1` copies of `H`.  The recurrence
`μ_G = X μ_{G-v} - ∑_{u ∼ v} μ_{G-v-u}` therefore gives

  `μ_G = X μ_H^p - p μ_{H-v} μ_H^{p-1} = μ_H^{p-1} (X μ_H - p μ_{H-v})`,

and every counterexample takes its root from the last factor.  That is `branch_factor`.

**This requires a separation.**  The step "deleting `v` leaves `p` disjoint copies" is exactly
the statement that `v` separates `G`, and for `p ≥ 2` that is what a cut vertex is.  In a
2-connected graph no *vertex* has this property, so this particular factorisation is
unavailable.  The inference originally drawn from that, recorded and refuted below, was that
the construction then has nothing to tune.  It has: deleting a separating *pair* does the same
job.

## The hypothesis this suggested, and its refutation

  **C1.**  Every 2-connected finite graph satisfies `Zeros(μ_G) ⊆ spec(T_G)`.

C1 was frozen on the strength of the factorisation below, and on evidence gathered afterwards:
twenty-six 2-connected graphs with a cycle skeleton produced no root in any gap
(`code/cycle_family.py`); every counterexample in hand had cut vertices, fifteen in the
`31`-vertex graph and eleven in Hall's; and closing those graphs up with a ring of edges
returned the root to `spec(T)` in all five closures tested, exactly when the last cut vertex
went (`code/twoconnected.py`).

**C1 is `FALSE`.**  The argument below was too narrow.  A 2-connected graph has no cut vertex
but can still have a 2-vertex separator, and a 2-cut carries its own factorisation with *more*
freedom than this one, not less.  Three 2-connected bipartite graphs on `56`, `58` and `62`
vertices, of vertex connectivity exactly two, carry a root of `μ_G` strictly inside a gap of
`spec(T)`.  See `SeparationOrder`, where the 2-cut factorisation is `two_cut_factor` and the
freedom count is `freedom_grows`.

## What survives

The factorisation itself, and the reading of it.  `branch_factor` is correct and is still the
engine of the `κ = 1` counterexamples; what was wrong was the inference that removing cut
vertices removes the engine.  The lesson is that the relevant feature is a *separation*, of
which a cut vertex is only the smallest case.

Minimum degree two and bounded maximum degree failed before this because they are local
conditions and the mechanism is global.  That reading was right.  What C1 got wrong was the
order of the separation, not its relevance.
-/

namespace CutVertexMechanism

open Polynomial

/-! ## The branch factorisation -/

/-- **The engine of every counterexample.**  If deleting a vertex leaves `p` copies of `H`,
and deleting it with a neighbour leaves `H - v` beside `p - 1` copies of `H`, then the matching
polynomial factors through `X μ_H - p μ_{H-v}`.  Stated as the polynomial identity, with the
two deletion counts as the hypotheses. -/
theorem branch_factor (muH muHv muG : ℤ[X]) (p : ℕ) (hp : 1 ≤ p)
    (hrec : muG = X * muH ^ p - (p : ℤ[X]) * muHv * muH ^ (p - 1)) :
    muG = muH ^ (p - 1) * (X * muH - (p : ℤ[X]) * muHv) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  simp only [Nat.add_sub_cancel_left] at *
  rw [hrec]
  ring

/-- The last factor is what carries the root: any root of it is a root of `μ_G`. -/
theorem root_of_branch_factor (muH muHv muG : ℤ[X]) (p : ℕ) (hp : 1 ≤ p)
    (hrec : muG = X * muH ^ p - (p : ℤ[X]) * muHv * muH ^ (p - 1))
    {θ : ℝ} (hθ : aeval θ (X * muH - (p : ℤ[X]) * muHv) = 0) :
    aeval θ muG = 0 := by
  rw [branch_factor muH muHv muG p hp hrec, map_mul, hθ, mul_zero]

/-! ## What the factorisation needs -/

/-- A vertex is *separating* for `G` when two vertices of `G - v` are mutually unreachable.
This is exactly the hypothesis the branch factorisation consumes, and a 2-connected graph has
no separating vertex. -/
def Separating {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b : ({u : V | u ≠ v} : Set V), ¬ (G.induce {u : V | u ≠ v}).Reachable a b

/-- **The mechanism needs a separation.**  Two branches of `G - v` are mutually unreachable,
which is precisely what makes `v` separating. -/
theorem separating_of_unreachable {V : Type*} (G : SimpleGraph V) (v : V)
    (a b : ({u : V | u ≠ v} : Set V))
    (h : ¬ (G.induce {u : V | u ≠ v}).Reachable a b) : Separating G v :=
  ⟨a, b, h⟩

/-- Having no separating vertex is exactly connectedness of every vertex-deleted subgraph. -/
theorem not_separating_iff {V : Type*} (G : SimpleGraph V) (v : V) :
    ¬ Separating G v ↔
      ∀ a b : ({u : V | u ≠ v} : Set V), (G.induce {u : V | u ≠ v}).Reachable a b := by
  simp [Separating]

/-- **C1, stated.**  That having no separating vertex suffices for the localization.  Recorded
so that the refuted target is unambiguous: this is `FALSE`, by the 2-cut counterexamples of
`SeparationOrder`.  A graph with no separating vertex can still have a separating *pair*. -/
def C1 : Prop :=
  ∀ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (Zeros Spec : Set ℝ),
    (∀ v, ¬ Separating G v) → Zeros ⊆ Spec

/-- A *separating pair*: the feature C1 failed to exclude.  Removing two vertices can
disconnect a graph that no single vertex disconnects, and that is enough for the mechanism. -/
def SeparatingPair {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ a b : ({w : V | w ≠ u ∧ w ≠ v} : Set V),
    ¬ (G.induce {w : V | w ≠ u ∧ w ≠ v}).Reachable a b

/-- **The gap in the C1 argument, exactly.**  Having no separating vertex says nothing about
separating pairs, so `∀ v, ¬ Separating G v` does not rule out the 2-cut engine.  This is the
implication C1 tacitly assumed and which does not hold. -/
theorem separatingPair_of_unreachable {V : Type*} (G : SimpleGraph V) (u v : V)
    (a b : ({w : V | w ≠ u ∧ w ≠ v} : Set V))
    (h : ¬ (G.induce {w : V | w ≠ u ∧ w ≠ v}).Reachable a b) : SeparatingPair G u v :=
  ⟨a, b, h⟩

end CutVertexMechanism
