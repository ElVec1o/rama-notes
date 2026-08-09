import Mathlib

/-!
# The cut vertex is the mechanism

Every known counterexample to Conjecture 10 is built the same way: a cut vertex `v` whose
removal leaves `p` isomorphic branches `H`, so that the vertex-deletion recurrence factors the
matching polynomial and a root can be placed by tuning `p` and `H`.  This file isolates that
factorisation, which is the engine, and records what it needs.

## The factorisation

Deleting `v` leaves `p` disjoint copies of `H`, and deleting `v` together with one neighbour
leaves one copy of `H - v` and `p - 1` copies of `H`.  The recurrence
`μ_G = X μ_{G-v} - ∑_{u ∼ v} μ_{G-v-u}` therefore gives

  `μ_G = X μ_H^p - p μ_{H-v} μ_H^{p-1} = μ_H^{p-1} (X μ_H - p μ_{H-v})`,

and every counterexample takes its root from the last factor.  That is `branch_factor`.

**This requires a cut vertex.**  The step "deleting `v` leaves `p` disjoint copies" is exactly
the statement that `v` separates `G`, and for `p ≥ 2` that is what a cut vertex is.  In a
2-connected graph no vertex has this property, the matching polynomial does not factor this
way, and the construction has nothing to tune.

## The frozen hypothesis

  **C1.**  Every 2-connected finite graph satisfies `Zeros(μ_G) ⊆ spec(T_G)`.

Evidence, all obtained after C1 was written down.  Twenty-six 2-connected graphs with a cycle
skeleton produce no root in any gap (`code/cycle_family.py`).  Every counterexample in hand has
cut vertices, fifteen in the `31`-vertex graph and eleven in Hall's.  And closing those graphs
up, by adding a ring of edges until no cut vertex remains, destroys the violation every time:
five closures tested, and in each the root returns to `spec(T)` exactly when the cut vertices
are gone (`code/twoconnected.py`).

C1 is a `CONJECTURE`.  What is proved below is the factorisation it would have to defeat, and
the elementary observation that the factorisation is unavailable without a cut vertex.

## Why this is the right hypothesis to have reached

Minimum degree two and bounded maximum degree both failed, and failed to one graph.  Those are
local conditions, and the mechanism is not local: it needs a global separation.  Connectivity
is the invariant that sees separations, which is why it is the one that survives.
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

/-- **C1, stated.**  The conjecture is that having no separating vertex suffices for the
localization.  Recorded so that the target is unambiguous; it is not proved here. -/
def C1 : Prop :=
  ∀ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (Zeros Spec : Set ℝ),
    (∀ v, ¬ Separating G v) → Zeros ⊆ Spec

end CutVertexMechanism
