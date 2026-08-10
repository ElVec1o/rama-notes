import Mathlib
import RamaLean.CutVertexMechanism
import RamaLean.MinimumDegreeThreshold

/-!
# The glued search, and why it is a test of `D3` at all

The evidence for `D3` is now largely a search: `806` cut-based configurations
(`code/D1cut.py`, `code/D1cut_adv.py`), `299` graphs with no separator
(`code/D3broad.py`) and `39` with a separating pair, all clean.  A search is only worth its
count if two things hold, and neither is obvious from the code.

* **The constructed graphs are in scope.**  `D3` quantifies over graphs of minimum degree three.
  Hall's engine glues `p` copies of a block `H` to a new centre, and the resulting minimum degree
  is not `min` of `H`'s degrees: the centre is a new vertex of degree `p`, and the attachment
  vertex gains one. If the arithmetic there is wrong the search tests a different class than the
  one `D3` speaks about, and its count means nothing.
* **A hit would actually refute.**  The reason a root of `μ_H` is worth testing at all is the
  branch factorisation, which makes it a root of `μ_G`
  (`CutVertexMechanism.root_of_branch_factor`).

This file proves the first and assembles the second into the soundness statement the search needs:
finding nothing is evidence for `D3`, and finding something refutes it.  What is *not* claimed
here is that any particular `θ` lies in `spec(T)`; that stays a computation, gated by
`SpectralAtom`.

## The degree arithmetic

Gluing `p ≥ 3` copies of `H` at a new centre joined to the copy of `v` in each gives

* the centre degree `p`,
* each copy of `v` degree `deg_H(v) + 1`,
* every other vertex its degree in `H`,

so minimum degree three needs exactly `p ≥ 3`, `deg_H(v) ≥ 2` and `deg_H(u) ≥ 3` for `u ≠ v`
(`glued_min_degree`).  The middle condition is the one that is easy to get wrong: the attachment
vertex is allowed degree **two** inside `H`, because gluing gives it a third edge.  That is what
makes `K_{2,q}` blocks usable at all, and widening the side graph to any graph of minimum degree
one — rather than a regular one — is the same observation applied to the other vertices.

## Status

`glued_min_degree`, `glued_deg_centre`, `glued_deg_attach`, `glued_deg_other`,
`search_sound` and `search_refutes` are `VERIFIED`.
-/

namespace GluedSearch

variable {V : Type*} [DecidableEq V]

/-- Degree of a vertex of the glued graph, with `none` the new centre and `some u` the copy of
`u` in one block.  `p` is the number of copies, `v` the attachment vertex of the block. -/
def gluedDeg (dH : V → ℕ) (v : V) (p : ℕ) : Option V → ℕ
  | none => p
  | some u => if u = v then dH u + 1 else dH u

@[simp] theorem glued_deg_centre (dH : V → ℕ) (v : V) (p : ℕ) :
    gluedDeg dH v p none = p := rfl

@[simp] theorem glued_deg_attach (dH : V → ℕ) (v : V) (p : ℕ) :
    gluedDeg dH v p (some v) = dH v + 1 := by simp [gluedDeg]

theorem glued_deg_other (dH : V → ℕ) (v : V) (p : ℕ) {u : V} (h : u ≠ v) :
    gluedDeg dH v p (some u) = dH u := by simp [gluedDeg, h]

/-- **The construction lands in `D3`'s scope.**  Note the attachment vertex needs only degree
two inside the block: gluing supplies its third edge.  That is why `K_{2,q}` blocks, whose hubs
are the attachment and whose other side has degree two, become admissible once the side graph
contributes one more edge. -/
theorem glued_min_degree (dH : V → ℕ) (v : V) (p : ℕ)
    (hp : 3 ≤ p) (hv : 2 ≤ dH v) (hother : ∀ u, u ≠ v → 3 ≤ dH u) :
    ∀ w : Option V, 3 ≤ gluedDeg dH v p w := by
  intro w
  match w with
  | none => simpa using hp
  | some u =>
      by_cases h : u = v
      · subst h; simp only [glued_deg_attach]; omega
      · rw [glued_deg_other dH v p h]; exact hother u h

/-! ## Soundness of the search

Abstractly: `G` ranges over a carrier `Γ`, `MinDeg` and `Violates` are as in
`MinimumDegreeThreshold`, and `glue H p` is the graph the engine builds.  The two hypotheses are
exactly the two facts above, and they are supplied by `glued_min_degree` and by the branch
factorisation. -/

variable {Γ : Type*}

/-- **A hit refutes `D3`.**  If the construction has minimum degree three and its root escapes
the spectrum, `D3` is false.  This is why the search is worth running. -/
theorem search_refutes {MinDeg : Γ → ℕ} {Violates : Γ → Prop}
    (glue : Γ → ℕ → Γ) (H : Γ) (p : ℕ)
    (hdeg : 3 ≤ MinDeg (glue H p)) (hhit : Violates (glue H p)) :
    ¬ MinimumDegreeThreshold.D3 MinDeg Violates := by
  intro hD3
  exact hD3 (glue H p) hdeg hhit

/-- **Finding nothing is evidence, and of exactly this shape.**  If `D3` holds then no glued
configuration of minimum degree three can violate, so a clean search is consistent with `D3` and
a dirty one is not.  The converse does not hold and is not claimed: the search covers a family,
not the class. -/
theorem search_sound {MinDeg : Γ → ℕ} {Violates : Γ → Prop}
    (hD3 : MinimumDegreeThreshold.D3 MinDeg Violates)
    (glue : Γ → ℕ → Γ) (H : Γ) (p : ℕ) (hdeg : 3 ≤ MinDeg (glue H p)) :
    ¬ Violates (glue H p) :=
  hD3 (glue H p) hdeg

end GluedSearch
