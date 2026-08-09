import Mathlib

/-!
# Every cycle uses a cotree edge

`TorusGodsilGutman.sum_ne_zero_of_disjoint_support` is the algebraic heart of the torus form
of Godsil–Gutman, but it consumes two graph-theoretic facts that were left informal:

1. every cycle of `G` uses at least one edge outside a fixed spanning tree, so its homology
   class in the cotree basis is nonzero;
2. the cycles of a permutation are vertex-disjoint, so they use disjoint edge sets.

This file proves the first, which is the one with content.  The second is immediate from the
cycle decomposition of a permutation and is recorded here as `disjoint_edges_of_disjoint_support`
in the form the argument uses.

## The argument

A spanning tree is acyclic.  If a cycle of `G` had all its edges in the tree, transferring the
walk to the tree would produce a cycle there, which is what acyclicity forbids.  That is
`exists_cotree_edge`.

## Status

`exists_cotree_edge` and `disjoint_edges_of_disjoint_support` are proved.  What remains
informal in the identity is only the identification of the monomial attached to a permutation
with the sum of the homology classes of its cycles, which is a definitional bookkeeping step
about how the magnetic matrix is set up rather than a mathematical one.
-/

namespace CotreeCycle

open SimpleGraph

variable {V : Type*}

/-! ## A cycle cannot lie inside a spanning tree -/

/-- **Every cycle of `G` uses an edge outside any acyclic subgraph.**  If all of its edges
lay in the tree, the walk would transfer to a cycle there, contradicting acyclicity.  Applied
to a spanning tree this says the homology class of a cycle, read in the cotree basis, is
nonzero.  No relation between `T` and `G` is needed: acyclicity of `T` alone does it. -/
theorem exists_cotree_edge {G T : SimpleGraph V} (hT : T.IsAcyclic)
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    ∃ e ∈ c.edges, e ∉ T.edgeSet := by
  by_contra h
  push Not at h
  exact hT (c.transfer T h) (hc.transfer h)

/-- The cycles of a permutation are vertex-disjoint, so any two of them share no edge.  Stated
on edge sets of walks with disjoint supports, which is the form
`sum_ne_zero_of_disjoint_support` consumes. -/
theorem disjoint_edges_of_disjoint_support {G : SimpleGraph V} {u v : V}
    (c : G.Walk u u) (d : G.Walk v v)
    (hdisj : ∀ w, w ∈ c.support → w ∉ d.support) :
    ∀ e ∈ c.edges, e ∉ d.edges := by
  intro e he hd
  revert he hd
  induction e using Sym2.inductionOn with
  | _ a b =>
    intro he hd
    exact hdisj a (c.fst_mem_support_of_mem_edges he) (d.fst_mem_support_of_mem_edges hd)

end CotreeCycle
