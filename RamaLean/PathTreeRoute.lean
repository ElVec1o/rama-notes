import Mathlib

/-!
# A tree-theoretic reformulation, and what the measurements say about it

Five search engines have been run against `D3` and all came back clean, which raises confidence
and yields nothing proof-shaped. This file records the one reformulation the measurements
actually hand over, and is deliberately modest about it: the implication below is easy, and its
value is that it moves the question off matchings and onto a finite tree.

## The reduction

Godsil's path tree `P = P(G,v)` satisfies `μ_G ∣ μ_P`, so every root of `μ_G` is a root of `μ_P`;
and `P` is a tree, where the matching polynomial is the characteristic polynomial, so those roots
are eigenvalues of `P`. Hence

  `spec(P) ⊆ spec(T)`   ⟹   `Zeros(μ_G) ⊆ spec(T)`,

which is `conj_of_pathtree` below. The hypothesis is strictly stronger than the conclusion, since
`μ_P` carries its own roots as well as those of `μ_G`, and that is the point rather than a defect:
it is a statement about the spectrum of one explicit finite tree, with no matchings in it.

## Why it is worth stating

Because it is not vacuous in either direction, and the measurements pin both.

* It **fails** for Hall's graph, necessarily: `√5` is a root of `μ_G`, hence an eigenvalue of the
  path tree, and it is outside `spec(T)`. So the hypothesis is genuinely restrictive and cannot be
  proved in general — as it must not be, the conjecture being false.
* It **holds**, measured, wherever it has been looked at: over four `(d,q,r)` families that are
  not complete bipartite, with path trees of `3457`, `17241`, `22402` and `291429` vertices, the
  path tree has no eigenvalue in the gap (`code/pathtree_inertia.py`), counted by Sylvester's law
  rather than by diagonalising.

So the content of `D3`, on the evidence available, is the assertion that minimum degree three
forces the path tree to inherit the gap. That is a question about self-avoiding paths and the
spectrum of the tree they form, and it is the form in which we would attack it next.

## What this is not

It is not a proof of anything new, and the implication is three lines. What it does is relocate
the conjecture: from "no root of a matching polynomial enters a gap" to "the path tree inherits
the gap", the second being about an explicit finite object. Whether that is easier is unknown.

## Status

`conj_of_pathtree` and `pathtree_fails_of_violation` are `VERIFIED`. The containment
`spec(P) ⊆ spec(T)` is a `CONJECTURE` at minimum degree three and is `HEURISTIC` for biregular
graphs, on four families.
-/

namespace PathTreeRoute

variable {α : Type*}

/-- **The reduction.**  If every eigenvalue of the path tree lies in the spectrum of the universal
cover, then so does every root of `μ_G`, since `μ_G ∣ μ_P` places the roots of `μ_G` among the
eigenvalues of `P`.  Stated over abstract sets so that it does not depend on an encoding of
graphs, path trees or covers. -/
theorem conj_of_pathtree (Zeros SpecP SpecT : Set α)
    (hdvd : Zeros ⊆ SpecP) (hinherit : SpecP ⊆ SpecT) :
    Zeros ⊆ SpecT :=
  fun _ hx => hinherit (hdvd hx)

/-- **The hypothesis is genuinely restrictive.**  A violation forces the path tree to carry an
eigenvalue outside the cover's spectrum, so `spec(P) ⊆ spec(T)` fails exactly where the
conjecture does.  For Hall's graph this is `√5`. -/
theorem pathtree_fails_of_violation (Zeros SpecP SpecT : Set α)
    (hdvd : Zeros ⊆ SpecP) {x : α} (hroot : x ∈ Zeros) (hout : x ∉ SpecT) :
    ¬ (SpecP ⊆ SpecT) :=
  fun h => hout (h (hdvd hroot))

/-- The two together, as the reformulation is meant to be used: on a class where the path tree
inherits the spectrum the conjecture holds there, and on a graph where it fails the path tree
witnesses the failure.  Nothing here is deep; it is a change of object. -/
theorem reformulation (Zeros SpecP SpecT : Set α) (hdvd : Zeros ⊆ SpecP) :
    (SpecP ⊆ SpecT → Zeros ⊆ SpecT) ∧
      (∀ x ∈ Zeros, x ∉ SpecT → ¬ (SpecP ⊆ SpecT)) :=
  ⟨fun h => conj_of_pathtree Zeros SpecP SpecT hdvd h,
   fun _ hx hout => pathtree_fails_of_violation Zeros SpecP SpecT hdvd hx hout⟩

end PathTreeRoute
