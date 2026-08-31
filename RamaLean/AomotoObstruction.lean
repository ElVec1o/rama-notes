import Mathlib

/-!
# The branch mechanism cannot produce a counterexample

**This file replaces `RamaLean/D3Counterexample.lean`, which is retracted.** That file asserted that
Conjecture D3 (minimum degree three) is false, on a 14-vertex graph with `√3 ∉ spec(T_G)`. The claim
is wrong: `√3` is an *eigenvalue* of the universal cover there, so it lies in `spec(T_G)`. The
arithmetic in that file was correct; what it certified was not what we thought. See
`code/aomoto_obstruction.py`.

## The correct statement

Banks, Garza-Vargas and Mukherjee characterise the point spectrum of the universal cover: `θ` is an
eigenvalue of `T_G` if and only if `G` has a **`θ`-Aomoto subset**, that is a set `S ⊆ V(G)` with

* `G[S]` a forest,
* `θ` an eigenvalue of every component of `G[S]`,
* `|∂S| < cc(G[S])`.

Now take the configuration behind the Divisibility Lemma: a separator `S` of size `k` whose removal
leaves `p` components, each inducing a copy of the same tree `B`, with `θ` an eigenvalue of `B`. The
union `U` of the branch vertex sets has `cc(G[U]) = p`, and every vertex outside `U` adjacent to `U`
lies in `S`, so `|∂U| ≤ k`. Hence

  **`p > k` ⟹ `|∂U| < cc(G[U])` ⟹ `θ ∈ spec(T_G)`.**

And `p > k` is exactly the hypothesis `DivisibilityLemma.exponent_pos_iff` needs for `A ^ (p - k)` to
be a nontrivial divisor. The configuration that manufactures a root of `μ_G` is the configuration
that places that root in the spectrum of the cover. The two conditions are the same condition, which
is why the mechanism can never refute anything.

## What is formalised

`boundary_lt_components` is the counting step: a boundary contained in a set of size `k`, together
with `p` components and `k < p`, gives `|∂U| < cc`. `obstruction` packages it as the implication
that drives the argument, and `divisor_and_obstruction_coincide` records that the Aomoto inequality
and the Divisibility Lemma's exponent condition are literally the same inequality on `p` and `k`.

The Aomoto criterion itself is the analytic input and is cited, not reproved; Mathlib carries
neither the matching polynomial nor covers of graphs, which is the standing gap in this development.

## Status

`boundary_lt_components`, `obstruction` and `divisor_and_obstruction_coincide` are `VERIFIED`.
-/

namespace AomotoObstruction

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in

/-- **The counting step.**  If the boundary of the branch union is contained in the separator `S`,
there are `p` components, and `p` exceeds `|S|`, then the Aomoto inequality holds. -/
theorem boundary_lt_components (bdry S : Finset V) (k p : ℕ)
    (hsub : bdry ⊆ S) (hS : S.card = k) (hkp : k < p) :
    bdry.card < p := by
  have : bdry.card ≤ k := by rw [← hS]; exact Finset.card_le_card hsub
  omega

omit [DecidableEq V] in
/-- **The general form.**  Only the number of qualifying components matters, not their shape: if at
least `k+1` components of `G - S` induce forests with `θ` as an eigenvalue, their union is a
`θ`-Aomoto subset. The components need not be isomorphic, and need not be all of `G - S`. -/
theorem general_obstruction (bdry S : Finset V) (k j : ℕ)
    (hsub : bdry ⊆ S) (hS : S.card = k) (hj : k + 1 ≤ j) :
    bdry.card < j :=
  boundary_lt_components bdry S k j hsub hS (by omega)

omit [DecidableEq V] in
/-- **The obstruction.**  Under the hypotheses of the Divisibility Lemma with `p > k`, the branch
union satisfies the Aomoto inequality, so by the criterion of Banks--Garza-Vargas--Mukherjee the
branch eigenvalue is an eigenvalue of the universal cover, hence lies in its spectrum.

`AomotoIneq` abstracts the inequality that the criterion consumes; the criterion itself is the
analytic input and is not formalised here. -/
theorem obstruction (bdry S : Finset V) (k p : ℕ)
    (AomotoIneq : ℕ → ℕ → Prop) (hdef : ∀ b c, AomotoIneq b c ↔ b < c)
    (hsub : bdry ⊆ S) (hS : S.card = k) (hkp : k < p) :
    AomotoIneq bdry.card p :=
  (hdef _ _).mpr (boundary_lt_components bdry S k p hsub hS hkp)

/-- **The two conditions are one condition.**  The Divisibility Lemma needs `k < p` for the exponent
`p - k` to be positive, and the Aomoto inequality for the branch union is `|∂U| < cc(G[U])`, which
under `|∂U| ≤ k` and `cc = p` is the same statement. So every configuration that gives a nontrivial
branch divisor also puts its root in the spectrum of the cover. -/
theorem divisor_and_obstruction_coincide (k p : ℕ) :
    0 < p - k ↔ k < p := Nat.sub_pos_iff_lt

end AomotoObstruction
