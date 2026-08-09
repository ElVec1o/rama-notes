import Mathlib

/-!
# The tuning freedom is the order of the separation

`CutVertexMechanism` isolated the identity every counterexample to Conjecture 10 runs on,

  `μ_G = μ_H^{p-1} (X μ_H - p μ_{H-v})`,

and observed that it needs a cut vertex.  The hypothesis **C1**, that 2-connectedness therefore
restores the conjecture, was frozen on that basis.

**C1 is false.**  A 2-connected graph has no cut vertex but may still have a 2-vertex
separator, and a 2-cut carries its own recurrence.  With two hubs and `p` branches attached to
both, writing `A` for the branch polynomial, `A₁` and `A₂` for the branch with one anchor
deleted and `A₁₂` for both,

  `μ_G = A^{p-2} (X²A² - pX(A₁+A₂)A + p A₁₂ A + p(p-1) A₁A₂)`,

which is `two_cut_factor` below.  Three graphs of this shape, on `56`, `58` and `62` vertices,
have no cut vertex and carry a root of `μ_G` strictly inside a gap of `spec(T)`
(`code/twocut.py`, verified in `private/verify_twocut.py` by an exact factorisation of `μ_G`, a
`40`-digit Angel-Friedman-Hoory decay rate of `0.94` to `0.96`, and a density-of-states ladder
in which the root scales linearly in `η` while an in-band control stays constant).

## The freedom grows with the order of the separation

Compare the two brackets *as polynomials in the number of branches* `p`.  The cut-vertex
bracket is linear in `p`; the 2-cut bracket is quadratic, with leading coefficient `A₁A₂`.
That is `cutBracket_natDegree`, `twoCutBracket_natDegree` and `freedom_grows`.

So forbidding the cut vertex does not remove the mechanism, it upgrades it: the 2-cut bracket
has *more* room to place a root than the cut-vertex bracket, not less.  The obstruction is a
separation of some order, and connectivity bounds that order from below rather than removing it.

## Why that does not immediately close the connectivity route

The obvious continuation, that a `k`-cut beats `k`-connectedness for every `k`, was predicted
and **did not happen**.  A search over thirty-eight branch families at `k = 3, 4, 5`, with `p`
branches and up to `62` vertices, found no root in any gap (`code/kcut.py`, with the `k`-cut
expansion checked against a brute-force matching polynomial at `k = 3`).  The search was not
vacuous: those graphs do have gaps, two to five of them with total width `0.40` to `0.75`
(`private/gapdiag.py`).

There is a second effect running the other way.  Raising the connectivity forces more edges,
which widens the bands of `spec(T)` and narrows the gaps that a root could hide in.  At `k = 2`
the extra tuning freedom wins.  At `k = 3`, in the range searched, the narrowing wins.  Which
effect dominates in general is open, and it is the real question this file leaves behind.

## Status

`two_cut_factor`, `root_of_two_cut`, `cutBracket_natDegree`, `twoCutBracket_natDegree` and
`freedom_grows` are `VERIFIED`.  `C1` is `FALSE`.  `C2` and `NoConnectivityRepair` are the two
incompatible continuations, stated below; `no_threshold_works` records that they exclude each
other.  `C2` is the one the evidence currently favours, and it is a `CONJECTURE` on a search
range narrow enough that it should be treated as provisional.
-/

namespace SeparationOrder

open Polynomial

/-- Polynomials in the graph variable: matching polynomials live here. -/
abbrev GPoly := Polynomial ℤ

/-- Polynomials in the branch count `p`, with matching polynomials as coefficients.  Viewing a
bracket in this ring is what exposes how much freedom the construction has. -/
abbrev BPoly := Polynomial GPoly

/-! ## The two brackets -/

/-- The cut-vertex bracket `X μ_H - p μ_{H-v}`, read as a polynomial in `p`. -/
noncomputable def cutBracket (A A1 : GPoly) : BPoly := C ((X : GPoly) * A) - (X : BPoly) * C A1

/-- The 2-cut bracket `X²A² - pX(A₁+A₂)A + p A₁₂ A + p(p-1) A₁A₂`, read as a polynomial in
`p`.  The `p(p-1)` term is what the cut-vertex bracket does not have. -/
noncomputable def twoCutBracket (A A1 A2 A12 : GPoly) : BPoly :=
  C (A1 * A2) * (X : BPoly) ^ 2
    + C (A12 * A - (X : GPoly) * (A1 + A2) * A - A1 * A2) * (X : BPoly)
    + C ((X : GPoly) ^ 2 * A ^ 2)

/-! ## The 2-cut factorisation -/

/-- **The engine that refuted C1.**  Two hubs and `p = k+2` branches attached to both: summing
over which hub is matched into which branch gives the displayed recurrence, and it factors
through a bracket exactly as the cut-vertex recurrence does.  A 2-connected graph admits this
even though it admits no cut vertex. -/
theorem two_cut_factor (A A1 A2 A12 muG : GPoly) (k : ℕ)
    (hrec : muG = X ^ 2 * A ^ (k + 2)
              - ((k + 2 : ℕ) : GPoly) * X * (A1 + A2) * A ^ (k + 1)
              + ((k + 2 : ℕ) : GPoly) * A12 * A ^ (k + 1)
              + ((k + 2 : ℕ) : GPoly) * ((k + 1 : ℕ) : GPoly) * A1 * A2 * A ^ k) :
    muG = A ^ k * (X ^ 2 * A ^ 2
              - ((k + 2 : ℕ) : GPoly) * X * (A1 + A2) * A
              + ((k + 2 : ℕ) : GPoly) * A12 * A
              + ((k + 2 : ℕ) : GPoly) * ((k + 1 : ℕ) : GPoly) * A1 * A2) := by
  rw [hrec]; ring

/-- A root of the 2-cut bracket is a root of `μ_G`: the bracket is where the root is placed. -/
theorem root_of_two_cut (A A1 A2 A12 muG : GPoly) (k : ℕ)
    (hrec : muG = X ^ 2 * A ^ (k + 2)
              - ((k + 2 : ℕ) : GPoly) * X * (A1 + A2) * A ^ (k + 1)
              + ((k + 2 : ℕ) : GPoly) * A12 * A ^ (k + 1)
              + ((k + 2 : ℕ) : GPoly) * ((k + 1 : ℕ) : GPoly) * A1 * A2 * A ^ k)
    {θ : ℝ}
    (hθ : aeval θ (X ^ 2 * A ^ 2
              - ((k + 2 : ℕ) : GPoly) * X * (A1 + A2) * A
              + ((k + 2 : ℕ) : GPoly) * A12 * A
              + ((k + 2 : ℕ) : GPoly) * ((k + 1 : ℕ) : GPoly) * A1 * A2) = 0) :
    aeval θ muG = 0 := by
  rw [two_cut_factor A A1 A2 A12 muG k hrec, map_mul, hθ, mul_zero]

/-! ## The freedom count -/

/-- The cut-vertex bracket is **linear** in the branch count. -/
theorem cutBracket_natDegree (A A1 : GPoly) (h : A1 ≠ 0) :
    (cutBracket A A1).natDegree = 1 := by
  have : cutBracket A A1 = C (-A1) * X + C ((X : GPoly) * A) := by
    unfold cutBracket; rw [map_neg]; ring
  rw [this]
  exact natDegree_linear (neg_ne_zero.mpr h)

/-- The 2-cut bracket is **quadratic** in the branch count, with leading coefficient `A₁A₂`. -/
theorem twoCutBracket_natDegree (A A1 A2 A12 : GPoly) (h1 : A1 ≠ 0) (h2 : A2 ≠ 0) :
    (twoCutBracket A A1 A2 A12).natDegree = 2 :=
  natDegree_quadratic (mul_ne_zero h1 h2)

/-- **The tuning freedom grows with the order of the separation.**  Forbidding the cut vertex
does not remove the mechanism; it upgrades it, replacing a bracket linear in the branch count
by one that is quadratic.  This is why C1 was false, and why the same is expected at every
level of the connectivity ladder. -/
theorem freedom_grows (A A1 A2 A12 : GPoly) (h1 : A1 ≠ 0) (h2 : A2 ≠ 0) :
    (cutBracket A A1).natDegree < (twoCutBracket A A1 A2 A12).natDegree := by
  rw [cutBracket_natDegree A A1 h1, twoCutBracket_natDegree A A1 A2 A12 h1 h2]
  norm_num

/-! ## What is left of the connectivity route -/

/-- **The route is closed.**  For every `κ` there is a `κ`-connected finite graph violating
Conjecture 10.  `κ = 1` is Hall's counterexample and `κ = 2` is the refutation of C1 above; the
degree count `freedom_grows` is the reason to expect it to continue.  It is stated because it
was predicted, and the `k`-cut search did **not** confirm it beyond `κ = 2`. -/
def NoConnectivityRepair
    (Connectivity : (Σ V : Type, SimpleGraph V) → ℕ)
    (Violates : (Σ V : Type, SimpleGraph V) → Prop) : Prop :=
  ∀ κ : ℕ, ∃ G, κ ≤ Connectivity G ∧ Violates G

/-- **C2, the surviving hypothesis.**  Three-connectedness repairs Conjecture 10.  This is what
the failure of the `k = 3, 4, 5` search suggests, against the prediction of `freedom_grows`,
and it is the exact point at which the two effects are claimed to balance. -/
def C2
    (Connectivity : (Σ V : Type, SimpleGraph V) → ℕ)
    (Violates : (Σ V : Type, SimpleGraph V) → Prop) : Prop :=
  ∀ G, 3 ≤ Connectivity G → ¬ Violates G

/-- Once every connectivity level contains a violating graph, no threshold on connectivity
implies non-violation.  So `NoConnectivityRepair` and `C2` are incompatible, and the `k`-cut
search is a genuine test between them rather than a matter of taste. -/
theorem no_threshold_works
    {Connectivity : (Σ V : Type, SimpleGraph V) → ℕ}
    {Violates : (Σ V : Type, SimpleGraph V) → Prop}
    (h : NoConnectivityRepair Connectivity Violates) (κ : ℕ) :
    ¬ (∀ G, κ ≤ Connectivity G → ¬ Violates G) := by
  intro hthr
  obtain ⟨G, hκ, hv⟩ := h κ
  exact hthr G hκ hv

/-- The two continuations exclude each other. -/
theorem C2_not_noRepair
    {Connectivity : (Σ V : Type, SimpleGraph V) → ℕ}
    {Violates : (Σ V : Type, SimpleGraph V) → Prop}
    (h : NoConnectivityRepair Connectivity Violates) :
    ¬ C2 Connectivity Violates :=
  no_threshold_works h 3

end SeparationOrder
