import Mathlib

/-!
# The gap-label program for Conjecture 10

This file fixes the logical skeleton of the route to Conjecture 10 at `d = 1`, so that the
statement of what remains open is pinned by the kernel rather than by prose.

Write `T` for the universal cover of a finite connected loopless `G` on `n` vertices, and
recall that `x ∉ spec(T)` is equivalent to invertibility of `x I - A_G` in
`M_n(C*_r(F_b))`, `b = b₁(G)`.  For such `x` the negative spectral projection
`P₋(x) = 1_{(-∞,0)}(x I - A_G)` is a projection in that algebra, and Pimsner–Voiculescu's
computation `K₀(C*_r(F_b)) = ℤ·[1]` forces its amplified trace

  `κ(x) = τ_n(P₋(x)) ∈ ℤ ∩ [0,n]`,

the **gap label**.  It is locally constant off `spec(T)` and takes the value `0` above
`ρ(T)` and `n` below `-ρ(T)`.

The statement this file is organised around is

  **GAPCOUNT.**  For `x ∉ spec(T)`, the number of roots of `μ_G` strictly above `x`,
  counted with multiplicity, equals `κ(x)`.

GAPCOUNT is strictly stronger than Conjecture 10, and it implies it: `κ` is constant across
a gap while the root count jumps at any root, so a gap contains no root.  That implication
is `no_root_of_countAbove_const` and `conj10_of_gapcount` below, both proved.  What is *not*
proved is GAPCOUNT itself; nothing here asserts it.

The point of separating them is that Conjecture 10 is a non-vanishing statement, which
offers no handle, whereas GAPCOUNT equates two integers.  Integer-valued locally constant
quantities are computed by deformation from a boundary condition, which is the standard
shape of an index theorem and is the new attack surface.  `countAbove_eq_of_locallyConstant`
records that a locally constant integer function is already determined on a connected gap by
one value, and `gapcount_at_top` records the boundary condition at `x > ρ(T)`.

Status of the pieces, in the labels of the project's rules:

* `no_root_of_countAbove_const`, `conj10_of_gapcount`,
  `countAbove_eq_of_locallyConstant`, `gapcount_at_top` — VERIFIED here.
* integrality and local constancy of `κ` — PROVED modulo Pimsner–Voiculescu, which is not
  in Mathlib (see `RamaLean/FeedbackVertex.lean` for the `k = 1` consumption of it).
* GAPCOUNT — CONJECTURE.  Verified exactly on 24 graphs at 65 gap points by
  `code/gap_count.py`; no counterexample.
-/

namespace GapLabel

open Multiset

/-! ## The root-counting function -/

/-- `countAbove R x` is the number of elements of the multiset `R` strictly greater than
`x`.  Applied to the root multiset of `μ_G` it is the left side of GAPCOUNT. -/
noncomputable def countAbove (R : Multiset ℝ) (x : ℝ) : ℕ := R.countP (fun r => x < r)

theorem countAbove_le_card (R : Multiset ℝ) (x : ℝ) : countAbove R x ≤ Multiset.card R :=
  Multiset.countP_le_card _ _

/-- Monotonicity of `countP` in the predicate, by induction on the multiset. -/
theorem countP_le_countP_of_imp {α : Type*} (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (s : Multiset α) (h : ∀ a, p a → q a) :
    s.countP p ≤ s.countP q := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      by_cases hp : p a
      · rw [Multiset.countP_cons_of_pos _ hp, Multiset.countP_cons_of_pos _ (h a hp)]; omega
      · rw [Multiset.countP_cons_of_neg _ hp]
        by_cases hq : q a
        · rw [Multiset.countP_cons_of_pos _ hq]; omega
        · rw [Multiset.countP_cons_of_neg _ hq]; omega

/-- `countAbove` is antitone: lowering the cut can only include more roots. -/
theorem countAbove_antitone (R : Multiset ℝ) {u v : ℝ} (huv : u ≤ v) :
    countAbove R v ≤ countAbove R u := by
  classical
  exact countP_le_countP_of_imp _ _ R fun r hr => lt_of_le_of_lt huv hr

/-- **The jump.**  A root strictly above the cut `u` and at most `v` is counted at `u` and
not at `v`, so the count drops by at least one across it. -/
theorem countAbove_lt_of_mem (R : Multiset ℝ) {u v θ : ℝ} (hθ : θ ∈ R)
    (huθ : u < θ) (hθv : θ ≤ v) : countAbove R v < countAbove R u := by
  classical
  have huv : u < v := lt_of_lt_of_le huθ hθv
  obtain ⟨S, hS⟩ : ∃ S, R = θ ::ₘ S := ⟨R.erase θ, (Multiset.cons_erase hθ).symm⟩
  subst hS
  have hpos : countAbove (θ ::ₘ S) u = countAbove S u + 1 := by
    simp only [countAbove]; exact Multiset.countP_cons_of_pos _ huθ
  have hneg : countAbove (θ ::ₘ S) v = countAbove S v := by
    simp only [countAbove]; exact Multiset.countP_cons_of_neg _ (not_lt.mpr hθv)
  have hmono : countAbove S v ≤ countAbove S u := countAbove_antitone _ huv.le
  omega

/-! ## Constancy forbids roots -/

/-- **The implication that carries the program.**  If the root count above the cut is
constant throughout an open interval, that interval contains no root.

This is why GAPCOUNT is worth more than Conjecture 10: the right side of GAPCOUNT is a
spectral quantity which is manifestly constant across a gap, so constancy of the left side
is automatic once the two are identified, and non-vanishing follows. -/
theorem no_root_of_countAbove_const (R : Multiset ℝ) {a b : ℝ}
    (hconst : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo a b, countAbove R u = countAbove R v)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo a b) : θ ∉ R := by
  intro hmem
  obtain ⟨u, hu1, hu2⟩ := exists_between hθ.1
  have hu : u ∈ Set.Ioo a b := ⟨hu1, lt_trans hu2 hθ.2⟩
  have hjump : countAbove R θ < countAbove R u :=
    countAbove_lt_of_mem R hmem hu2 le_rfl
  rw [hconst θ hθ u hu] at hjump
  exact lt_irrefl _ hjump

/-- **GAPCOUNT implies Conjecture 10 on a gap.**  `kappa` is the gap label, assumed here
only to be constant on the gap, which it is because the gap carries no spectrum. -/
theorem conj10_of_gapcount (R : Multiset ℝ) (kappa : ℝ → ℕ) {a b : ℝ}
    (hgapcount : ∀ x ∈ Set.Ioo a b, countAbove R x = kappa x)
    (hkappa : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo a b, kappa u = kappa v)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo a b) : θ ∉ R := by
  refine no_root_of_countAbove_const R ?_ hθ
  intro u hu v hv
  rw [hgapcount u hu, hgapcount v hv]
  exact hkappa u hu v hv

/-! ## Why the label is determined -/

/-- A locally constant function on a preconnected set is determined by one of its values.
This is the deformation principle the program runs on: the gap label is fixed on each gap
by transporting the boundary condition at `x > ρ(T)` along the complement of the spectrum,
so the content of GAPCOUNT is a statement about how the root count changes as a band is
crossed, not about any single gap. -/
theorem countAbove_eq_of_locallyConstant {f : ℝ → ℕ} (hf : IsLocallyConstant f)
    {s : Set ℝ} (hs : IsPreconnected s) {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) :
    f u = f v :=
  hf.apply_eq_of_isPreconnected hs hu hv

/-- **The boundary condition.**  Above every root the count is zero, which is the value the
gap label must take above `ρ(T)`.  GAPCOUNT at the top of the spectrum is therefore free;
all the content is in what happens as each band is crossed downward. -/
theorem gapcount_at_top (R : Multiset ℝ) {x : ℝ} (hx : ∀ r ∈ R, r ≤ x) :
    countAbove R x = 0 := by
  classical
  rw [countAbove, Multiset.countP_eq_zero]
  intro r hr
  exact not_lt.mpr (hx r hr)

/-- **The boundary condition at the bottom.**  Below every root the count is the full
degree, matching `κ = n`. -/
theorem gapcount_at_bot (R : Multiset ℝ) {x : ℝ} (hx : ∀ r ∈ R, x < r) :
    countAbove R x = Multiset.card R := by
  classical
  rw [countAbove, Multiset.countP_eq_card]
  exact hx

end GapLabel
