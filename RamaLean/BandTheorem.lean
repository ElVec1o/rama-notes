import Mathlib
import RamaLean.GapLabel

/-!
# The band theorem: GAPCOUNT over the maximal abelian cover

`GapLabel` sets up GAPCOUNT and proves that it implies Conjecture 10.  This file proves
the abelian instance of it outright, and in doing so isolates exactly what the universal
cover still needs.

## The statement

Put a circle variable on each of the `b = b₁(G)` cotree edges and let `A_G(z)` be the
magnetic adjacency matrix, Hermitian for `z ∈ T^b`.  Order eigenvalues decreasingly and set

  `B_k = λ_k(T^b)`,   the `k`-th **Floquet band**,

so that `spec(G^ab) = ⋃_k B_k`.  Each `B_k` is the continuous image of a connected space,
hence an interval.  Write `θ_1 ≥ … ≥ θ_n` for the roots of `μ_G`.

  **BAND.**   `θ_k ∈ B_k` for every `k`.

  **GAPCOUNT-ab.**  For `x ∉ spec(G^ab)`, `#{k : θ_k > x} = #{k : B_k ⊆ (x,∞)}`.

BAND implies GAPCOUNT-ab (`countAbove_eq_countBands`), and GAPCOUNT-ab implies
`Zeros(μ_G) ⊆ spec(G^ab)`, recovering `AbelianCover.root_mem_of_average` with the count
attached rather than only the containment.

## Why BAND is true

Two classical inputs, neither in Mathlib, both carried as hypotheses here.

1. Godsil–Gutman: `μ_G = E_s[χ_{A_s}]` over uniform `±1` edge signings.
2. Marcus–Spielman–Srivastava: those signings form an interlacing family.  The common
   interlacing lemma then gives, for **every** `k`, signings `s, s'` with
   `λ_k(A_s) ≤ θ_k ≤ λ_k(A_{s'})`.

Every signing is a point of `T^b`, so both bracketing values lie in `B_k`; `B_k` is an
interval; hence `θ_k ∈ B_k`.  That squeeze is `mem_of_squeezed`, proved below, and it is
the whole content once the two inputs are granted.

## What this does not give

The target is the **universal** cover, and the argument does not transfer.  It runs on
`spec(A_G(z)) ⊆ spec(G^ab)`, which holds because the `z` are one-dimensional unitary
representations of `F_b` and the abelian cover is assembled from exactly those.  The
analogous containment `spec(A_G(π)) ⊆ spec(T)` is **false** for a general unitary
representation `π` of `F_b`: the trivial representation returns `A_G` itself, whose top
eigenvalue exceeds `ρ(T)` already for `K_4`, where `3 > 2√2`.  Finite-dimensional
representations of a free group are not weakly contained in the regular representation.

So GAPCOUNT over the universal cover needs an input that is not a band decomposition.
That is now the isolated obstruction, and it is stated here rather than in prose.
-/

namespace BandTheorem

open Finset Set
open scoped Classical

/-! ## Bands are intervals -/

/-- The continuous image of a preconnected space in a linear order is order-connected.
Applied to `λ_k : T^b → ℝ` this says the `k`-th Floquet band is an interval. -/
theorem ordConnected_range_of_continuous {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {f : X → ℝ} (hf : Continuous f) :
    (Set.range f).OrdConnected := by
  have h : IsPreconnected (Set.range f) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image f hf.continuousOn
  exact h.ordConnected

/-- **The squeeze.**  A point bracketed by two members of an order-connected set, and hence
lying between them, belongs to the set.  This is how the two interlacing bounds place a
matching root inside its band. -/
theorem mem_of_squeezed {S : Set ℝ} (hS : S.OrdConnected) {lo hi θ : ℝ}
    (hlo : lo ∈ S) (hhi : hi ∈ S) (h1 : lo ≤ θ) (h2 : θ ≤ hi) : θ ∈ S :=
  hS.out hlo hhi ⟨h1, h2⟩

/-! ## Band membership forces the count -/

/-- **The assembly.**  If each root lies in its own band and the cut avoids every band, the
number of roots above the cut equals the number of bands above the cut.

The only step with content is the forward direction: a root above the cut cannot have its
band dip below, because the band is an interval containing both the root and that lower
point, and would then have to contain the cut. -/
theorem band_above_iff {n : ℕ} {θ : Fin n → ℝ} {B : Fin n → Set ℝ} {x : ℝ}
    (hmem : ∀ k, θ k ∈ B k) (hconn : ∀ k, (B k).OrdConnected)
    (hx : ∀ k, x ∉ B k) (k : Fin n) :
    x < θ k ↔ ∀ y ∈ B k, x < y := by
  constructor
  · intro hk y hy
    by_contra hcon
    push Not at hcon
    -- `y ≤ x < θ k`, both `y` and `θ k` in the band, so the band contains `x`
    have hxin : x ∈ B k := (hconn k).out hy (hmem k) ⟨hcon, le_of_lt hk⟩
    exact hx k hxin
  · intro h
    exact h (θ k) (hmem k)

/-- **GAPCOUNT-ab.**  Off `spec(G^ab)` the root count is the band count. -/
theorem countAbove_eq_countBands {n : ℕ} {θ : Fin n → ℝ} {B : Fin n → Set ℝ} {x : ℝ}
    (hmem : ∀ k, θ k ∈ B k) (hconn : ∀ k, (B k).OrdConnected) (hx : ∀ k, x ∉ B k) :
    (Finset.univ.filter (fun k => x < θ k)).card
      = (Finset.univ.filter (fun k => ∀ y ∈ B k, x < y)).card := by
  classical
  rw [Finset.filter_congr (fun k _ => band_above_iff hmem hconn hx k)]

/-- No root sits off `spec(G^ab)`: the containment `Zeros(μ_G) ⊆ spec(G^ab)`, recovered
from BAND rather than from the vanishing-average argument. -/
theorem root_mem_bands {n : ℕ} {θ : Fin n → ℝ} {B : Fin n → Set ℝ}
    (hmem : ∀ k, θ k ∈ B k) (k : Fin n) : θ k ∈ ⋃ j, B j :=
  Set.mem_iUnion.mpr ⟨k, hmem k⟩

/-- **Conjecture 10 wherever the abelian cover already exhausts the universal one.**

The hypothesis `B k ⊆ univSpec` says every Floquet band lies in `spec(T)`, which holds
exactly when `spec(G^ab) ⊆ spec(T)`.  For `b₁(G) = 1` the deck group is `F_1 = ℤ`, already
abelian, so `G^ab = T` and the hypothesis is automatic: BAND recovers the unicyclic case of
Conjecture 10, which the note proves by Floquet theory, and sharpens it to `θ_k ∈ B_k`.

The hypothesis fails as soon as `b₁ ≥ 2`.  For `K_4` the top band contains the Perron value
`3`, while `ρ(T) = 2√2 < 3`.  That failure is the whole distance still to be covered. -/
theorem conj10_of_bands_subset {n : ℕ} {θ : Fin n → ℝ} {B : Fin n → Set ℝ}
    {univSpec : Set ℝ} (hmem : ∀ k, θ k ∈ B k) (hsub : ∀ k, B k ⊆ univSpec) (k : Fin n) :
    θ k ∈ univSpec :=
  hsub k (hmem k)

/-! ## The theorem, with the two classical inputs visible -/

/-- **BAND, conditionally.**

`lam k z` is the `k`-th largest eigenvalue of `A_G(z)`, `Z` the parameter space `T^b`,
`sgn : S → Z` the inclusion of the `±1` signings, and `θ k` the `k`-th largest root of
`μ_G`.

* `hcont` is continuity of `lam k`, standard for ordered eigenvalues of a Hermitian family.
* `hsqueeze` is Godsil–Gutman together with Marcus–Spielman–Srivastava: the signings form
  an interlacing family averaging to `μ_G`, so the common interlacing lemma brackets every
  root of the average between two members, at every index `k`.  Neither is in Mathlib.

The conclusion is that each root lies in its band, and hence that the root count off
`spec(G^ab)` is the band count. -/
theorem band_of {n : ℕ} {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z]
    {S : Type*} (sgn : S → Z) {lam : Fin n → Z → ℝ} {θ : Fin n → ℝ}
    (hcont : ∀ k, Continuous (lam k))
    (hsqueeze : ∀ k, ∃ s s' : S, lam k (sgn s) ≤ θ k ∧ θ k ≤ lam k (sgn s')) :
    ∀ k, θ k ∈ Set.range (lam k) := by
  intro k
  obtain ⟨s, s', h1, h2⟩ := hsqueeze k
  exact mem_of_squeezed (ordConnected_range_of_continuous (hcont k))
    ⟨sgn s, rfl⟩ ⟨sgn s', rfl⟩ h1 h2

/-- **GAPCOUNT-ab, conditionally**, assembled from `band_of`. -/
theorem gapcount_ab_of {n : ℕ} {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z]
    {S : Type*} (sgn : S → Z) {lam : Fin n → Z → ℝ} {θ : Fin n → ℝ} {x : ℝ}
    (hcont : ∀ k, Continuous (lam k))
    (hsqueeze : ∀ k, ∃ s s' : S, lam k (sgn s) ≤ θ k ∧ θ k ≤ lam k (sgn s'))
    (hx : ∀ k, x ∉ Set.range (lam k)) :
    (Finset.univ.filter (fun k => x < θ k)).card
      = (Finset.univ.filter (fun k => ∀ y ∈ Set.range (lam k), x < y)).card :=
  countAbove_eq_countBands (band_of sgn hcont hsqueeze)
    (fun k => ordConnected_range_of_continuous (hcont k)) hx

end BandTheorem
