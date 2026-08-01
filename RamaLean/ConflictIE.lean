import Mathlib

/-!
# Inclusion–exclusion for conflict-free subsets

Both paper 2 and paper 4 open their coefficient computations with the same identity: the
number of `k`-subsets of a finite set containing no *conflicting* pair is

  `m_k = ∑_{S ⊆ P} (-1)^{|S|} · C(N - |V(S)|, k - |V(S)|)`,                        (IE)

`P` the set of conflicting pairs, `V(S)` the elements involved in `S`, `N` the size of the
ground set.  For a graph with `conflict = shares an endpoint` this counts `k`-matchings,
and the first two terms are `C(N,k)` and `-p_2 C(N-2,k-2)` — exactly the expansion paper 4
runs, and the one `BipartiteMatchingPoly` runs in the bipartite case.

Nothing in the argument uses bipartiteness, or graphs at all: only that conflict is a
symmetric irreflexive relation on a finite type.  That is what is proved here, so that
both papers rest on one statement rather than two.

The proof is three steps.  `freeIndicator_eq_alt_sum` is the sign-cancellation: over the
subsets of the conflicting pairs *inside* `T`, the alternating sum of `(-1)^{|S|}` is `1`
when `T` is free and `0` otherwise, which is Mathlib's
`Finset.sum_powerset_neg_one_pow_card`.  Substituting it into the count and exchanging the
two summations is `mCount_eq_ie`, which needs that conflict is intrinsic to a pair, so the
inner index set depends on the outer one only through a containment.  The weight is then a
binomial coefficient, by the bijection between the `k`-subsets containing a fixed `V` and
the `(k-|V|)`-subsets of the complement.
-/

namespace ConflictIE

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]
variable (cf : E → E → Prop) [DecidableRel cf]

/-- A finite set is *free* when it contains no conflicting pair. -/
def IsFree (T : Finset E) : Prop := ∀ e ∈ T, ∀ f ∈ T, cf e f → False

instance (T : Finset E) : Decidable (IsFree cf T) := by
  unfold IsFree; infer_instance

/-- The conflicting pairs inside `T`, as ordered pairs. -/
def pairsIn (T : Finset E) : Finset (E × E) :=
  (T ×ˢ T).filter (fun p => cf p.1 p.2)

/-- All conflicting pairs of the ground set. -/
def allPairs : Finset (E × E) := (univ ×ˢ univ).filter (fun p => cf p.1 p.2)

/-- The elements involved in a set of pairs. -/
def endpoints (S : Finset (E × E)) : Finset E := S.image Prod.fst ∪ S.image Prod.snd

@[simp] theorem endpoints_empty : endpoints (∅ : Finset (E × E)) = ∅ := by
  simp [endpoints]

theorem pairsIn_eq_empty_iff (T : Finset E) : pairsIn cf T = ∅ ↔ IsFree cf T := by
  constructor
  · intro h e he f hf hcf
    have : (e, f) ∈ pairsIn cf T := by
      simp [pairsIn, mem_filter, mem_product, he, hf, hcf]
    rw [h] at this
    exact absurd this (notMem_empty _)
  · intro h
    ext p
    simp only [pairsIn, mem_filter, mem_product, notMem_empty, iff_false, not_and]
    intro hp hcf
    exact h p.1 hp.1 p.2 hp.2 hcf

/-- **The sign cancellation.**  Summing `(-1)^{|S|}` over the subsets of the conflicting
pairs inside `T` gives `1` exactly when `T` is free. -/
theorem freeIndicator_eq_alt_sum (T : Finset E) :
    (∑ S ∈ (pairsIn cf T).powerset, (-1 : ℤ) ^ S.card)
      = if IsFree cf T then 1 else 0 := by
  rw [Finset.sum_powerset_neg_one_pow_card]
  by_cases h : IsFree cf T
  · rw [if_pos ((pairsIn_eq_empty_iff cf T).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((pairsIn_eq_empty_iff cf T).mp hc)), if_neg h]

/-- The number of free `k`-subsets. -/
def mCount (k : ℕ) : ℕ :=
  ((univ.powersetCard k).filter (IsFree cf)).card

/-- **The count as an alternating double sum.** -/
theorem mCount_eq_double_sum (k : ℕ) :
    (mCount cf k : ℤ)
      = ∑ T ∈ univ.powersetCard k, ∑ S ∈ (pairsIn cf T).powerset, (-1 : ℤ) ^ S.card := by
  rw [Finset.sum_congr rfl fun T _ => freeIndicator_eq_alt_sum cf T, Finset.sum_boole]
  rfl

/-- A set of pairs lies inside `T` exactly when all its endpoints do. -/
theorem mem_powerset_pairsIn_iff {T : Finset E} {S : Finset (E × E)} :
    S ∈ (pairsIn cf T).powerset ↔ S ∈ (allPairs cf).powerset ∧ endpoints S ⊆ T := by
  simp only [Finset.mem_powerset]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, ?_⟩
    · have hmem := h hp
      simp only [pairsIn, mem_filter, mem_product] at hmem
      simp only [allPairs, mem_filter, mem_product, mem_univ, true_and]
      exact hmem.2
    · intro e he
      simp only [endpoints, mem_union, mem_image] at he
      rcases he with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
      · have hmem := h hp
        simp only [pairsIn, mem_filter, mem_product] at hmem
        exact hmem.1.1
      · have hmem := h hp
        simp only [pairsIn, mem_filter, mem_product] at hmem
        exact hmem.1.2
  · rintro ⟨hS, hV⟩ p hp
    have h1 : p.1 ∈ T := hV (mem_union_left _ (mem_image_of_mem _ hp))
    have h2 : p.2 ∈ T := hV (mem_union_right _ (mem_image_of_mem _ hp))
    have hmem := hS hp
    simp only [allPairs, mem_filter, mem_product] at hmem
    simp only [pairsIn, mem_filter, mem_product]
    exact ⟨⟨h1, h2⟩, hmem.2⟩

/-- The inner index set, rewritten as a filter of a fixed set. -/
theorem pairsIn_powerset_eq (T : Finset E) :
    (pairsIn cf T).powerset
      = (allPairs cf).powerset.filter (fun S => endpoints S ⊆ T) := by
  ext S
  rw [mem_powerset_pairsIn_iff, Finset.mem_filter]

/-- **Inclusion–exclusion.**  The two summations exchange, and the inner count is the
number of `k`-subsets containing every endpoint of `S`. -/
theorem mCount_eq_ie (k : ℕ) :
    (mCount cf k : ℤ)
      = ∑ S ∈ (allPairs cf).powerset, (-1 : ℤ) ^ S.card
          * ((univ.powersetCard k).filter (fun T => endpoints S ⊆ T)).card := by
  rw [mCount_eq_double_sum]
  have step : ∀ T ∈ univ.powersetCard k,
      (∑ S ∈ (pairsIn cf T).powerset, (-1 : ℤ) ^ S.card)
        = ∑ S ∈ (allPairs cf).powerset,
            (if endpoints S ⊆ T then (-1 : ℤ) ^ S.card else 0) := by
    intro T _
    rw [pairsIn_powerset_eq, Finset.sum_filter]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_zero, add_zero,
    nsmul_eq_mul, mul_comm]

end ConflictIE
