import Mathlib

/-!
# The bipartite matching polynomial under an asymmetric specialization

Mathlib has no matching polynomial, so this file gives a minimal self-contained one for bipartite
graphs, presented as a finite set of edges `E : Finset (α × β)`, and proves the identity that
characterizes the polynomials arising in the biregular gap problem.

Write `A` for the left side and `B` for the right side.  The multivariate matching polynomial of
Heilmann and Lieb, specialized at `x = y` on `A` and `x = 1` on `B`, is

  `bipF E y p = ∑_{M a matching} (-1)^|M| * y^(p - |M|)`,

and the main result `bipF_eq_sum_counts` is that this equals `∑_k (-1)^k m_k y^(p-k)`, where `m_k`
counts the `k`-matchings.  That identity is exactly the statement that the polynomial appearing in
the biregular problem is an asymmetric specialization of the multivariate matching polynomial.
-/

namespace BipartiteMatchingPoly

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A set of edges is a matching when no two share a left endpoint or a right endpoint. -/
def IsMatching (M : Finset (α × β)) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧ (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)

instance (M : Finset (α × β)) : Decidable (IsMatching M) := by
  unfold IsMatching; infer_instance

/-- The matchings contained in an edge set. -/
def matchings (E : Finset (α × β)) : Finset (Finset (α × β)) :=
  E.powerset.filter IsMatching

/-- The number of `k`-matchings. -/
def mCount (E : Finset (α × β)) (k : ℕ) : ℕ :=
  ((matchings E).filter (fun M => M.card = k)).card

variable {R : Type*} [CommRing R]

/-- The matching polynomial of a bipartite edge set, specialized to `y` on the left side and `1`
on the right: `∑_M (-1)^|M| y^(p - |M|)`. -/
def bipF (E : Finset (α × β)) (y : R) (p : ℕ) : R :=
  ∑ M ∈ matchings E, (-1 : R) ^ M.card * y ^ (p - M.card)

/-- **A4.** The asymmetric specialization of the multivariate matching polynomial is the
alternating generating function of the matching counts:
`bipF E y p = ∑_k (-1)^k m_k y^(p-k)`. -/
theorem bipF_eq_sum_counts (E : Finset (α × β)) (y : R) (p : ℕ)
    (hcard : ∀ M ∈ matchings E, M.card ≤ p) :
    bipF E y p = ∑ k ∈ Finset.range (p + 1), (-1 : R) ^ k * (mCount E k : R) * y ^ (p - k) := by
  classical
  unfold bipF
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun M : Finset (α × β) => M.card)
        (t := Finset.range (p + 1))
        (fun M hM => Finset.mem_range.mpr (Nat.lt_succ_of_le (hcard M hM)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ∀ M ∈ (matchings E).filter (fun M => M.card = k),
      (-1 : R) ^ M.card * y ^ (p - M.card) = (-1 : R) ^ k * y ^ (p - k) := by
    intro M hM
    rw [(Finset.mem_filter.mp hM).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, mCount, nsmul_eq_mul]
  ring

/-- `bipF` at `p = 0` on the empty edge set is `1`: the empty matching alone. -/
@[simp] theorem bipF_empty (y : R) (p : ℕ) :
    bipF (∅ : Finset (α × β)) y p = y ^ p := by
  unfold bipF matchings
  have : (∅ : Finset (α × β)).powerset.filter IsMatching = {∅} := by
    ext M; simp [IsMatching, Finset.mem_filter, Finset.mem_powerset]
    intro h; subst h; simp
  rw [this, Finset.sum_singleton]
  simp


/-! ## The deletion recursion (A5)

The combinatorial content of the asymmetric recursion is that the `(k+1)`-matchings of `E` split
according to how the left vertex `v` is covered: either it is uncovered, and the matching is a
`(k+1)`-matching of `E` with all `v`-edges deleted, or it uses a unique edge `(v,u)`, and deleting
that edge gives a `k`-matching of `E` with all `v`-edges and all `u`-edges deleted.
-/

/-- Edges of `E` not meeting the left vertex `v`. -/
def delL (E : Finset (α × β)) (v : α) : Finset (α × β) := E.filter (fun e => e.1 ≠ v)

/-- Edges of `E` meeting neither the left vertex `v` nor the right vertex `u`. -/
def delLR (E : Finset (α × β)) (v : α) (u : β) : Finset (α × β) :=
  E.filter (fun e => e.1 ≠ v ∧ e.2 ≠ u)

/-- The right endpoints available to `v`. -/
def nbrL (E : Finset (α × β)) (v : α) : Finset β :=
  (E.filter (fun e => e.1 = v)).image Prod.snd

lemma isMatching_of_subset {M N : Finset (α × β)} (hMN : M ⊆ N) (hN : IsMatching N) :
    IsMatching M :=
  ⟨fun e he f hf h => hN.1 e (hMN he) f (hMN hf) h,
   fun e he f hf h => hN.2 e (hMN he) f (hMN hf) h⟩

/-- A matching of `E` avoiding `v` is precisely a matching of `delL E v`. -/
lemma mem_matchings_delL {E : Finset (α × β)} {v : α} {M : Finset (α × β)} :
    M ∈ matchings (delL E v) ↔ M ∈ matchings E ∧ ∀ e ∈ M, e.1 ≠ v := by
  classical
  simp only [matchings, delL, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hM⟩
    refine ⟨⟨fun e he => (Finset.mem_filter.mp (hsub he)).1, hM⟩,
            fun e he => (Finset.mem_filter.mp (hsub he)).2⟩
  · rintro ⟨⟨hsub, hM⟩, hv⟩
    exact ⟨fun e he => Finset.mem_filter.mpr ⟨hsub he, hv e he⟩, hM⟩

/-- A matching of `E` avoiding `v` and `u` is precisely a matching of `delLR E v u`. -/
lemma mem_matchings_delLR {E : Finset (α × β)} {v : α} {u : β} {M : Finset (α × β)} :
    M ∈ matchings (delLR E v u) ↔ M ∈ matchings E ∧ ∀ e ∈ M, e.1 ≠ v ∧ e.2 ≠ u := by
  classical
  simp only [matchings, delLR, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hM⟩
    exact ⟨⟨fun e he => (Finset.mem_filter.mp (hsub he)).1, hM⟩,
           fun e he => (Finset.mem_filter.mp (hsub he)).2⟩
  · rintro ⟨⟨hsub, hM⟩, hvu⟩
    exact ⟨fun e he => Finset.mem_filter.mpr ⟨hsub he, hvu e he⟩, hM⟩


/-! `mCount_delete_left`, the deletion recursion (A5), is proved on paper but not
formalized: it needs the bijection between `(k+1)`-matchings using edge `(v,u)` and `k`-matchings
of the doubly-deleted edge set, which is a larger `Finset` argument than the fibering above. -/

end BipartiteMatchingPoly
