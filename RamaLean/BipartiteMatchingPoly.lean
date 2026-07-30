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



/-- In a matching, a left vertex is covered at most once. -/
lemma unique_partner {M : Finset (α × β)} (hM : IsMatching M) {v : α} {u u' : β}
    (h : (v, u) ∈ M) (h' : (v, u') ∈ M) : u = u' := by
  have h2 := hM.1 (v, u) h (v, u') h' rfl
  exact congrArg Prod.snd h2

/-- **Uncovered part.** The `(k+1)`-matchings of `E` avoiding `v` are the `(k+1)`-matchings of
`delL E v`. -/
lemma card_uncovered (E : Finset (α × β)) (v : α) (m : ℕ) :
    (((matchings E).filter (fun M => M.card = m)).filter
        (fun M => ∀ e ∈ M, e.1 ≠ v)).card = mCount (delL E v) m := by
  classical
  unfold mCount
  congr 1
  ext M
  simp only [Finset.mem_filter, mem_matchings_delL]
  tauto

/-- **Covered part.** For an available partner `u`, the `(k+1)`-matchings of `E` using `(v,u)`
correspond to the `k`-matchings of `delLR E v u`, by deleting the edge. -/
lemma card_covered (E : Finset (α × β)) (v : α) (u : β) (hu : (v, u) ∈ E) (k : ℕ) :
    (((matchings E).filter (fun M => M.card = k + 1)).filter
        (fun M => (v, u) ∈ M)).card = mCount (delLR E v u) k := by
  classical
  unfold mCount
  refine Finset.card_bij' (fun M _ => M.erase (v, u)) (fun N _ => insert (v, u) N) ?_ ?_ ?_ ?_
  · -- erase lands in the target
    intro M hM
    simp only [Finset.mem_filter] at hM
    obtain ⟨⟨hMm, hcard⟩, hvu⟩ := hM
    have hMatch : IsMatching M := (Finset.mem_filter.mp hMm).2
    have hsub : M ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hMm).1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_matchings_delLR.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (fun e he => hsub (Finset.mem_of_mem_erase he)),
          isMatching_of_subset (Finset.erase_subset _ _) hMatch⟩
      · intro e he
        have hne : e ≠ (v, u) := Finset.ne_of_mem_erase he
        have heM : e ∈ M := Finset.mem_of_mem_erase he
        constructor
        · intro h1; exact hne (hMatch.1 e heM (v, u) hvu (by simpa using h1))
        · intro h2; exact hne (hMatch.2 e heM (v, u) hvu (by simpa using h2))
    · rw [Finset.card_erase_of_mem hvu, hcard]; rfl
  · -- insert lands back
    intro N hN
    simp only [Finset.mem_filter] at hN
    obtain ⟨hNm, hcard⟩ := hN
    obtain ⟨hNE, hNavoid⟩ := mem_matchings_delLR.mp hNm
    have hNMatch : IsMatching N := (Finset.mem_filter.mp hNE).2
    have hNsub : N ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hNE).1
    have hnotmem : (v, u) ∉ N := fun h => (hNavoid _ h).1 rfl
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact hu
        · exact hNsub he'
      · constructor
        · intro e he f hf hef
          rcases Finset.mem_insert.mp he with rfl | he' <;>
            rcases Finset.mem_insert.mp hf with rfl | hf'
          · rfl
          · exact absurd hef.symm (hNavoid f hf').1
          · exact absurd hef (hNavoid e he').1
          · exact hNMatch.1 e he' f hf' hef
        · intro e he f hf hef
          rcases Finset.mem_insert.mp he with rfl | he' <;>
            rcases Finset.mem_insert.mp hf with rfl | hf'
          · rfl
          · exact absurd hef.symm (hNavoid f hf').2
          · exact absurd hef (hNavoid e he').2
          · exact hNMatch.2 e he' f hf' hef
    · rw [Finset.card_insert_of_notMem hnotmem, hcard]
    · exact Finset.mem_insert_self _ _
  · intro M hM
    simp only [Finset.mem_filter] at hM
    exact Finset.insert_erase hM.2
  · intro N hN
    simp only [Finset.mem_filter] at hN
    obtain ⟨hNm, _⟩ := hN
    obtain ⟨_, hNavoid⟩ := mem_matchings_delLR.mp hNm
    exact Finset.erase_insert (fun h => (hNavoid _ h).1 rfl)


/-- The covered `(k+1)`-matchings decompose over the partner of `v`. -/
lemma covered_biUnion (E : Finset (α × β)) (v : α) (m : ℕ) :
    ((matchings E).filter (fun M => M.card = m)).filter (fun M => ¬ ∀ e ∈ M, e.1 ≠ v)
      = (nbrL E v).biUnion
          (fun u => ((matchings E).filter (fun M => M.card = m)).filter (fun M => (v, u) ∈ M)) := by
  classical
  ext M
  simp only [Finset.mem_biUnion, Finset.mem_filter, not_forall]
  constructor
  · rintro ⟨⟨hMm, hc⟩, e, he, hne⟩
    have hev : e = (v, e.2) := by
      rcases e with ⟨e1, e2⟩
      have : e1 = v := not_not.mp hne
      simp [this]
    have hsub : M ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hMm).1
    refine ⟨e.2, ?_, ⟨hMm, hc⟩, hev ▸ he⟩
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨hsub he, by rw [hev]⟩, rfl⟩
  · rintro ⟨u, _, ⟨hMm, hc⟩, hvu⟩
    exact ⟨⟨hMm, hc⟩, (v, u), hvu, by simp⟩

/-- Distinct partners give disjoint families. -/
lemma covered_disjoint (E : Finset (α × β)) (v : α) (m : ℕ) :
    ∀ u ∈ nbrL E v, ∀ u' ∈ nbrL E v, u ≠ u' →
      Disjoint (((matchings E).filter (fun M => M.card = m)).filter (fun M => (v, u) ∈ M))
               (((matchings E).filter (fun M => M.card = m)).filter (fun M => (v, u') ∈ M)) := by
  classical
  intro u _ u' _ hne
  rw [Finset.disjoint_left]
  intro M hM hM'
  rw [Finset.mem_filter] at hM hM'
  have hMatch : IsMatching M := (Finset.mem_filter.mp (Finset.mem_filter.mp hM.1).1).2
  exact hne (unique_partner hMatch hM.2 hM'.2)

/-- Every available partner really is an edge. -/
lemma edge_of_mem_nbrL {E : Finset (α × β)} {v : α} {u : β} (hu : u ∈ nbrL E v) : (v, u) ∈ E := by
  classical
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨heE, hev⟩ := Finset.mem_filter.mp he
  have heq : (v, e.2) = e := Prod.ext_iff.mpr ⟨hev.symm, rfl⟩
  rw [heq]; exact heE

/-- **A5, count form.** The `(k+1)`-matchings of `E` split by how the left vertex `v` is covered. -/
theorem mCount_delete_left (E : Finset (α × β)) (v : α) (k : ℕ) :
    mCount E (k + 1)
      = mCount (delL E v) (k + 1) + ∑ u ∈ nbrL E v, mCount (delLR E v u) k := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (matchings E).filter (fun M => M.card = k + 1))
    (p := fun M => ∀ e ∈ M, e.1 ≠ v)
  have hcov : (((matchings E).filter (fun M => M.card = k + 1)).filter
        (fun M => ¬ ∀ e ∈ M, e.1 ≠ v)).card = ∑ u ∈ nbrL E v, mCount (delLR E v u) k := by
    rw [covered_biUnion E v (k + 1), Finset.card_biUnion (covered_disjoint E v (k + 1))]
    exact Finset.sum_congr rfl fun u hu => card_covered E v u (edge_of_mem_nbrL hu) k
  have huncov := card_uncovered E v (k + 1)
  calc mCount E (k + 1)
      = (((matchings E).filter (fun M => M.card = k + 1)).filter
            (fun M => ∀ e ∈ M, e.1 ≠ v)).card
        + (((matchings E).filter (fun M => M.card = k + 1)).filter
            (fun M => ¬ ∀ e ∈ M, e.1 ≠ v)).card := by
        rw [hsplit]; rfl
    _ = mCount (delL E v) (k + 1) + ∑ u ∈ nbrL E v, mCount (delLR E v u) k := by
        rw [huncov, hcov]



end BipartiteMatchingPoly
