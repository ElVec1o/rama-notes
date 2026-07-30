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




/-- The empty matching is the only `0`-matching, so `m_0 = 1`. -/
lemma mCount_zero (E : Finset (α × β)) : mCount E 0 = 1 := by
  classical
  unfold mCount matchings
  have : (E.powerset.filter IsMatching).filter (fun M => M.card = 0) = {∅} := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, _⟩, h⟩; exact h
    · rintro rfl
      exact ⟨⟨Finset.empty_subset _, ⟨by simp, by simp⟩⟩, rfl⟩
  rw [this, Finset.card_singleton]

/-! The polynomial form of the recursion,
`bipF E y (p+1) = y * bipF (delL E v) y p - sum_u bipF (delLR E v u) y p`,
follows from `mCount_delete_left` and `bipF_eq_sum_counts` by separating the `k = 0` term and
reindexing.  In the `X^|M|` normalization that reindexing disappears entirely, and the recursion
is proved below as `bipQ_delete_left`; `bipP_eq_reverse_bipQ` records that the two normalizations
are reverses of one another. -/

/-! ## The subleading coefficient after the band-centre shift

For an `(a,b)`-biregular bipartite graph with parts of sizes `p ≤ q` and degree `a` on the
`p`-side, the polynomial `f_G` defined by `μ_G(x) = x^(q-p) f_G(x²)` is monic of degree `p` with
`[y^(p-1)] f_G = -|E| = -pa`.  Shifting by the band centre `c = (a-1)+(b-1)` gives
`[z^(p-1)] f_G(z+c) = p·c - pa = p(b-2)`.

This is exactly zero iff `b = 2`.  A matching polynomial of degree `p` has vanishing coefficient at
`p-1`, so `f_G(z+c)` can be a matching polynomial only when `b = 2` — which is the case where the
Yan–Yeh subdivision identity applies and the two-sided Heilmann–Lieb bound is available.  So the
boundary between the proved and the open case is not an artefact of the method.

Equivalently the roots of `f_G(z+c)` have mean `-(b-2)`: they are centred at the band centre
exactly when `b = 2`, and are skewed towards the lower band edge otherwise.
-/

section Subleading

open Polynomial

/-- Every singleton edge set is a matching, and these are all the matchings of size one, so the
number of `1`-matchings is the number of edges. -/
theorem mCount_one (E : Finset (α × β)) : mCount E 1 = E.card := by
  have hset : (matchings E).filter (fun M => M.card = 1)
      = E.image (fun e => ({e} : Finset (α × β))) := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_image, matchings, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hsub, _⟩, hcard⟩
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨e, hsub (Finset.mem_singleton_self e), rfl⟩
    · rintro ⟨e, he, rfl⟩
      refine ⟨⟨?_, ?_⟩, Finset.card_singleton e⟩
      · intro f hf; rw [Finset.mem_singleton] at hf; subst hf; exact he
      · exact ⟨fun x hx y hy _ => by
            rw [Finset.mem_singleton] at hx hy; rw [hx, hy],
          fun x hx y hy _ => by
            rw [Finset.mem_singleton] at hx hy; rw [hx, hy]⟩
  unfold mCount
  rw [hset, Finset.card_image_of_injective _ (fun x y h => by
    simpa using Finset.singleton_injective h)]

variable {R : Type*} [CommRing R]

/-- The polynomial form of `bipF`: `∑_k (-1)^k m_k X^(p-k)`. -/
noncomputable def bipP (E : Finset (α × β)) (p : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (p + 1), C ((-1 : R) ^ k * (mCount E k : R)) * X ^ (p - k)

theorem bipP_natDegree_le (E : Finset (α × β)) (p : ℕ) :
    (bipP (R := R) E p).natDegree ≤ p := by
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  simp only [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun k _ => ?_⟩
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  calc (p - k) * (X : R[X]).natDegree ≤ (p - k) * 1 :=
        Nat.mul_le_mul_left _ Polynomial.natDegree_X_le
    _ ≤ p := by omega

/-- The leading coefficient: `m_0 = 1`. -/
theorem bipP_coeff_self (E : Finset (α × β)) (p : ℕ) :
    (bipP (R := R) E p).coeff p = 1 := by
  unfold bipP
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp [mCount_zero]
  · intro k hk hk0
    have hne : p ≠ p - k := by
      have := Finset.mem_range.mp hk
      omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne]
    ring
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos p)) h

/-- The subleading coefficient: `-m_1 = -|E|`. -/
theorem bipP_coeff_pred (E : Finset (α × β)) {p : ℕ} (hp : 1 ≤ p) :
    (bipP (R := R) E p).coeff (p - 1) = -(E.card : R) := by
  unfold bipP
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 1]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mCount_one]
    ring
  · intro k hk hk1
    have hne : p - 1 ≠ p - k := by
      have := Finset.mem_range.mp hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · omega
      · omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne]
    ring
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The Taylor shift on the subleading coefficient.**  For any `f` of degree at most `p`,
the coefficient of `X^(p-1)` in `f(X + c)` is `f_{p-1} + p·f_p·c`. -/
theorem taylor_coeff_pred (f : R[X]) (c : R) {p : ℕ} (hp : 1 ≤ p)
    (hdeg : f.natDegree ≤ p) :
    (Polynomial.taylor c f).coeff (p - 1) = f.coeff (p - 1) + p * f.coeff p * c := by
  rw [Polynomial.taylor_coeff]
  have hH : Polynomial.hasseDeriv (p - 1) f
      = C (f.coeff (p - 1)) + C ((p : R) * f.coeff p) * X := by
    ext n
    rw [Polynomial.hasseDeriv_coeff]
    match n with
    | 0 => simp
    | 1 =>
      have h1 : 1 + (p - 1) = p := by omega
      have h2 : p.choose (p - 1) = p := by
        rw [show p - 1 = p - 1 from rfl, Nat.choose_symm (by omega : 1 ≤ p),
          Nat.choose_one_right]
      rw [h1, h2]; simp
    | (n + 2) =>
      have hz : f.coeff (n + 2 + (p - 1)) = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        omega
      rw [hz]
      simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
        Polynomial.coeff_X]
  rw [hH]
  simp [mul_comm]

/-- **The Taylor shift on the second subleading coefficient.**  For `f` of degree at most `p`,
the coefficient of `X^(p-2)` in `f(X + c)` is `f_{p-2} + (p-1)f_{p-1}c + C(p,2)f_p c^2`. -/
theorem taylor_coeff_pred_two (f : R[X]) (c : R) {p : ℕ} (hp : 2 ≤ p)
    (hdeg : f.natDegree ≤ p) :
    (Polynomial.taylor c f).coeff (p - 2)
      = f.coeff (p - 2) + (p - 1 : ℕ) * f.coeff (p - 1) * c
        + (p.choose 2 : ℕ) * f.coeff p * c ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 from rfl]
  rw [Polynomial.taylor_coeff]
  have hnd : (Polynomial.hasseDeriv k f).natDegree < 3 := by
    have h := Polynomial.natDegree_hasseDeriv_le f k
    omega
  rw [Polynomial.eval_eq_sum_range' hnd, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Polynomial.hasseDeriv_coeff, Nat.zero_add, Nat.choose_self]
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, Nat.choose_succ_self_right,
    show 2 + k = k + 2 from Nat.add_comm 2 k,
    show (k + 2).choose k = (k + 2).choose 2 by
      rw [← Nat.choose_symm (by omega : 2 ≤ k + 2), Nat.add_sub_cancel]]
  push_cast
  ring

/-- **A16.**  The second subleading coefficient of the shifted bipartite polynomial, in terms of
the number of `2`-matchings and the number of edges. -/
theorem bipP_taylor_coeff_pred_two (E : Finset (α × β)) (c : R) {p : ℕ} (hp : 2 ≤ p) :
    (Polynomial.taylor c (bipP (R := R) E p)).coeff (p - 2)
      = (mCount E 2 : R) - (p - 1 : ℕ) * (E.card : R) * c + (p.choose 2 : ℕ) * c ^ 2 := by
  have hd : (bipP (R := R) E p).natDegree ≤ p := bipP_natDegree_le E p
  have h2 : (bipP (R := R) E p).coeff (p - 2) = (mCount E 2 : R) := by
    unfold bipP
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 2]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]; ring
    · intro k hk hk2
      have hne : p - 2 ≠ p - k := by
        have := Finset.mem_range.mp hk
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> omega
        · omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne]; ring
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [taylor_coeff_pred_two _ _ hp hd, h2,
    bipP_coeff_pred E (by omega), bipP_coeff_self E p]
  ring

/-- **A15.**  For a bipartite graph whose polynomial is monic of degree `p` with `|E|` edges,
shifting by `c` moves the subleading coefficient to `p·c - |E|`. -/
theorem bipP_taylor_coeff_pred (E : Finset (α × β)) (c : R) {p : ℕ} (hp : 1 ≤ p) :
    (Polynomial.taylor c (bipP (R := R) E p)).coeff (p - 1) = p * c - (E.card : R) := by
  rw [taylor_coeff_pred _ _ hp (bipP_natDegree_le E p), bipP_coeff_pred E hp,
    bipP_coeff_self E p]
  ring

/-- **A15, biregular form.**  If the graph is `(a,b)`-biregular with `p` vertices of degree `a` on
the smaller side, so `|E| = p·a`, and `c = (a-1) + (b-1)` is the band centre, then the subleading
coefficient after the shift is exactly `p·(b-2)`.

It vanishes iff `b = 2` (in a ring where `p ≠ 0` is not a zero divisor).  Since a matching
polynomial of degree `p` has vanishing coefficient at `p-1`, the shifted polynomial can be a
matching polynomial only when `b = 2`. -/
theorem bipP_taylor_coeff_biregular (E : Finset (α × β)) {p a b : ℕ} (hp : 1 ≤ p) (hb : 1 ≤ b)
    (hcard : E.card = p * a) :
    (Polynomial.taylor (((a : R) - 1) + ((b : R) - 1)) (bipP (R := R) E p)).coeff (p - 1)
      = (p : R) * ((b : R) - 2) := by
  rw [bipP_taylor_coeff_pred _ _ hp, hcard]
  push_cast
  ring

end Subleading

/-! ## The deletion recursion in polynomial form

`bipP E p = ∑_k (-1)^k m_k X^(p-k)` carries a truncated natural subtraction in the exponent, which
makes every reindexing step awkward.  The *reversed* polynomial

  `bipQ E = ∑_M (-1)^|M| X^|M| = ∑_k (-1)^k m_k X^k`

has no subtraction at all: it is obtained from `bipP E p` by reversing the coefficient list, so no
information is lost.  In this form the combinatorial split of `mCount_delete_left` becomes a single
polynomial identity,

  `bipQ E = bipQ (E - v) - X * ∑_{u ∼ v} bipQ (E - v - u)`,

which is the deletion recursion for the bipartite matching polynomial.
-/

section Deletion

open Polynomial

variable {R : Type*} [CommRing R]

/-- The **reversed** bipartite matching polynomial `∑_M (-1)^|M| X^|M|`.  Its coefficient of `X^k`
is `(-1)^k m_k`, whereas `bipP E p` places that same coefficient on `X^(p-k)`. -/
noncomputable def bipQ (E : Finset (α × β)) : R[X] :=
  ∑ M ∈ matchings E, C ((-1 : R) ^ M.card) * X ^ M.card

/-- Card-free analogue of `covered_biUnion`: the matchings of `E` that cover the left vertex `v`
decompose according to the partner of `v`. -/
lemma covered_biUnion' (E : Finset (α × β)) (v : α) :
    (matchings E).filter (fun M => ¬ ∀ e ∈ M, e.1 ≠ v)
      = (nbrL E v).biUnion (fun u => (matchings E).filter (fun M => (v, u) ∈ M)) := by
  classical
  ext M
  simp only [Finset.mem_biUnion, Finset.mem_filter, not_forall]
  constructor
  · rintro ⟨hMm, e, he, hne⟩
    have hev : e = (v, e.2) := by
      rcases e with ⟨e1, e2⟩
      have : e1 = v := not_not.mp hne
      simp [this]
    have hsub : M ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hMm).1
    refine ⟨e.2, ?_, hMm, hev ▸ he⟩
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨hsub he, by rw [hev]⟩, rfl⟩
  · rintro ⟨u, _, hMm, hvu⟩
    exact ⟨hMm, (v, u), hvu, by simp⟩

/-- Card-free analogue of `covered_disjoint`: distinct partners give disjoint families. -/
lemma covered_disjoint' (E : Finset (α × β)) (v : α) :
    ∀ u ∈ nbrL E v, ∀ u' ∈ nbrL E v, u ≠ u' →
      Disjoint ((matchings E).filter (fun M => (v, u) ∈ M))
               ((matchings E).filter (fun M => (v, u') ∈ M)) := by
  classical
  intro u _ u' _ hne
  rw [Finset.disjoint_left]
  intro M hM hM'
  rw [Finset.mem_filter] at hM hM'
  have hMatch : IsMatching M := (Finset.mem_filter.mp hM.1).2
  exact hne (unique_partner hMatch hM.2 hM'.2)

/-- Polynomial analogue of `card_covered`: for an available partner `u`, deleting the edge `(v,u)`
is a bijection from the matchings of `E` using `(v,u)` onto the matchings of `delLR E v u`, and it
drops the degree by one.  Hence the contribution of the partner `u` is `-X * bipQ (delLR E v u)`. -/
lemma sum_covered_partner (E : Finset (α × β)) (v : α) (u : β) (hu : (v, u) ∈ E) :
    ∑ M ∈ (matchings E).filter (fun M => (v, u) ∈ M),
        C ((-1 : R) ^ M.card) * X ^ M.card
      = -(X * bipQ (R := R) (delLR E v u)) := by
  classical
  unfold bipQ
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij' (fun M _ => M.erase (v, u)) (fun N _ => insert (v, u) N)
    ?_ ?_ ?_ ?_ ?_
  · -- erase lands in the target
    intro M hM
    simp only [Finset.mem_filter] at hM
    obtain ⟨hMm, hvu⟩ := hM
    have hMatch : IsMatching M := (Finset.mem_filter.mp hMm).2
    have hsub : M ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hMm).1
    refine mem_matchings_delLR.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun e he => hsub (Finset.mem_of_mem_erase he)),
        isMatching_of_subset (Finset.erase_subset _ _) hMatch⟩
    · intro e he
      have hne : e ≠ (v, u) := Finset.ne_of_mem_erase he
      have heM : e ∈ M := Finset.mem_of_mem_erase he
      constructor
      · intro h1; exact hne (hMatch.1 e heM (v, u) hvu (by simpa using h1))
      · intro h2; exact hne (hMatch.2 e heM (v, u) hvu (by simpa using h2))
  · -- insert lands back
    intro N hN
    obtain ⟨hNE, hNavoid⟩ := mem_matchings_delLR.mp hN
    have hNMatch : IsMatching N := (Finset.mem_filter.mp hNE).2
    have hNsub : N ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hNE).1
    refine Finset.mem_filter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
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
  · -- the two maps are mutually inverse
    intro M hM
    exact Finset.insert_erase (Finset.mem_filter.mp hM).2
  · intro N hN
    obtain ⟨_, hNavoid⟩ := mem_matchings_delLR.mp hN
    exact Finset.erase_insert (fun h => (hNavoid _ h).1 rfl)
  · -- the summands agree: erasing an edge drops the degree by one and flips the sign
    intro M hM
    have hvu : (v, u) ∈ M := (Finset.mem_filter.mp hM).2
    have hc : M.card = (M.erase (v, u)).card + 1 := (Finset.card_erase_add_one hvu).symm
    rw [hc, pow_succ, pow_succ, map_mul, map_neg, map_one]
    ring

/-- **The deletion recursion.**  Splitting the matchings of `E` according to whether the left
vertex `v` is covered, and if so by which partner, gives
`bipQ E = bipQ (delL E v) - X * ∑_{u ∼ v} bipQ (delLR E v u)`.

This is the polynomial form of `mCount_delete_left`; because `bipQ` is the reverse of `bipP`, no
truncated subtraction appears. -/
theorem bipQ_delete_left (E : Finset (α × β)) (v : α) :
    bipQ (R := R) E = bipQ (delL E v) - X * ∑ u ∈ nbrL E v, bipQ (delLR E v u) := by
  classical
  have huncov : (matchings E).filter (fun M => ∀ e ∈ M, e.1 ≠ v) = matchings (delL E v) := by
    ext M
    simp only [Finset.mem_filter, mem_matchings_delL]
  have huncov' : (∑ M ∈ (matchings E).filter (fun M => ∀ e ∈ M, e.1 ≠ v),
        C ((-1 : R) ^ M.card) * X ^ M.card) = bipQ (R := R) (delL E v) := by
    unfold bipQ
    rw [huncov]
  have hdisj : Set.PairwiseDisjoint (↑(nbrL E v))
      (fun u => (matchings E).filter (fun M => (v, u) ∈ M)) := by
    intro u hu u' hu' hne
    exact covered_disjoint' E v u (Finset.mem_coe.mp hu) u' (Finset.mem_coe.mp hu') hne
  have hsplit : bipQ (R := R) E
      = (∑ M ∈ (matchings E).filter (fun M => ∀ e ∈ M, e.1 ≠ v),
            C ((-1 : R) ^ M.card) * X ^ M.card)
        + ∑ M ∈ (matchings E).filter (fun M => ¬ ∀ e ∈ M, e.1 ≠ v),
            C ((-1 : R) ^ M.card) * X ^ M.card :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcov : (∑ M ∈ (matchings E).filter (fun M => ¬ ∀ e ∈ M, e.1 ≠ v),
        C ((-1 : R) ^ M.card) * X ^ M.card)
      = ∑ u ∈ nbrL E v, -(X * bipQ (R := R) (delLR E v u)) := by
    rw [covered_biUnion' E v, Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl fun u hu => sum_covered_partner E v u (edge_of_mem_nbrL hu)
  rw [hsplit, hcov, huncov', Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- The coefficients of `bipQ` are the alternating matching counts: `[X^k] bipQ E = (-1)^k m_k`. -/
theorem bipQ_coeff (E : Finset (α × β)) (k : ℕ) :
    (bipQ (R := R) E).coeff k = (-1 : R) ^ k * (mCount E k : R) := by
  classical
  unfold bipQ mCount
  rw [Polynomial.finsetSum_coeff]
  have h : ∀ M ∈ matchings E,
      (C ((-1 : R) ^ M.card) * X ^ M.card).coeff k
        = if M.card = k then (-1 : R) ^ k else 0 := by
    intro M _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : M.card = k
    · subst h; simp
    · have h' : ¬ (k = M.card) := fun hh => h hh.symm
      simp [h, h']
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `bipQ` really is the reverse of `bipP`: reading the coefficients of `bipQ E` off in the
opposite order recovers `bipP E p`. -/
theorem bipP_eq_reverse_bipQ (E : Finset (α × β)) (p : ℕ) :
    bipP (R := R) E p
      = ∑ k ∈ Finset.range (p + 1), C ((bipQ (R := R) E).coeff k) * X ^ (p - k) := by
  unfold bipP
  exact Finset.sum_congr rfl fun k _ => by rw [bipQ_coeff]

/-- **The deletion recursion, evaluated form.**  The ordinary one-variable statement
`Q_E(y) = Q_{E-v}(y) - y * ∑_{u ∼ v} Q_{E-v-u}(y)`. -/
theorem bipQ_eval_delete_left (E : Finset (α × β)) (v : α) (y : R) :
    (bipQ (R := R) E).eval y
      = (bipQ (R := R) (delL E v)).eval y
        - y * ∑ u ∈ nbrL E v, (bipQ (R := R) (delLR E v u)).eval y := by
  rw [bipQ_delete_left (R := R) E v]
  simp [Polynomial.eval_finsetSum]

end Deletion

end BipartiteMatchingPoly
