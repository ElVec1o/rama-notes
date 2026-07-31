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

/-- **The Taylor shift, in general.**  For `f` of degree at most `p` and any `j ≤ p`, the
coefficient of `X^j` in `f(X + c)` is `∑_i C(i+j, j) f_{i+j} c^i`.  Specializing `j = p-1`,
`j = p-2` and `j = p-4` recovers the individual coefficient formulas; the last is the shift step
used in the `4`-cycle theorem. -/
theorem taylor_coeff_of_natDegree_le (f : R[X]) (c : R) {p j : ℕ} (hj : j ≤ p)
    (hdeg : f.natDegree ≤ p) :
    (Polynomial.taylor c f).coeff j
      = ∑ i ∈ Finset.range (p + 1 - j), ((i + j).choose j : ℕ) * f.coeff (i + j) * c ^ i := by
  rw [Polynomial.taylor_coeff]
  have hnd : (Polynomial.hasseDeriv j f).natDegree < p + 1 - j := by
    have h := Polynomial.natDegree_hasseDeriv_le f j
    omega
  rw [Polynomial.eval_eq_sum_range' hnd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.hasseDeriv_coeff]

/-- The `j = p-4` case, written as the five-term sum in the matching counts.  This is the shift
step of the `4`-cycle theorem: with `f` the polynomial whose `X^(p-k)` coefficient is
`(-1)^k m_k`, the coefficient of `z^(p-4)` in `f(z+c)` is
`∑_{k≤4} (-1)^k C(p-k, p-4) m_k c^(4-k)`. -/
theorem taylor_coeff_sub_four (f : R[X]) (c : R) {p : ℕ} (hp : 4 ≤ p)
    (hdeg : f.natDegree ≤ p) :
    (Polynomial.taylor c f).coeff (p - 4)
      = ∑ i ∈ Finset.range 5,
          ((i + (p - 4)).choose (p - 4) : ℕ) * f.coeff (i + (p - 4)) * c ^ i := by
  have h := taylor_coeff_of_natDegree_le f c (by omega : p - 4 ≤ p) hdeg
  rwa [show p + 1 - (p - 4) = 5 by omega] at h

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

/-! ## Counting the `2`-matchings

`mCount_zero` and `mCount_one` evaluate `m_0` and `m_1`; this section does `m_2`, which is the last
coefficient that the earlier results consume as an input rather than produce.

The count is easiest through *ordered* pairs of distinct edges, of which there are `|E|(|E|-1)`.
Such a pair either shares its left endpoint (`confL`), or shares its right endpoint (`confR`), or
neither, in which case the two edges form a `2`-matching (`ordMatch`).  The three cases are
exhaustive and mutually exclusive: in a bipartite edge set two edges agreeing in both coordinates
are equal, so `confL` and `confR` are disjoint.  Since every `2`-matching arises from exactly two
ordered pairs, this gives the degree-free identity

  `2 m_2 + |confL| + |confR| = |E| (|E| - 1)`

(`two_mul_mCount_two_add_conflicts`).  No regularity is assumed anywhere.

`card_confL` and `card_confR` then evaluate the two conflict counts as degree sums,
`|confL| = ∑_v d(v)(d(v)-1)`, which is what specializes.  For an `(a,b)`-biregular graph with `p`
vertices of degree `a` on the left and `q` of degree `b` on the right, the two sums collapse to
`p·a·(a-1)` and `q·b·(b-1)`, and with `|E| = pa = qb` the identity reads

  `2 m_2 = pa(pa - 1) - pa(a - 1) - qb(b - 1) = pa(pa - a - b + 1)`,

i.e. `m_2 = (pa/2)(pa - a - b + 1)`.  That is precisely the `m_2` appearing in the coefficient
theorems above — `bipP_taylor_coeff_pred_two` and the shifted `4`-cycle coefficient — which take
`mCount E 2` as an abstract input.  So this section is what connects those statements to the
degrees of the graph.
-/

section TwoMatchings

/-- Ordered pairs of distinct edges sharing their left endpoint. -/
def confL (E : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  E.offDiag.filter (fun q => q.1.1 = q.2.1)

/-- Ordered pairs of distinct edges sharing their right endpoint. -/
def confR (E : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  E.offDiag.filter (fun q => q.1.2 = q.2.2)

/-- Ordered pairs of distinct edges sharing neither endpoint: the ordered `2`-matchings. -/
def ordMatch (E : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  E.offDiag.filter (fun q => q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2)

/-- Two distinct edges cannot share both endpoints, so the two conflict types are exclusive. -/
lemma confL_disjoint_confR (E : Finset (α × β)) : Disjoint (confL E) (confR E) := by
  classical
  rw [Finset.disjoint_left]
  rintro q hL hR
  rw [confL, Finset.mem_filter] at hL
  rw [confR, Finset.mem_filter] at hR
  have hne : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hL.1).2.2
  exact hne (Prod.ext hL.2 hR.2)

/-- Natural-subtraction bookkeeping for `Finset.offDiag_card`: the off-diagonal of an `n`-element
set has `n(n-1)` elements. -/
lemma card_offDiag_mul_pred {γ : Type*} [DecidableEq γ] (s : Finset γ) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  cases hn : s.card with
  | zero => simp
  | succ n => simp [Nat.mul_succ]

/-- **The three-way split.**  `ordMatch`, `confL` and `confR` partition the ordered pairs of
distinct edges. -/
lemma card_ordMatch_add_conflicts (E : Finset (α × β)) :
    (ordMatch E).card + (confL E).card + (confR E).card = E.card * (E.card - 1) := by
  classical
  have hsplit : E.offDiag = ordMatch E ∪ (confL E ∪ confR E) := by
    ext q
    simp only [ordMatch, confL, confR, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      by_cases h1 : q.1.1 = q.2.1
      · exact Or.inr (Or.inl ⟨hq, h1⟩)
      · by_cases h2 : q.1.2 = q.2.2
        · exact Or.inr (Or.inr ⟨hq, h2⟩)
        · exact Or.inl ⟨hq, h1, h2⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  have hdisj : Disjoint (ordMatch E) (confL E ∪ confR E) := by
    rw [Finset.disjoint_left]
    rintro q hq hmem
    rw [ordMatch, Finset.mem_filter] at hq
    rcases Finset.mem_union.mp hmem with h | h
    · exact hq.2.1 (Finset.mem_filter.mp h).2
    · exact hq.2.2 (Finset.mem_filter.mp h).2
  have hcard : E.offDiag.card = (ordMatch E).card + ((confL E).card + (confR E).card) := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_union_of_disjoint (confL_disjoint_confR E)]
  rw [card_offDiag_mul_pred] at hcard
  omega

/-- **The fibres are pairs.**  A `2`-matching `M` is hit by exactly the two orderings of its two
edges, so the fibre of `q ↦ {q.1, q.2}` over `M` has two elements. -/
lemma card_ordMatch_fiber (E : Finset (α × β)) {M : Finset (α × β)}
    (hM : M ∈ (matchings E).filter (fun M => M.card = 2)) :
    ((ordMatch E).filter (fun q => ({q.1, q.2} : Finset (α × β)) = M)).card = 2 := by
  classical
  rw [Finset.mem_filter] at hM
  obtain ⟨hMm, hMcard⟩ := hM
  have hMatch : IsMatching M := (Finset.mem_filter.mp hMm).2
  have hsub : M ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hMm).1
  obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hMcard
  have heE : e ∈ E := hsub (by simp)
  have hfE : f ∈ E := hsub (by simp)
  have h1 : e.1 ≠ f.1 := fun h => hef (hMatch.1 e (by simp) f (by simp) h)
  have h2 : e.2 ≠ f.2 := fun h => hef (hMatch.2 e (by simp) f (by simp) h)
  have hset : (ordMatch E).filter (fun q => ({q.1, q.2} : Finset (α × β)) = {e, f})
      = {(e, f), (f, e)} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, ordMatch,
      Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨_, _, hqne⟩, _, _⟩, hq⟩
      have hq1 : q.1 = e ∨ q.1 = f := by
        have : q.1 ∈ ({e, f} : Finset (α × β)) := hq ▸ (by simp)
        simpa using this
      have hq2 : q.2 = e ∨ q.2 = f := by
        have : q.2 ∈ ({e, f} : Finset (α × β)) := hq ▸ (by simp)
        simpa using this
      rcases hq1 with h | h <;> rcases hq2 with h' | h'
      · exact absurd (h.trans h'.symm) hqne
      · exact Or.inl (Prod.ext h h')
      · exact Or.inr (Prod.ext h h')
      · exact absurd (h.trans h'.symm) hqne
    · rintro (rfl | rfl)
      · exact ⟨⟨⟨heE, hfE, hef⟩, h1, h2⟩, rfl⟩
      · exact ⟨⟨⟨hfE, heE, hef.symm⟩, h1.symm, h2.symm⟩, Finset.pair_comm f e⟩
  have hne : ((e, f) : (α × β) × (α × β)) ≠ (f, e) := fun h => hef (congrArg Prod.fst h)
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- Ordered `2`-matchings are counted with multiplicity two by the unordered ones. -/
lemma card_ordMatch (E : Finset (α × β)) : (ordMatch E).card = 2 * mCount E 2 := by
  classical
  have hmaps : ∀ q ∈ ordMatch E,
      ({q.1, q.2} : Finset (α × β)) ∈ (matchings E).filter (fun M => M.card = 2) := by
    intro q hq
    rw [ordMatch, Finset.mem_filter, Finset.mem_offDiag] at hq
    obtain ⟨⟨h1E, h2E, hne⟩, hf, hs⟩ := hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h1E
      · rw [Finset.mem_singleton] at hx; exact hx ▸ h2E
    · intro x hx y hy h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact absurd h hf
      · exact absurd h.symm hf
      · rfl
    · intro x hx y hy h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact absurd h hs
      · exact absurd h.symm hs
      · rfl
    · rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun q : (α × β) × (α × β) => ({q.1, q.2} : Finset (α × β)))
    (fun q hq => hmaps q hq)]
  rw [Finset.sum_congr rfl (fun M hM => card_ordMatch_fiber E hM)]
  rw [Finset.sum_const, smul_eq_mul, mCount]
  ring

/-- **The `2`-matching count, degree-free.**  Ordered pairs of distinct edges are counted in two
ways: `|E|(|E|-1)` of them altogether, and separately as the ordered `2`-matchings (two per
`2`-matching) plus the two kinds of conflicting pair. -/
theorem two_mul_mCount_two_add_conflicts (E : Finset (α × β)) :
    2 * mCount E 2 + (confL E).card + (confR E).card = E.card * (E.card - 1) := by
  rw [← card_ordMatch]
  exact card_ordMatch_add_conflicts E

/-- The left degree of a vertex: the number of edges at `v`. -/
def dL (E : Finset (α × β)) (v : α) : ℕ := (E.filter (fun e => e.1 = v)).card

/-- The right degree of a vertex: the number of edges at `u`. -/
def dR (E : Finset (α × β)) (u : β) : ℕ := (E.filter (fun e => e.2 = u)).card

/-- **The left conflicts as a degree sum.**  Fibring over the shared left endpoint, the fibre at
`v` is the off-diagonal of the edges at `v`. -/
theorem card_confL (E : Finset (α × β)) :
    (confL E).card = ∑ v ∈ E.image Prod.fst, dL E v * (dL E v - 1) := by
  classical
  have hmaps : ∀ q ∈ confL E, q.1.1 ∈ E.image Prod.fst := by
    intro q hq
    rw [confL, Finset.mem_filter, Finset.mem_offDiag] at hq
    exact Finset.mem_image.mpr ⟨q.1, hq.1.1, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun q : (α × β) × (α × β) => q.1.1) (fun q hq => hmaps q hq)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : (confL E).filter (fun q => q.1.1 = v)
      = (E.filter (fun e => e.1 = v)).offDiag := by
    ext q
    simp only [confL, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨h1, h2, hne⟩, heq⟩, hv⟩
      exact ⟨⟨h1, hv⟩, ⟨h2, heq ▸ hv⟩, hne⟩
    · rintro ⟨⟨h1, hv1⟩, ⟨h2, hv2⟩, hne⟩
      exact ⟨⟨⟨h1, h2, hne⟩, hv1.trans hv2.symm⟩, hv1⟩
  rw [hfib, card_offDiag_mul_pred, dL]

/-- **The right conflicts as a degree sum**, the mirror image of `card_confL`. -/
theorem card_confR (E : Finset (α × β)) :
    (confR E).card = ∑ u ∈ E.image Prod.snd, dR E u * (dR E u - 1) := by
  classical
  have hmaps : ∀ q ∈ confR E, q.1.2 ∈ E.image Prod.snd := by
    intro q hq
    rw [confR, Finset.mem_filter, Finset.mem_offDiag] at hq
    exact Finset.mem_image.mpr ⟨q.1, hq.1.1, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun q : (α × β) × (α × β) => q.1.2) (fun q hq => hmaps q hq)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hfib : (confR E).filter (fun q => q.1.2 = u)
      = (E.filter (fun e => e.2 = u)).offDiag := by
    ext q
    simp only [confR, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨h1, h2, hne⟩, heq⟩, hu⟩
      exact ⟨⟨h1, hu⟩, ⟨h2, heq ▸ hu⟩, hne⟩
    · rintro ⟨⟨h1, hu1⟩, ⟨h2, hu2⟩, hne⟩
      exact ⟨⟨⟨h1, h2, hne⟩, hu1.trans hu2.symm⟩, hu1⟩
  rw [hfib, card_offDiag_mul_pred, dR]

end TwoMatchings

/-! ## Why `m_3` cannot see the graph

The counts `m_k` are the numbers of independent `k`-sets of the conflict graph `L`, whose
vertices are the edges of `G` and whose adjacency is "shares an endpoint".  For `m_3` the
inclusion–exclusion expansion needs the numbers of edges, of `2`-edge paths and of triangles of
`L`.  The first two are determined by the degree sequence of `L`, and `conflict_degree` below
shows that degree is `(d_left - 1) + (d_right - 1)`, so for a biregular graph it is the constant
`c = (a-1) + (b-1)`.

The triangles are where bipartiteness enters, and `three_meeting_share` is the reason: three
edges of a bipartite graph that pairwise meet must all pass through one vertex, since otherwise
they would form a triangle in `G`.  So the triangles of `L` are exactly the triples inside a
single star, and their number is `p*C(a,3) + q*C(b,3)` — again a function of the parameters only.
Hence `m_3`, and with it the coefficient of `z^(p-3)`, does not depend on `G`.
-/

section ConflictGraph

/-- Two distinct edges of a bipartite graph conflict when they share an endpoint. -/
def Conflict (e f : α × β) : Prop := e.1 = f.1 ∨ e.2 = f.2

instance (e : α × β) : DecidablePred (Conflict e) := fun _ => by
  unfold Conflict; infer_instance

/-- Distinct edges cannot share both endpoints. -/
theorem not_both_of_ne {e f : α × β} (h : e ≠ f) : ¬(e.1 = f.1 ∧ e.2 = f.2) := by
  rintro ⟨h1, h2⟩
  exact h (Prod.ext h1 h2)

/-- **Three pairwise-meeting edges of a bipartite graph share a vertex.**

This is the step that uses bipartiteness.  In a general graph three edges can meet pairwise at
three distinct vertices, forming a triangle; in a bipartite graph they cannot, so a triangle of
the conflict graph is always a triple of edges through one vertex. -/
theorem three_meeting_share {e f g : α × β}
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (mef : Conflict e f) (mfg : Conflict f g) (meg : Conflict e g) :
    (e.1 = f.1 ∧ f.1 = g.1) ∨ (e.2 = f.2 ∧ f.2 = g.2) := by
  unfold Conflict at mef mfg meg
  rcases mef with h1 | h1
  · rcases mfg with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · -- e,f share the left vertex and f,g share the right: then e and g cannot meet
      rcases meg with h3 | h3
      · -- e.1 = g.1 = f.1, so f and g share both coordinates
        exact absurd ⟨h1 ▸ h3, h2⟩ (not_both_of_ne hfg)
      · -- e.2 = g.2 = f.2, so e and f share both coordinates
        exact absurd ⟨h1, h2 ▸ h3⟩ (not_both_of_ne hef)
  · rcases mfg with h2 | h2
    · -- e,f share the right vertex and f,g share the left: then e and g cannot meet
      rcases meg with h3 | h3
      · -- e.1 = g.1 = f.1, so e and f share both coordinates
        exact absurd ⟨h3.trans h2.symm, h1⟩ (not_both_of_ne hef)
      · -- e.2 = g.2 = f.2, so f and g share both coordinates
        exact absurd ⟨h2, h1.symm.trans h3⟩ (not_both_of_ne hfg)
    · exact Or.inr ⟨h1, h2⟩

/-- The conflicting partners of an edge `e`, i.e. its neighbours in the conflict graph. -/
def conflictNbr (E : Finset (α × β)) (e : α × β) : Finset (α × β) :=
  (E.erase e).filter (fun f => Conflict e f)

/-- **The conflict graph is regular when `G` is biregular.**  An edge `(u,v)` conflicts with the
other `d_u - 1` edges at `u` and the other `d_v - 1` edges at `v`, and with nothing twice, since
two distinct edges cannot share both endpoints.  So its conflict degree is
`(d_u - 1) + (d_v - 1)`, which for an `(a,b)`-biregular graph is `(a-1) + (b-1)`. -/
theorem conflict_degree (E : Finset (α × β)) {e : α × β} (he : e ∈ E) :
    (conflictNbr E e).card
      = ((E.filter (fun f => f.1 = e.1)).card - 1)
        + ((E.filter (fun f => f.2 = e.2)).card - 1) := by
  classical
  have hL : (E.erase e).filter (fun f => f.1 = e.1)
      = (E.filter (fun f => f.1 = e.1)).erase e := by
    ext f; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have hR : (E.erase e).filter (fun f => f.2 = e.2)
      = (E.filter (fun f => f.2 = e.2)).erase e := by
    ext f; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have hdisj : Disjoint ((E.erase e).filter (fun f => f.1 = e.1))
      ((E.erase e).filter (fun f => f.2 = e.2)) := by
    rw [Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_filter, Finset.mem_erase] at hf1 hf2
    exact not_both_of_ne (Ne.symm hf1.1.1) ⟨hf1.2.symm, hf2.2.symm⟩
  have hsplit : conflictNbr E e
      = (E.erase e).filter (fun f => f.1 = e.1) ∪ (E.erase e).filter (fun f => f.2 = e.2) := by
    unfold conflictNbr Conflict
    ext f
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ⟨hfe, h | h⟩
      · exact Or.inl ⟨hfe, h.symm⟩
      · exact Or.inr ⟨hfe, h.symm⟩
    · rintro (⟨hfe, h⟩ | ⟨hfe, h⟩)
      · exact ⟨hfe, Or.inl h.symm⟩
      · exact ⟨hfe, Or.inr h.symm⟩
  have hmemL : e ∈ E.filter (fun f => f.1 = e.1) := Finset.mem_filter.mpr ⟨he, rfl⟩
  have hmemR : e ∈ E.filter (fun f => f.2 = e.2) := Finset.mem_filter.mpr ⟨he, rfl⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hL, hR,
    Finset.card_erase_of_mem hmemL, Finset.card_erase_of_mem hmemR]

/-! ### Four-cycles of the conflict graph

Identify an edge of `G` with a cell of the `p x q` biadjacency matrix.  Two distinct cells are
adjacent in `L` exactly when they share a row or share a column, never both, so every edge of `L`
has a well-defined type, R or C.  Reading the cyclic word of types around a four-cycle of `L`,
only three words survive, and that is what makes the fifth coefficient split into a universal
part plus the four-cycle count of `G`:

* `no_RRRC`  — three consecutive edges of one type force the fourth to have that type too, so the
  words `RRRC` and `RCCC` do not occur;
* `no_RRCC`  — two edges of one row cannot both meet two edges of one column;
* `RRRR`/`CCCC` — all four cells lie in one line, giving the degenerate cycles inside a single
  clique, whose number depends only on the parameters;
* `RCRC`     — by `RCRC_rectangle` the four cells are exactly the entries of a `2 x 2` all-ones
  submatrix, that is a four-cycle of `G`, each contributing exactly one.
-/

/-- **Three consecutive edges of one type force the fourth.**  If `w,x,y,z` lie in one row then
`z` and `w` also share their row, so they cannot instead share a column without coinciding.
Hence the cyclic words `RRRC` and `RCCC` do not occur. -/
theorem no_RRRC {w x y z : α × β} (hzw : z ≠ w)
    (h1 : w.1 = x.1) (h2 : x.1 = y.1) (h3 : y.1 = z.1) (h4 : z.2 = w.2) : False :=
  hzw (Prod.ext (by rw [← h3, ← h2, ← h1]) h4)

/-- **`RRCC` is impossible.**  If `w,x,y` share a row and `y,z,w` share a column, then `w` and `y`
agree in both coordinates. -/
theorem no_RRCC {w x y z : α × β} (hwy : w ≠ y)
    (h1 : w.1 = x.1) (h2 : x.1 = y.1) (h3 : y.2 = z.2) (h4 : z.2 = w.2) : False :=
  hwy (Prod.ext (h1.trans h2) (h3.trans h4).symm)

/-- **The alternating case is a rectangle.**  A four-cycle of `L` whose types alternate has its
four cells at the corners of a `2 x 2` submatrix, determined by the two rows and two columns.
Since all four cells are edges of `G`, that submatrix is all-ones, i.e. a four-cycle of `G`. -/
theorem RCRC_rectangle {w x y z : α × β}
    (h1 : w.1 = x.1) (h2 : x.2 = y.2) (h3 : y.1 = z.1) (h4 : z.2 = w.2) :
    x = (w.1, y.2) ∧ z = (y.1, w.2) :=
  ⟨Prod.ext h1.symm h2, Prod.ext h3.symm h4⟩

/-- The rectangle has two distinct rows and two distinct columns, so it is a genuine four-cycle
of `G` rather than a degenerate one.  If the two rows coincided the cycle would revisit `y` at
`x`, and if the two columns coincided it would revisit `y` at `z`. -/
theorem RCRC_distinct {w x y z : α × β} (hxy : x ≠ y) (hzy : z ≠ y)
    (h1 : w.1 = x.1) (h2 : x.2 = y.2) (h3 : y.1 = z.1) (h4 : z.2 = w.2) :
    w.1 ≠ y.1 ∧ w.2 ≠ y.2 :=
  ⟨fun hrow => hxy (Prod.ext (h1.symm.trans hrow) h2),
   fun hcol => hzy (Prod.ext h3.symm (h4.trans hcol))⟩

/-- Column mirror of `no_RRRC`. -/
theorem no_CCCR {w x y z : α × β} (hzw : z ≠ w)
    (h1 : w.2 = x.2) (h2 : x.2 = y.2) (h3 : y.2 = z.2) (h4 : z.1 = w.1) : False :=
  hzw (Prod.ext h4 (by rw [← h3, ← h2, ← h1]))

/-- Column mirror of `no_RRCC`. -/
theorem no_CCRR {w x y z : α × β} (hwy : w ≠ y)
    (h1 : w.2 = x.2) (h2 : x.2 = y.2) (h3 : y.1 = z.1) (h4 : z.1 = w.1) : False :=
  hwy (Prod.ext (h3.trans h4).symm (h1.trans h2))

/-- **Trichotomy for four-cycles of the conflict graph.**  Reading the cyclic word of edge types,
of the sixteen possibilities only four survive: all four cells in one row, all four in one column,
or one of the two alternating words, which by `RCRC_rectangle` put the cells at the corners of a
`2 x 2` submatrix.  The first two are the degenerate cycles inside a single clique, counted by the
parameters alone; the last two are exactly the four-cycles of `G`. -/
theorem four_cycle_trichotomy {w x y z : α × β}
    (hwx : w ≠ x) (hxy : x ≠ y) (hyz : y ≠ z) (hzw : z ≠ w) (hwy : w ≠ y) (hxz : x ≠ z)
    (c1 : Conflict w x) (c2 : Conflict x y) (c3 : Conflict y z) (c4 : Conflict z w) :
    (w.1 = x.1 ∧ x.1 = y.1 ∧ y.1 = z.1)
    ∨ (w.2 = x.2 ∧ x.2 = y.2 ∧ y.2 = z.2)
    ∨ (w.1 = x.1 ∧ x.2 = y.2 ∧ y.1 = z.1 ∧ z.2 = w.2)
    ∨ (w.2 = x.2 ∧ x.1 = y.1 ∧ y.2 = z.2 ∧ z.1 = w.1) := by
  unfold Conflict at c1 c2 c3 c4
  rcases c1 with r1 | k1 <;> rcases c2 with r2 | k2 <;>
    rcases c3 with r3 | k3 <;> rcases c4 with r4 | k4
  · exact Or.inl ⟨r1, r2, r3⟩                                             -- RRRR
  · exact (no_RRRC (w := w) (x := x) (y := y) (z := z) hzw r1 r2 r3 k4).elim   -- RRRC
  · exact (no_RRRC (w := z) (x := w) (y := x) (z := y) hyz r4 r1 r2 k3).elim   -- RRCR
  · exact (no_RRCC (w := w) (x := x) (y := y) (z := z) hwy r1 r2 k3 k4).elim   -- RRCC
  · exact (no_RRRC (w := y) (x := z) (y := w) (z := x) hxy r3 r4 r1 k2).elim   -- RCRR
  · exact Or.inr (Or.inr (Or.inl ⟨r1, k2, r3, k4⟩))                       -- RCRC
  · exact (no_RRCC (w := z) (x := w) (y := x) (z := y) hxz.symm r4 r1 k2 k3).elim -- RCCR
  · exact (no_CCCR (w := x) (y := z) (x := y) (z := w) hwx k2 k3 k4 r1).elim -- RCCC
  · exact (no_RRRC (w := x) (x := y) (y := z) (z := w) hwx r2 r3 r4 k1).elim   -- CRRR
  · exact (no_RRCC (w := x) (x := y) (y := z) (z := w) hxz r2 r3 k4 k1).elim   -- CRRC
  · exact Or.inr (Or.inr (Or.inr ⟨k1, r2, k3, r4⟩))                       -- CRCR
  · exact (no_CCCR (w := y) (x := z) (y := w) (z := x) hxy k3 k4 k1 r2).elim -- CRCC
  · exact (no_CCRR (w := w) (x := x) (y := y) (z := z) hwy k1 k2 r3 r4).elim -- CCRR
  · exact (no_CCCR (w := z) (x := w) (y := x) (z := y) hyz k4 k1 k2 r3).elim -- CCRC
  · exact (no_CCCR (w := w) (x := x) (y := y) (z := z) hzw k1 k2 k3 r4).elim -- CCCR
  · exact Or.inr (Or.inl ⟨k1, k2, k3⟩)                                    -- CCCC

/-! ### The engine of the inclusion-exclusion

Every count `m_k` in this file is a number of independent `k`-sets of the conflict graph, and the
expansion that computes them rests on one identity: the indicator of "no two elements conflict"
is the alternating sum over subsets of the conflicting pairs.  Summing that over all `k`-subsets
and exchanging the order of summation turns `m_k` into a signed sum of subgraph counts, which is
where `four_cycle_trichotomy` and `three_meeting_share` then do their work.
-/

/-- The conflicting ordered pairs inside a set of edges. -/
def conflictPairs (T : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  T.offDiag.filter (fun q => Conflict q.1 q.2)

/-- A set of edges is a matching exactly when it contains no conflicting pair. -/
theorem conflictPairs_eq_empty_iff (T : Finset (α × β)) :
    conflictPairs T = ∅ ↔ IsMatching T := by
  classical
  constructor
  · intro h
    refine ⟨fun e he f hf h1 => ?_, fun e he f hf h2 => ?_⟩
    · by_contra hne
      have hmem : (e, f) ∈ conflictPairs T :=
        Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨he, hf, hne⟩, Or.inl h1⟩
      simp [h] at hmem
    · by_contra hne
      have hmem : (e, f) ∈ conflictPairs T :=
        Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨he, hf, hne⟩, Or.inr h2⟩
      simp [h] at hmem
  · rintro ⟨hL, hR⟩
    refine Finset.eq_empty_of_forall_notMem ?_
    intro q hq
    simp only [conflictPairs, Finset.mem_filter, Finset.mem_offDiag] at hq
    obtain ⟨⟨h1, h2, hne⟩, hc⟩ := hq
    unfold Conflict at hc
    rcases hc with hc | hc
    · exact hne (hL _ h1 _ h2 hc)
    · exact hne (hR _ h1 _ h2 hc)

/-- **The matching indicator as an alternating sum.**  This is the identity the whole
inclusion-exclusion runs on: summing it over all `k`-subsets of the edge set and exchanging the
order of summation expresses `m_k` as a signed sum of subgraph counts of the conflict graph. -/
theorem alt_sum_conflictPairs (T : Finset (α × β)) :
    (∑ S ∈ (conflictPairs T).powerset, (-1 : ℤ) ^ S.card)
      = if IsMatching T then 1 else 0 := by
  classical
  rw [Finset.sum_powerset_neg_one_pow_card]
  by_cases h : IsMatching T
  · rw [if_pos ((conflictPairs_eq_empty_iff T).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((conflictPairs_eq_empty_iff T).mp hc)), if_neg h]

/-- The `k`-matchings are the `k`-subsets that are matchings. -/
theorem matchings_card_eq_powersetCard_filter (E : Finset (α × β)) (k : ℕ) :
    (matchings E).filter (fun M => M.card = k) = (E.powersetCard k).filter IsMatching := by
  classical
  ext M
  simp only [Finset.mem_filter, matchings, Finset.mem_powerset, Finset.mem_powersetCard]
  tauto

/-- Conflict is intrinsic to a pair of edges, so the conflicting pairs inside `T` are exactly
those conflicting pairs of `E` both of whose entries lie in `T`. -/
theorem mem_conflictPairs_iff {E T : Finset (α × β)} (hTE : T ⊆ E)
    {q : (α × β) × (α × β)} :
    q ∈ conflictPairs T ↔ q ∈ conflictPairs E ∧ q.1 ∈ T ∧ q.2 ∈ T := by
  classical
  simp only [conflictPairs, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨h1, h2, hne⟩, hc⟩
    exact ⟨⟨⟨hTE h1, hTE h2, hne⟩, hc⟩, h1, h2⟩
  · rintro ⟨⟨⟨_, _, hne⟩, hc⟩, h1, h2⟩
    exact ⟨⟨h1, h2, hne⟩, hc⟩

/-- **`m_k` as a double sum.**  Replacing the matching indicator by
`alt_sum_conflictPairs` turns the count of `k`-matchings into a sum over `k`-subsets of an
alternating sum over their internal conflicts.  Exchanging the two summations — using
`mem_conflictPairs_iff`, which says the inner index set depends on `T` only through which
endpoints lie in it — is what produces the signed sum of subgraph counts of the conflict graph
that Theorems~`thm:universal` and `thm:c4` evaluate. -/
theorem mCount_eq_sum_alt (E : Finset (α × β)) (k : ℕ) :
    (mCount E k : ℤ)
      = ∑ T ∈ E.powersetCard k, ∑ S ∈ (conflictPairs T).powerset, (-1 : ℤ) ^ S.card := by
  classical
  have hinner : ∀ T ∈ E.powersetCard k,
      (∑ S ∈ (conflictPairs T).powerset, (-1 : ℤ) ^ S.card)
        = if IsMatching T then 1 else 0 := fun T _ => alt_sum_conflictPairs T
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, nsmul_eq_mul]
  unfold mCount
  rw [matchings_card_eq_powersetCard_filter]

/-- For `T ⊆ E`, the conflict sets inside `T` are the conflict sets of `E` all of whose endpoints
lie in `T`.  This is what makes the inner index set of `mCount_eq_sum_alt` independent of `T`
except through a condition, so the two summations can be exchanged. -/
theorem powerset_conflictPairs_eq {E T : Finset (α × β)} (hTE : T ⊆ E) :
    (conflictPairs T).powerset
      = (conflictPairs E).powerset.filter (fun S => ∀ q ∈ S, q.1 ∈ T ∧ q.2 ∈ T) := by
  classical
  ext S
  simp only [Finset.mem_powerset, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨fun q hq => ((mem_conflictPairs_iff hTE).mp (h hq)).1,
           fun q hq => ((mem_conflictPairs_iff hTE).mp (h hq)).2⟩
  · rintro ⟨h1, h2⟩ q hq
    exact (mem_conflictPairs_iff hTE).mpr ⟨h1 hq, h2 q hq⟩

/-- **The inclusion-exclusion formula for the matching counts.**  Exchanging the two summations
of `mCount_eq_sum_alt` expresses `m_k` as a signed sum over sets of conflicting pairs, each
weighted by the number of `k`-subsets containing all their endpoints.

This is the identity Theorems `thm:universal` and `thm:c4` evaluate: the weight depends only on
`|E|` and the number of distinct endpoints of `S`, so the sum reorganizes into a signed sum of
subgraph counts of the conflict graph, which `three_meeting_share` and `four_cycle_trichotomy`
then identify. -/
theorem mCount_inclusion_exclusion (E : Finset (α × β)) (k : ℕ) :
    (mCount E k : ℤ)
      = ∑ S ∈ (conflictPairs E).powerset,
          (-1 : ℤ) ^ S.card
            * ((E.powersetCard k).filter (fun T => ∀ q ∈ S, q.1 ∈ T ∧ q.2 ∈ T)).card := by
  classical
  rw [mCount_eq_sum_alt]
  have hcongr : ∀ T ∈ E.powersetCard k,
      (∑ S ∈ (conflictPairs T).powerset, (-1 : ℤ) ^ S.card)
        = ∑ S ∈ (conflictPairs E).powerset,
            (if (∀ q ∈ S, q.1 ∈ T ∧ q.2 ∈ T) then (-1 : ℤ) ^ S.card else 0) := by
    intro T hT
    rw [powerset_conflictPairs_eq (Finset.mem_powersetCard.mp hT).1, Finset.sum_filter]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end ConflictGraph

end BipartiteMatchingPoly
