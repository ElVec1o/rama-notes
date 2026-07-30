import Mathlib

namespace ScratchTwoMatch

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def IsMatching (M : Finset (α × β)) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧ (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)

instance (M : Finset (α × β)) : Decidable (IsMatching M) := by
  unfold IsMatching; infer_instance

def matchings (E : Finset (α × β)) : Finset (Finset (α × β)) :=
  E.powerset.filter IsMatching

def mCount (E : Finset (α × β)) (k : ℕ) : ℕ :=
  ((matchings E).filter (fun M => M.card = k)).card

/-! ## New material -/

def confL (E : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  E.offDiag.filter (fun q => q.1.1 = q.2.1)

def confR (E : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  E.offDiag.filter (fun q => q.1.2 = q.2.2)

def ordMatch (E : Finset (α × β)) : Finset ((α × β) × (α × β)) :=
  E.offDiag.filter (fun q => q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2)

/-- Step A -/
lemma confL_disjoint_confR (E : Finset (α × β)) : Disjoint (confL E) (confR E) := by
  classical
  rw [Finset.disjoint_left]
  rintro q hL hR
  rw [confL, Finset.mem_filter] at hL
  rw [confR, Finset.mem_filter] at hR
  have hne : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hL.1).2.2
  exact hne (Prod.ext hL.2 hR.2)

/-- Step B -/
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
  have hdisj1 : Disjoint (ordMatch E) (confL E ∪ confR E) := by
    rw [Finset.disjoint_left]
    rintro q hq hmem
    rw [ordMatch, Finset.mem_filter] at hq
    rcases Finset.mem_union.mp hmem with h | h
    · exact hq.2.1 (Finset.mem_filter.mp h).2
    · exact hq.2.2 (Finset.mem_filter.mp h).2
  have hcard : E.offDiag.card = (ordMatch E).card + ((confL E).card + (confR E).card) := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj1,
      Finset.card_union_of_disjoint (confL_disjoint_confR E)]
  rw [Finset.offDiag_card] at hcard
  have hmul : E.card * E.card - E.card = E.card * (E.card - 1) := by
    cases hn : E.card with
    | zero => simp
    | succ n => simp [Nat.mul_succ]
  omega

/-- Step C, the fibre computation. -/
lemma ordMatch_fibre (E : Finset (α × β)) {M : Finset (α × β)}
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
  have hne2 : ((e, f) : (α × β) × (α × β)) ≠ (f, e) := fun h => hef (congrArg Prod.fst h)
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne2), Finset.card_singleton]

lemma card_ordMatch (E : Finset (α × β)) : (ordMatch E).card = 2 * mCount E 2 := by
  classical
  have hmaps : ∀ q ∈ ordMatch E,
      ({q.1, q.2} : Finset (α × β)) ∈ (matchings E).filter (fun M => M.card = 2) := by
    intro q hq
    rw [ordMatch, Finset.mem_filter, Finset.mem_offDiag] at hq
    obtain ⟨⟨h1E, h2E, hne⟩, hf, hs⟩ := hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩, ?_⟩
    · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
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
  rw [Finset.sum_congr rfl (fun M hM => ordMatch_fibre E hM)]
  rw [Finset.sum_const, smul_eq_mul, mCount]
  ring

theorem two_mul_mCount_two_add_conflicts (E : Finset (α × β)) :
    2 * mCount E 2 + (confL E).card + (confR E).card = E.card * (E.card - 1) := by
  rw [← card_ordMatch]
  exact card_ordMatch_add_conflicts E

/-! ## Second target -/

def dL (E : Finset (α × β)) (v : α) : ℕ := (E.filter (fun e => e.1 = v)).card
def dR (E : Finset (α × β)) (u : β) : ℕ := (E.filter (fun e => e.2 = u)).card

lemma offDiag_card' {γ : Type*} [DecidableEq γ] (s : Finset γ) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  cases hn : s.card with
  | zero => simp
  | succ n => simp [Nat.mul_succ]

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
  rw [hfib, offDiag_card', dL]

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
  rw [hfib, offDiag_card', dR]

end ScratchTwoMatch
