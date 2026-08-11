import Mathlib

/-!
# Systems of distinct representatives are matchings of the incidence graph

`XuSharp.bridge_roots` takes the factorisation `μ(t²) = c(t)·μ_I(t)` as a hypothesis. This file
supplies the combinatorial half of that hypothesis, which is the only part of the bridge that is
not classical.

Differentiating `det(xI + Σ z_e P_e) = ∏_v (x + Σ_{e ∋ v} z_e)` once in each `z_e` for `e ∈ S`
and setting `z = 0` counts the injective maps `S → V` with `e ↦ v ∈ e`: two hyperedges choosing
the same vertex differentiate one affine factor twice and contribute nothing. Summing over
`|S| = k`, the coefficient of `x^{n-k}` in the mixed characteristic polynomial is the number of
such *systems of distinct representatives* of `k` hyperedges. The claim of Proposition 35 is that
this is the number of `k`-matchings of the incidence bipartite graph `I(H)`.

That identification is what is proved here, and it is a bijection rather than a count: a matching
of `I(H)` is a set of incident pairs with distinct hyperedges and distinct vertices, which is
exactly the graph of an injective choice function. `toPRS` and `exists_repr_of_isPRS` are the two
directions, `card_toPRS` and `card_image_fst_of_isPRS` say both directions preserve cardinality,
and `prs_equiv_injections` packages them.

Nothing here mentions polynomials, projections or spectra: the statement is about a finite
incidence structure, which is the level at which it is true and the level at which it is checked.

## Status

Every theorem below is `VERIFIED`. The analytic half of the bridge — that the derivative
computation above produces these counts — is `HEURISTIC`, checked against the MSS definition in
exact arithmetic on four hypergraphs at `b = 2, 3, 4` in `code/xu_sharp.py`.
-/

namespace SDRMatching

variable {E V : Type*} [DecidableEq E] [DecidableEq V]

-- The incidence structure: `inc e` is the vertex set of the hyperedge `e`.
variable (inc : E → Finset V)

/-- A **matching of the incidence bipartite graph**, written as a finite set of incident pairs
with distinct hyperedges and distinct representatives.  Equivalently a partial system of distinct
representatives; the two are the same data, which is what this file makes precise. -/
def IsPRS (M : Finset (E × V)) : Prop :=
  (∀ p ∈ M, p.2 ∈ inc p.1) ∧
    Set.InjOn Prod.fst (M : Set (E × V)) ∧ Set.InjOn Prod.snd (M : Set (E × V))

/-- The graph of a choice function, as a set of pairs. -/
def toPRS (S : Finset E) (f : E → V) : Finset (E × V) := S.image fun e => (e, f e)

/-- Passing to the graph never collapses two hyperedges, so the size is the number of hyperedges
chosen.  This is the step that makes the two counts comparable at all. -/
theorem card_toPRS (S : Finset E) (f : E → V) : (toPRS S f).card = S.card :=
  Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h

/-- An injective choice of representatives is a matching of the incidence graph. -/
theorem isPRS_toPRS {S : Finset E} {f : E → V} (hf : ∀ e ∈ S, f e ∈ inc e)
    (hinj : Set.InjOn f S) : IsPRS inc (toPRS S f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro p hp
    simp only [toPRS, Finset.mem_image] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact hf e he
  · rintro p hp p' hp' h
    simp only [toPRS, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp hp'
    obtain ⟨e, -, rfl⟩ := hp
    obtain ⟨e', -, rfl⟩ := hp'
    have : e = e' := h
    subst this
    rfl
  · rintro p hp p' hp' h
    simp only [toPRS, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp hp'
    obtain ⟨e, he, rfl⟩ := hp
    obtain ⟨e', he', rfl⟩ := hp'
    exact Prod.ext (hinj he he' h) h

omit [DecidableEq V] in
/-- The hyperedges used by a matching, and the count is unchanged: distinct pairs use distinct
hyperedges, which is half of what it means to be a matching. -/
theorem card_image_fst_of_isPRS {M : Finset (E × V)} (h : IsPRS inc M) :
    (M.image Prod.fst).card = M.card :=
  Finset.card_image_of_injOn h.2.1

/-- **The other direction.**  Every matching of the incidence graph is the graph of an injective
choice of representatives for the hyperedges it uses.  So the two descriptions carry the same
data, and by `card_toPRS` and `card_image_fst_of_isPRS` they carry it in the same size. -/
theorem exists_repr_of_isPRS [Nonempty V] {M : Finset (E × V)} (h : IsPRS inc M) :
    ∃ f : E → V, (∀ e ∈ M.image Prod.fst, f e ∈ inc e) ∧
      Set.InjOn f (M.image Prod.fst) ∧ M = toPRS (M.image Prod.fst) f := by
  classical
  set f : E → V := fun e => if hx : ∃ v, (e, v) ∈ M then hx.choose else Classical.arbitrary V
    with hfdef
  have key : ∀ e ∈ M.image Prod.fst, (e, f e) ∈ M := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hx : ∃ v, (p.1, v) ∈ M := ⟨p.2, by simpa using hp⟩
    simp only [hfdef, dif_pos hx]
    exact hx.choose_spec
  refine ⟨f, ?_, ?_, ?_⟩
  · intro e he
    exact h.1 _ (key e he)
  · intro e he e' he' hff
    have h1 : (e, f e) ∈ M := key e he
    have h2 : (e', f e') ∈ M := key e' he'
    have hm1 : ((e, f e) : E × V) ∈ (M : Set (E × V)) := by exact_mod_cast h1
    have hm2 : ((e', f e') : E × V) ∈ (M : Set (E × V)) := by exact_mod_cast h2
    exact congrArg Prod.fst (h.2.2 hm1 hm2 hff)
  · apply Finset.ext
    intro p
    constructor
    · intro hp
      have hfst : p.1 ∈ M.image Prod.fst := Finset.mem_image_of_mem _ hp
      have hm1 : ((p.1, f p.1) : E × V) ∈ (M : Set (E × V)) := by
        exact_mod_cast key p.1 hfst
      have hm2 : p ∈ (M : Set (E × V)) := by exact_mod_cast hp
      have hval : f p.1 = p.2 := congrArg Prod.snd (h.2.1 hm1 hm2 rfl)
      rw [toPRS]
      exact Finset.mem_image.mpr ⟨p.1, hfst, by rw [hval]⟩
    · intro hp
      rw [toPRS] at hp
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      exact key e he

/-- The correspondence as a single statement: for every `k`, the matchings of the incidence graph
of size `k` and the injective choices of representatives for `k` hyperedges are the same objects.
This is the coefficient identity of Proposition 35, with the polynomials stripped away. -/
theorem prs_equiv_injections [Nonempty V] (k : ℕ) (M : Finset (E × V)) :
    (IsPRS inc M ∧ M.card = k) ↔
      ∃ (S : Finset E) (f : E → V), S.card = k ∧ (∀ e ∈ S, f e ∈ inc e) ∧
        Set.InjOn f S ∧ M = toPRS S f := by
  constructor
  · rintro ⟨h, hcard⟩
    obtain ⟨f, hf, hinj, hM⟩ := exists_repr_of_isPRS inc h
    exact ⟨M.image Prod.fst, f, by rw [card_image_fst_of_isPRS inc h, hcard], hf, hinj, hM⟩
  · rintro ⟨S, f, hcard, hf, hinj, rfl⟩
    exact ⟨isPRS_toPRS inc hf hinj, by rw [card_toPRS, hcard]⟩

end SDRMatching
