import Mathlib

/-!
# The deletion recursion for matching counts

`XuSharp` takes Godsil's bound and subgraph monotonicity of the greatest root as hypotheses,
because both are classical. Discharging them inside Lean is not a small job: Mathlib has
`Combinatorics/SimpleGraph/Matching.lean`, which gives matchings as a structure, and nothing at
all on matching *polynomials*, graph characteristic polynomials, graph covers, or interlacing.
The chain from a hypergraph incidence to the spectral boundary needs all four, and Heilmann-Lieb
real-rootedness besides.

This file formalises the rung everything else stands on. Every classical ingredient we depend on
-- real-rootedness, the divisibility `μ_G ∣ μ_P` for Godsil's path tree, and monotonicity of the
greatest root under subgraphs -- is proved from the recursion

  `μ_G(x) = μ_{G-e}(x) - μ_{G-u-v}(x)`,

which at the level of coefficients is the statement below: the `(k+1)`-matchings of an edge set
split according to whether they use a fixed edge, those that do not being the `(k+1)`-matchings of
the set with it deleted, and those that do being the `k`-matchings of the edges disjoint from it.

The setting is an abstract finite edge set with an incidence map, not `SimpleGraph`, because that
is the generality the argument has and because the incidence graph of a hypergraph is what
`XuSharp.bridge_roots` needs it for. Nothing here assumes the ends of an edge are distinct, or
that edges are distinct as vertex sets.

## Status

`matching_delete` and `matching_delete_card` are `VERIFIED`. They are one step of the chain, and
the rest of Godsil's bound remains a hypothesis in `XuSharp`; this file does not change that, it
records how far the discharge has got and in what form the next step is needed.
-/

namespace MatchingRecursion

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

-- `ends e` is the vertex set of the edge `e`.
variable (ends : E → Finset V)

/-- A set of edges is a matching when distinct edges in it share no vertex. -/
def IsMatching (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (ends e) (ends f)

instance : DecidablePred (IsMatching ends) := fun _ => by unfold IsMatching; infer_instance

/-- The `k`-matchings contained in an allowed edge set `S`. -/
def matchingsIn (S : Finset E) (k : ℕ) : Finset (Finset E) :=
  (S.powersetCard k).filter (IsMatching ends)

/-- The edges of `S` other than `e₀` that meet `e₀` in no vertex. -/
def avoiding (S : Finset E) (e₀ : E) : Finset E :=
  (S.erase e₀).filter (fun f => Disjoint (ends f) (ends e₀))

omit [DecidableEq V] [DecidableEq E] in
/-- A subset of a matching is a matching. -/
theorem isMatching_mono {M N : Finset E} (h : M ⊆ N) (hN : IsMatching ends N) :
    IsMatching ends M :=
  fun _ he _ hf hne => hN _ (h he) _ (h hf) hne

/-- **The deletion recursion, as a bijection.**  Fix an allowed edge `e₀`.  The `(k+1)`-matchings
inside `S` that avoid `e₀` are exactly the `(k+1)`-matchings inside `S.erase e₀`, and those that
use `e₀` are exactly `insert e₀ M` for `M` a `k`-matching inside `avoiding ends S e₀`.  This is the
coefficient form of `μ_G = μ_{G-e} - μ_{G-u-v}`. -/
theorem matching_delete (S : Finset E) (e₀ : E) (h₀ : e₀ ∈ S) (k : ℕ) :
    matchingsIn ends S (k + 1) =
      matchingsIn ends (S.erase e₀) (k + 1) ∪
        (matchingsIn ends (avoiding ends S e₀) k).image (insert e₀) ∧
      Disjoint (matchingsIn ends (S.erase e₀) (k + 1))
        ((matchingsIn ends (avoiding ends S e₀) k).image (insert e₀)) := by
  classical
  constructor
  · ext M
    simp only [matchingsIn, avoiding, Finset.mem_union, Finset.mem_filter, Finset.mem_image,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hMS, hcard⟩, hmat⟩
      by_cases h0 : e₀ ∈ M
      · right
        refine ⟨M.erase e₀, ⟨⟨?_, ?_⟩, ?_⟩, Finset.insert_erase h0⟩
        · intro f hf
          have hfM : f ∈ M := Finset.mem_of_mem_erase hf
          have hne : f ≠ e₀ := Finset.ne_of_mem_erase hf
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hMS hfM⟩,
            hmat _ hfM _ h0 hne⟩
        · rw [Finset.card_erase_of_mem h0, hcard]; rfl
        · exact isMatching_mono ends (Finset.erase_subset _ _) hmat
      · left
        exact ⟨⟨fun f hf => Finset.mem_erase.mpr ⟨fun h => h0 (h ▸ hf), hMS hf⟩, hcard⟩, hmat⟩
    · rintro (⟨⟨hMS, hcard⟩, hmat⟩ | ⟨N, ⟨⟨hNS, hcard⟩, hmat⟩, rfl⟩)
      · exact ⟨⟨fun f hf => Finset.mem_of_mem_erase (hMS hf), hcard⟩, hmat⟩
      · have hne : e₀ ∉ N := by
          intro h
          have := hNS h
          exact (Finset.mem_erase.mp (Finset.mem_filter.mp this).1).1 rfl
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact h₀
          · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hNS hf)).1
        · rw [Finset.card_insert_of_notMem hne, hcard]
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | ha' <;>
            rcases Finset.mem_insert.mp hb with rfl | hb'
          · exact absurd rfl hab
          · exact (Finset.mem_filter.mp (hNS hb')).2.symm
          · exact (Finset.mem_filter.mp (hNS ha')).2
          · exact hmat _ ha' _ hb' hab
  · rw [Finset.disjoint_right]
    rintro M hM hM'
    simp only [matchingsIn, Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard] at hM hM'
    obtain ⟨N, -, rfl⟩ := hM
    exact (Finset.mem_erase.mp (hM'.1.1 (Finset.mem_insert_self _ _))).1 rfl

/-- **The recursion on counts.**  `m_{k+1}(S) = m_{k+1}(S - e₀) + m_k(edges disjoint from e₀)`.
This is `μ_G = μ_{G-e} - μ_{G-u-v}` read off coefficient by coefficient, with the alternating sign
supplied by the `(-1)^k` in the polynomial rather than by the counts. -/
theorem matching_delete_card (S : Finset E) (e₀ : E) (h₀ : e₀ ∈ S) (k : ℕ) :
    (matchingsIn ends S (k + 1)).card =
      (matchingsIn ends (S.erase e₀) (k + 1)).card
        + (matchingsIn ends (avoiding ends S e₀) k).card := by
  classical
  obtain ⟨heq, hdisj⟩ := matching_delete ends S e₀ h₀ k
  have hnot : ∀ N ∈ matchingsIn ends (avoiding ends S e₀) k, e₀ ∉ N := by
    intro N hN h
    have hsub : N ⊆ avoiding ends S e₀ :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hN).1).1
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hsub h)).1).1 rfl
  have hinj : Set.InjOn (insert e₀) ((matchingsIn ends (avoiding ends S e₀) k : Finset (Finset E)) : Set (Finset E)) := by
    intro N hN N' hN' h
    have h1 := hnot N (by simpa using hN)
    have h2 := hnot N' (by simpa using hN')
    rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

end MatchingRecursion
