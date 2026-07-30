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

end BipartiteMatchingPoly
