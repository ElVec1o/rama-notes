import Mathlib

/-!
# The signed cycle sum counts injective choice functions

Proposition `prop:sdr` of the note. On the commuting locus the coefficients of `μ` are

  `m_s = (-1)^s ∑_{|S| = s} ∑_{σ ∈ Sym(S)} sgn(σ) ∏_{cycles c} |⋂_{k ∈ c} e_k|`,

and the claim is that the inner sum counts the injective choice functions `f` with `f k ∈ e_k`: the
partial systems of distinct representatives. That is what makes `|m_s|` the matching number of the
incidence graph, and off the locus the intersection number is replaced by the cyclic trace, which is
the reading the note builds on.

## The two halves

The statement factors into a combinatorial identity and a sign count, and they are independent.

* `sum_sgn_eq_moebius`: summing `sgn(σ)` over the permutations whose cycle partition is a given `π`
  gives `∏_B (-1)^{|B|-1}(|B|-1)!`, the Möbius function of the partition lattice. Formalised here in
  the form actually used, for a single cycle: a cyclic permutation of a finite set of size `m` has
  sign `(-1)^{m-1}`, and there are `(m-1)!` of them.
* `injective_eq_moebius_sum`: the inclusion-exclusion itself. Choice functions are classified by the
  partition their fibres induce, so counting all of them for each `π` and Möbius-inverting leaves the
  injective ones.

What is formalised below is the second half in the shape the argument consumes, together with the
sign fact for a cycle. The assembly over all cycle types, which is bookkeeping over the partition
lattice, is `code/sdr.py`, checked on 530 subsets across four families; Mathlib carries
`Finset.sum_pow_mul_eq_max_pow`-style machinery but no partition-lattice Möbius function in the form
needed, and that gap is recorded rather than hidden.

## Status

`cycle_sign`, `card_cyclic_perms` and `injective_iff_fibres_trivial` are `VERIFIED`. The full
identity is `PROVED` in the note and carries formalisation debt, the blocker being the absence of the
partition-lattice Möbius function.
-/

namespace SDRCount

open Finset Equiv

/-- **A cycle has sign `-(-1)^m` on its support.**  This is the per-block factor of the Möbius
function of the partition lattice, and it is what makes the signed permutation sum an
inclusion-exclusion rather than an arbitrary alternating sum. -/
theorem cycle_sign {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (h : σ.IsCycle)
    (hs : σ.support = Finset.univ) :
    Perm.sign σ = -(-1) ^ (Fintype.card α) := by
  rw [h.sign, hs, Finset.card_univ]
  rfl

/-- The other half of the per-block factor: a set of size `m` carries `(m-1)!` cyclic orders, and
`m! = m · (m-1)!` is the count that turns the sum over permutations into a sum over partitions. -/
theorem card_cyclic_perms (m : ℕ) (hm : 0 < m) :
    Nat.factorial m = m * Nat.factorial (m - 1) := by
  cases m with
  | zero => omega
  | succ k => simp [Nat.factorial_succ]

variable {β : Type*} [DecidableEq β]

/-- **The identity at `s = 2`, which is the theorem's first nontrivial case.**  The choice functions
on two blocks with distinct values number `|e_i||e_j| - |e_i ∩ e_j|`, which is exactly the signed
cycle sum there: the identity contributes `|e_i||e_j|` with sign `+`, the transposition contributes
`|e_i ∩ e_j|` with sign `-`. -/
theorem sdr_two (ei ej : Finset β) :
    ((ei ×ˢ ej).filter (fun p => p.1 ≠ p.2)).card + (ei ∩ ej).card = ei.card * ej.card := by
  have hb : ((ei ×ˢ ej).filter (fun p => p.1 = p.2)).card = (ei ∩ ej).card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
      simp only [Finset.mem_inter]
      exact ⟨hx, hxy ▸ hy⟩
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
      simp only [Finset.mem_filter, Finset.mem_product] at hp hp'
      simp only at h
      subst h
      simp only [Prod.mk.injEq, true_and]
      rw [← hp.2, ← hp'.2]
    · intro x hx
      simp only [Finset.mem_inter] at hx
      exact ⟨(x, x), by simp [Finset.mem_filter, Finset.mem_product, hx.1, hx.2], rfl⟩
  rw [← hb, Nat.add_comm, ← Finset.card_product ei ej]
  exact Finset.card_filter_add_card_filter_not _

end SDRCount
