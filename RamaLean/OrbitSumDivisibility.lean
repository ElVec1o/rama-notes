import Mathlib
/-!
# Orbit-sum divisibility

If a finite group `G` acts **freely** on a fintype `X` and `f : X → ZMod (|G|)` is
`G`-invariant, then `∑ x, f x = 0`. Each orbit has size `|G|` and `f` is constant on
it, so contributes `|G| • c = 0` in `ZMod |G|`.

This is the engine behind the 2-adic tower for the GCD permanent
`a(n) = per[gcd(i,j)]`: a free `(ℤ/2)^k` action (by even permutations) on the
sign-`(−1)` terms, permuting the rows `≡ (1,…,1) mod 2^k`, forces `2^k ∣ a(n)`-oddsum,
hence `v₂(a(n)) → ∞`.
-/
open Finset MulAction

/-- **Free finite group action + invariant ⟹ `|G|` divides the sum**, over any commutative
ring `R`. Each orbit has size `|G|` and `f` is constant on it, so the orbit contributes
`|G| • f(rep) = |G| * f(rep)`, a multiple of `|G|`; summing keeps divisibility.

This is the abstract kernel behind two divisibilities for the GCD permanent
`a(n) = per[gcd(i,j)]`:
* the **2-adic tower** — `R = ZMod (2^k)`, a free `(ℤ/2)^k` action (see the `ZMod`
  corollary below), forcing `2^k ∣ a(n)`-oddsum, hence `v₂(a(n)) → ∞`;
* the **`c!`-divisibility of a permanent** with `c` all-ones columns — take `R = ℤ`,
  `X = Perm (Fin n)`, `f σ = ∏ᵢ M (σ i) i`, and `G = Perm C` (`C` the all-ones columns)
  acting freely by precomposition `σ ↦ σ ∘ τ̃`; invariance holds because the all-ones
  columns contribute factor `1`. Then `(c! : ℤ) = |Perm C| ∣ per M`, the linear-`v₂` step. -/
theorem card_dvd_sum_of_free_invariant {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X] {R : Type*} [CommRing R]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (f : X → R) (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (Fintype.card G : R) ∣ ∑ x, f x := by
  classical
  rw [← Equiv.sum_comp (MulAction.selfEquivSigmaOrbits G X).symm f, Fintype.sum_sigma]
  apply Finset.dvd_sum
  intro ω _
  have hconst : ∀ y : orbit G (Quotient.out ω),
      f ((MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, y⟩) = f (Quotient.out ω) := by
    intro y
    obtain ⟨g, hg⟩ := y.2
    have hy : (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, y⟩ = (y : X) := rfl
    rw [hy, ← hg, hf]
  rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (orbit G (Quotient.out ω)) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G (Quotient.out ω)),
      hfree, Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
  rw [hcard, nsmul_eq_mul]
  exact dvd_mul_right _ _

/-- Free finite group action + `ZMod |G|`-valued invariant ⟹ the sum vanishes.
(Corollary of `card_dvd_sum_of_free_invariant`: `|G| = 0` in `ZMod |G|`.) -/
theorem sum_zmod_eq_zero_of_free_invariant {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (f : X → ZMod (Fintype.card G)) (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∑ x, f x = 0 := by
  have h := card_dvd_sum_of_free_invariant hfree f hf
  rwa [ZMod.natCast_self, zero_dvd_iff] at h
