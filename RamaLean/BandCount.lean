import Mathlib
import RamaLean.GapLabel
import RamaLean.Interlacing

/-!
# Removing Marcus–Spielman–Srivastava from the band count

`BandTheorem` derives BAND from a squeeze supplied by MSS, carried as the hypothesis
`hsqueeze`.  Formalizing MSS itself means formalizing real stability, which is out of
reach.  This file takes the other road: it **removes** the hypothesis rather than proving
it, replacing a deep theorem by a geometric condition that can be checked.

The observation is that connectedness of the parameter space already does the work MSS was
being asked for, and does it for free.

## The clopen argument

Fix `x` avoiding every `λ_k(z)`.  For each `k` the set `{z : λ_k(z) > x}` is open by
continuity, and so is `{z : λ_k(z) < x}`; they are disjoint and cover, so the first is
clopen.  A preconnected parameter space then forces it to be empty or everything.  Hence

  `#{k : λ_k(z) > x}` is the same integer for every `z`,

which is `count_const_of_connected`.  Every member of the family therefore has the same
sign at `x`, so the average does too and cannot vanish there.  That gives, with no MSS:

* `Zeros(μ_G) ⊆ spec(G^ab)`, and
* the **parity** of the root count of `μ_G` above `x`.

## From parity to the count

Parity alone leaves the count undetermined.  Crossing one connected component `C` of
`spec(G^ab)` downward raises the band count by the number of bands inside `C` and the root
count by the number of roots inside `C`, and parity says only that those agree mod 2.

But the two totals are both `n`.  So if every component holds exactly one band, each
component holds an odd number of roots, there are `n` components, and `n` odd positive
integers summing to `n` are all `1`.  That is `all_eq_one_of_odd_of_sum`, and it upgrades
parity to equality.

The band-separation condition is a statement about `spec(G^ab)` that can be checked on any
given graph, unlike common interlacing.  Where it fails, the components-level conclusion
still holds: each component contains as many roots as it does bands, modulo 2.

`BandTheorem.band_of` is left as it is, since the MSS route gives `θ_k ∈ B_k` band by band
rather than only the count.  The two are independent.
-/

namespace BandCount

open Finset GapLabel Interlacing
open scoped Classical

/-! ## The count is constant on a connected parameter space -/

/-- For a continuous real function that never takes the value `x`, being above `x` is a
clopen condition, hence constant on a preconnected space. -/
theorem above_const_of_connected {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z]
    {f : Z → ℝ} (hcont : Continuous f) {x : ℝ} (hx : ∀ z, f z ≠ x) (z w : Z) :
    x < f z ↔ x < f w := by
  set U : Set Z := {u | x < f u} with hU
  have hopen : IsOpen U := hcont.isOpen_preimage (Set.Ioi x) isOpen_Ioi
  have hcompl : Uᶜ = {u | f u < x} := by
    ext u
    simp only [hU, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hx u), fun h => h.le⟩
  have hopen' : IsOpen Uᶜ := by
    rw [hcompl]; exact hcont.isOpen_preimage (Set.Iio x) isOpen_Iio
  have hclopen : IsClopen U := ⟨isOpen_compl_iff.mp hopen', hopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have hz : ¬ (x < f z) := fun hc => by
      have hmem : z ∈ U := hc
      rw [h] at hmem; simp at hmem
    have hw : ¬ (x < f w) := fun hc => by
      have hmem : w ∈ U := hc
      rw [h] at hmem; simp at hmem
    exact ⟨fun c => absurd c hz, fun c => absurd c hw⟩
  · have hz : x < f z := by have : z ∈ U := by rw [h]; trivial
                            exact this
    have hw : x < f w := by have : w ∈ U := by rw [h]; trivial
                            exact this
    exact ⟨fun _ => hw, fun _ => hz⟩

/-- **The count is a constant of the family.**  On a preconnected parameter space, if `x`
is never an eigenvalue then every member has the same number of eigenvalues above `x`.
This is what MSS was being used to supply, and here it is free. -/
theorem count_const_of_connected {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    [PreconnectedSpace Z] {lam : Fin n → Z → ℝ} (hcont : ∀ k, Continuous (lam k))
    {x : ℝ} (hx : ∀ k z, lam k z ≠ x) (z w : Z) :
    (Finset.univ.filter (fun k => x < lam k z)).card
      = (Finset.univ.filter (fun k => x < lam k w)).card := by
  refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
  exact above_const_of_connected (hcont k) (hx k) z w

/-! ## Parity of the root count -/

/-- **Parity, with no interlacing input.**  If every member of the family has `j`
eigenvalues above `x`, then a nonnegative combination of their characteristic polynomials
has a root count above `x` of the same parity.  Together with `count_const_of_connected`
this holds automatically on a connected parameter space. -/
theorem parity_of_family {ι : Type*} (I : Finset ι) (c : ι → ℝ) (r : ι → Multiset ℝ)
    (ρ : Multiset ℝ) (x : ℝ) (j : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hroot : ∀ i ∈ I, x ∉ r i) (hρ : x ∉ ρ)
    (hcount : ∀ i ∈ I, countAbove (r i) x = j)
    {i₀ : ι} (hi₀ : i₀ ∈ I) (hc₀ : 0 < c i₀)
    (havg : ev ρ x = ∑ i ∈ I, c i * ev (r i) x) :
    (-1 : ℝ) ^ (countAbove ρ x) = (-1 : ℝ) ^ j :=
  parity_of_combination I c r ρ x j hc hroot hρ hcount hi₀ hc₀ havg

/-! ## Parity to equality, by counting -/

/-- **The counting step.**  Odd positive integers indexed by a finite set, summing to the
size of that set, are all `1`.

Applied with one entry per connected component of `spec(G^ab)`: parity makes the number of
roots in each component odd, the components number `n` when every component holds a single
band, and the roots number `n` in total. -/
theorem all_eq_one_of_odd_of_sum {ι : Type*} (I : Finset ι) (r : ι → ℕ)
    (hodd : ∀ i ∈ I, Odd (r i)) (hsum : ∑ i ∈ I, r i = I.card) :
    ∀ i ∈ I, r i = 1 := by
  have hge : ∀ i ∈ I, 1 ≤ r i := fun i hi => (hodd i hi).pos
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hne⟩ := hcon
  have h1 := hge i₀ hi₀
  have h2 : 1 < r i₀ := by omega
  have hlt : I.card < ∑ i ∈ I, r i := by
    calc I.card = ∑ _i ∈ I, 1 := by simp
      _ < ∑ i ∈ I, r i := Finset.sum_lt_sum (fun i hi => hge i hi) ⟨i₀, hi₀, h2⟩
  omega

/-- **Band count without MSS.**  If each connected piece carries an odd number of roots,
and the pieces number as many as the roots, then each carries exactly one.  This is the
counting content of BAND, obtained from connectedness and parity alone. -/
theorem one_root_per_band {ι : Type*} (I : Finset ι) (r : ι → ℕ)
    (hparity : ∀ i ∈ I, Odd (r i)) (htotal : ∑ i ∈ I, r i = I.card) (i : ι) (hi : i ∈ I) :
    r i = 1 :=
  all_eq_one_of_odd_of_sum I r hparity htotal i hi

end BandCount
