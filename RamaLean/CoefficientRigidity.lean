import Mathlib

/-!
# Why four coefficients are rigid

Rotating a commuting tight family off its locus moves the mixed characteristic polynomial, but not
all of it: the coefficients of `y^n, y^{n-1}, y^{n-2}, y^{n-3}` do not move at all, and the
deformation has degree exactly `n - 4`. Measured first at three families, then explained. This
file is the explanation's core, which is a statement about polynomials and nothing else.

## The reduction

Only subsets containing exactly one of the two rotated blocks depend on `θ`, and they pair as
`S ∪ {e}` with `S ∪ {f}`. For a diagonal `N` and a unit vector `u`,
`det(xI + N + P_u) = det(xI + N) + uᵀ adj(xI + N) u`, and for diagonal `N = diag(d)` the adjugate
is diagonal with entries `∏_{l ≠ i}(x + d_l)`. With `u` supported on `{v, w}` the pair's
`θ`-dependent part collapses to `sin²θ · Δ(x)` where

  `Δ(x) = (d_v - d_w) [ ∏_{l ≠ v,w}(x + d_l) - ∏_{l ≠ v,w}(x + d'_l) ]`,

using that `d` and `d'` agree at `v` and at `w`. Both products are monic of degree `n - 2`, and
`tr N_e = tr N_f` gives them the same sum of roots. Two such polynomials agree in their top two
coefficients, so their difference has degree at most `n - 4`. That is the whole reason for the
exponent: one degree from monicity, one from the equal traces.

`prod_diff_natDegree_le` is that step. `natDegree_sub_le_of_coeff_eq` is the trivial half it rests
on, stated separately because it is what makes the argument checkable rather than plausible.

## Status

Both theorems are `VERIFIED`. That the pairing reduces the `θ`-dependence to `Δ` is `PROVED` in
the note and checked numerically in `code/curvature.py`; the identification of the two products as
monic with equal root sums is immediate from `d_v = d'_v`, `d_w = d'_w` and `tr N_e = tr N_f`,
each of which is a statement about which vertices lie in which hyperedge.
-/

namespace CoefficientRigidity

open Polynomial Finset

-- Nontrivial is needed for `X.natDegree = 1`; over the zero ring every degree collapses.
variable {R : Type*} [CommRing R] [Nontrivial R]

/-- If two polynomials agree in every coefficient above `k`, their difference has degree at most
`k`.  Elementary, and it is the only thing the rigidity argument needs from polynomial algebra. -/
theorem natDegree_sub_le_of_coeff_eq {p q : R[X]} {k : ℕ}
    (h : ∀ j, k < j → p.coeff j = q.coeff j) : (p - q).natDegree ≤ k := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  simp [coeff_sub, h m hm]

/-- **The rigidity step.**  Two products `∏ (X + d i)` and `∏ (X + d' i)` over the same index set,
with the same sum of the `d`, differ by a polynomial of degree at most `card - 2`.  Monicity kills
the top coefficient and the equal sums kill the next one; nothing else is used, and nothing else is
true in general. -/
theorem prod_diff_natDegree_le {ι : Type*} (s : Finset ι) (d d' : ι → R) (N : ℕ)
    (hcard : s.card = N + 2) (hsum : ∑ i ∈ s, d i = ∑ i ∈ s, d' i) :
    ((∏ i ∈ s, (X + C (d i))) - (∏ i ∈ s, (X + C (d' i)))).natDegree ≤ N := by
  classical
  have hmon : ∀ r : ι → R, (∏ i ∈ s, (X + C (r i))).Monic :=
    fun r => monic_prod_of_monic _ _ fun i _ => monic_X_add_C (r i)
  have hdeg : ∀ r : ι → R, (∏ i ∈ s, (X + C (r i))).natDegree = s.card := by
    intro r
    rw [natDegree_prod_of_monic _ _ (fun i (_ : i ∈ s) => monic_X_add_C (r i))]
    simp [natDegree_X]
  refine natDegree_sub_le_of_coeff_eq fun j hj => ?_
  rcases lt_trichotomy j (N + 2) with hlt | rfl | hgt
  · -- the only case left below the top is j = N + 1, the coefficient the trace controls
    have : j = N + 1 := by omega
    subst this
    rw [prod_X_add_C_coeff s d (by omega), prod_X_add_C_coeff s d' (by omega)]
    have : s.card - (N + 1) = 1 := by omega
    rw [this]
    simpa [Finset.powersetCard_one, Finset.sum_map] using hsum
  · -- the leading coefficient, equal because both products are monic
    have h1 := (hmon d).coeff_natDegree
    have h2 := (hmon d').coeff_natDegree
    rw [hdeg d] at h1
    rw [hdeg d'] at h2
    rw [hcard] at h1 h2
    rw [h1, h2]
  · -- above the degree both vanish
    rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg d, hcard]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg d', hcard]; omega)]

/-- The consequence as it is used: with `n` vertices the deformation of the mixed characteristic
polynomial is supported on the coefficients of `y^{n-4}` and below, so the four leading
coefficients are rigid. -/
theorem four_leading_rigid {ι : Type*} (s : Finset ι) (d d' : ι → R) (n : ℕ)
    (hcard : s.card = n - 2) (hn : 4 ≤ n) (hsum : ∑ i ∈ s, d i = ∑ i ∈ s, d' i) :
    ((∏ i ∈ s, (X + C (d i))) - (∏ i ∈ s, (X + C (d' i)))).natDegree ≤ n - 4 :=
  prod_diff_natDegree_le s d d' (n - 4) (by omega) hsum

end CoefficientRigidity
