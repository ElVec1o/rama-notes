import Mathlib

/-!
# The mixed discriminant, and the two properties the identity needs

The coefficients of the mixed characteristic polynomial off the commuting locus are mixed
discriminants (A12, `code/mixeddisc.py`, P37):

  `c_s = (-1)^s s! binom(p,s) ∑_{|S| = s} D(A_k : k ∈ S, I repeated p-s)`.

Two things about `D` have to hold before that display even parses, and both were carried as prose.

* **It is well defined.**  The right-hand side writes `D` of an unordered set together with a
  repeated identity.  That is legitimate only because `D` is symmetric in its arguments, which is
  `mixedDisc_comp_perm` below.  Without it the sum over `S` is not a sum over sets.
* **It extends the determinant.**  Calling `D` the multilinear extension of `det` is a claim, and
  the claim is `mixedDisc_const`: on the diagonal `D(B, …, B)` is `p!` times `det B` in the
  unnormalised convention used here, hence exactly `det B` after dividing by `p!`, which is the
  normalisation `code/mixeddisc.py` uses.

Linearity in each argument separately is `mixedDisc_update_add`, and it holds for a reason worth
recording: in the term indexed by `σ`, the matrix `B k` contributes to exactly one column, the one
numbered `σ⁻¹ k`, so each determinant is linear in `B k` by linearity of `det` in a column. That
there is exactly one such column, not several, is what makes the permutation sum multilinear rather
than merely homogeneous.

## What is not formalised

Alexandrov's inequality, that `D ≥ 0` on positive semidefinite arguments, and Bapat's and Gurvits'
theorems, are classical and are cited rather than proved; they are what give nonnegativity of the
coefficients and the van der Waerden bound, and Mathlib carries none of them.  The identity P37
itself is a computation checked numerically at `p ≤ 6` in `code/mixeddisc.py` and is not formalised
either.  No novelty is claimed for anything in this file; the point is that the naming claim and the
well-definedness of the display are now checked rather than asserted.

## Convention

`mixedDisc` here is the unnormalised permutation sum, `p!` times the usual mixed discriminant.  The
factor is carried explicitly in `mixedDisc_const` so that no normalisation is hidden; a mismatch of
exactly this kind, between this convention and Gurvits', is recorded in the log as a regime error
caught by Rule 7.

## Status

`mixedDisc_const`, `mixedDisc_comp_perm` and `mixedDisc_update_add` are `VERIFIED`.
-/

namespace MixedDiscriminant

open Matrix Finset Equiv

variable {p : ℕ} {R : Type*} [CommRing R]

/-- The unnormalised mixed discriminant: sum over permutations of the determinant of the matrix
whose `j`-th column is the `j`-th column of `B (σ j)`.  Dividing by `p!` gives the usual mixed
discriminant, and the factor is kept explicit rather than folded in. -/
def mixedDisc (B : Fin p → Matrix (Fin p) (Fin p) R) : R :=
  ∑ σ : Perm (Fin p), (Matrix.of fun i j => B (σ j) i j).det

/-- **It extends the determinant.**  Every term of the permutation sum is `det B`, so the diagonal
value is `p!` times it. -/
theorem mixedDisc_const (B : Matrix (Fin p) (Fin p) R) :
    mixedDisc (fun _ => B) = (Nat.factorial p : R) * B.det := by
  have h : mixedDisc (fun _ => B) = ∑ _σ : Perm (Fin p), B.det := rfl
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- **It is symmetric in its arguments.**  Precomposing the family with a permutation reindexes the
sum and changes nothing, which is what makes `D` of an unordered set of matrices meaningful. -/
theorem mixedDisc_comp_perm (B : Fin p → Matrix (Fin p) (Fin p) R) (τ : Perm (Fin p)) :
    mixedDisc (fun k => B (τ k)) = mixedDisc B := by
  unfold mixedDisc
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

/-- **It is additive in each argument.**  In the term indexed by `σ` the matrix `B k` occupies
exactly the column `σ⁻¹ k`, so the determinant is linear there. -/
theorem mixedDisc_update_add (B : Fin p → Matrix (Fin p) (Fin p) R)
    (k : Fin p) (M N : Matrix (Fin p) (Fin p) R) :
    mixedDisc (Function.update B k (M + N))
      = mixedDisc (Function.update B k M) + mixedDisc (Function.update B k N) := by
  unfold mixedDisc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key : ∀ (C : Matrix (Fin p) (Fin p) R),
      (Matrix.of fun i j => Function.update B k C (σ j) i j)
        = (Matrix.of fun i j => B (σ j) i j).updateCol (σ.symm k) (fun i => C i (σ.symm k)) := by
    intro C
    ext i j
    by_cases h : j = σ.symm k
    · subst h
      rw [Matrix.updateCol_self]
      simp [Equiv.apply_symm_apply]
    · have hne : σ j ≠ k := fun hj => h (by rw [← hj, Equiv.symm_apply_apply])
      rw [Matrix.updateCol_ne h]
      simp [Function.update_of_ne hne]
  rw [key (M + N), key M, key N]
  have hsplit : (fun i => (M + N) i (σ.symm k))
      = (fun i => M i (σ.symm k)) + (fun i => N i (σ.symm k)) := rfl
  rw [hsplit, Matrix.det_updateCol_add]

end MixedDiscriminant
