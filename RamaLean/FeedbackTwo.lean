import Mathlib
import RamaLean.GapLabel
import RamaLean.FeedbackGapCount
import RamaLean.TieBreak

/-!
# Feedback vertex number two

At feedback vertex number one the Schur complement `S_v(x)` is a single element of
`C*_r(F_b)`, projectionless by Pimsner–Voiculescu, hence definite, and its trace alone
decides everything.  At `k = 2` that collapses: `M_2(C*_r(F_b))` is **not** projectionless,
`diag(1,0)` being a counterexample, so `S(x)` can be genuinely indefinite.  This is the
barrier the whole operator-algebra line has sat behind.

What survives of Pimsner–Voiculescu is the K-theory, and it is enough to keep the problem
finite.  `K₀(M_2(C*_r(F_b))) ≅ K₀(C*_r(F_b)) = ℤ·[1]`, so the trace of the negative spectral
projection of `S(x)` is an integer, and being a subprojection of `1` it lies in `{0,1,2}`.
Write it `δ(x)`.

Three facts then bracket the root count, and a fourth picks it out.

* **Inertia.**  Haynsworth additivity gives `κ(x) = N_F(x) + δ(x)`, where `F = G - v₁ - v₂`.
* **Window.**  Vertex-deletion interlacing twice, `μ_G ≻ μ_{G-v₁} ≻ μ_F`, gives
  `N_G(x) - N_F(x) ∈ {0,1,2}`.  That is `window_two`.
* **Parity.**  `N_G ≡ N_F + δ` mod 2, from the sign of `μ_G/μ_F`.

Parity now leaves a two-way choice, between `δ = 0` and `δ = 2`, because both are even.
That is exactly one bit short, and the missing bit is available:

* **Tie-break.**  `δ = 0` means `S(x) > 0` and `δ = 2` means `S(x) < 0`, so the sign of
  `τ(S(x))` separates them.  And that trace is a matching-polynomial ratio.  By the same
  no-bypass argument that gives the `k = 1` formula, the diagonal entries satisfy
  `τ(S₁₁) = μ_{G-v₂}/μ_F` and `τ(S₂₂) = μ_{G-v₁}/μ_F`, so

    `τ(S(x)) = (μ_{G-v₁}(x) + μ_{G-v₂}(x)) / μ_{G-v₁-v₂}(x)`,

  computable from matching polynomials alone.  That is `trace_two`.

`eq_of_window3` is the arithmetic that closes it, and `gapcount_fvs_two_of` assembles.

## Status: `hcount0` is now proved, and `hparity` is the gap

`hcount0` asserts that the root count reads the tie-break sign back.  It **is** a theorem,
`TieBreak.tiebreak_iff`, and it needs nothing but vertex-deletion interlacing: in the even
case the squeeze forces `N_{G-v₁} = N_{G-v₂}`, so the two summands of `τ(S)` share a sign
and their sum has it.  No condition on `spec(T)` enters.  `gapcount_fvs_two_sign` below
discharges it.

The remaining gap is `hparity`, `N_G ≡ N_F + δ` mod 2.  At `k = 1` that came free, because
`τ(S_v) = μ_G/μ_F` and a definite element has a strictly signed trace.  At `k = 2` the
corresponding object is `μ_G/μ_F = CT_z det S(x,z)`, the constant term of the abelianised
determinant, and there is no evident reason for its sign to be `(-1)^δ`: `S(x)` is `2×2`
over a noncommutative algebra and `CT det` is not a determinant of scalars.  Assuming it
would be assuming part of what is to be proved.

So feedback vertex number two is **reduced, not proved**, and the reduction is now to a
single statement with the operator algebra still in it:

  for `x` outside `spec(T)`, `N_G(x) - N_F(x)` is odd exactly when `S(x)` is indefinite.

`code/fvs2_tiebreak.py` and `code/tiebreak_sweep.py` cover the tie-break, which is settled.
Nothing yet covers the parity.
-/

namespace FeedbackTwo

open GapLabel FeedbackGapCount

/-! ## Arithmetic -/

/-- Shifting the exponent by two does not change the sign. -/
theorem neg_one_pow_add_two (n : ℕ) : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
  rw [pow_add]; norm_num

/-- **Window of width three, parity, and one tie-break bit.**

Parity confines `N` to the two values in `{M, M+1, M+2}` of the right parity.  When `d` is
odd that is a single value.  When `d` is even it is `{M, M+2}`, and `htie` chooses. -/
theorem eq_of_window3 {N M d : ℕ}
    (hwin : N = M ∨ N = M + 1 ∨ N = M + 2)
    (hd : d = 0 ∨ d = 1 ∨ d = 2)
    (hpar : (-1 : ℝ) ^ N = (-1 : ℝ) ^ (M + d))
    (htie : d ≠ 1 → (N = M ↔ d = 0)) :
    N = M + d := by
  have hsucc := neg_one_pow_ne_succ M
  rcases hd with rfl | rfl | rfl
  · -- `d = 0`: parity rules out `M+1`, the tie-break rules out `M+2`
    simpa using (htie (by norm_num)).mpr rfl
  · -- `d = 1`: parity rules out both even options
    rcases hwin with h | h | h
    · exact absurd (h ▸ hpar) hsucc
    · exact h
    · exfalso
      rw [h, neg_one_pow_add_two] at hpar
      exact hsucc hpar
  · -- `d = 2`: parity rules out `M+1`, the tie-break rules out `M`
    have hne : ¬ (N = M) := fun h => by simpa using (htie (by norm_num)).mp h
    rcases hwin with h | h | h
    · exact absurd h hne
    · exfalso
      rw [h, neg_one_pow_add_two] at hpar
      exact hsucc hpar.symm
    · exact h

/-! ## The window, from interlacing twice -/

/-- **Window.**  Deleting one vertex moves the root count by at most one, so deleting two
moves it by at most two.  This is vertex-deletion interlacing of matching polynomials
applied along `μ_G ≻ μ_{G-v₁} ≻ μ_{G-v₁-v₂}`. -/
theorem window_two {NG N1 NF : ℕ}
    (h1 : NG = N1 ∨ NG = N1 + 1) (h2 : N1 = NF ∨ N1 = NF + 1) :
    NG = NF ∨ NG = NF + 1 ∨ NG = NF + 2 := by
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | rfl <;> omega

/-! ## The tie-break trace -/

/-- **The trace of the two-by-two Schur complement is a matching-polynomial ratio.**  Each
diagonal entry is the `k = 1` formula for the graph with the other vertex deleted, so the
trace is `(μ_{G-v₁} + μ_{G-v₂})/μ_{G-v₁-v₂}`. -/
theorem trace_two {mF mG1 mG2 t1 t2 : ℝ} (h1 : t1 = mG2 / mF) (h2 : t2 = mG1 / mF) :
    t1 + t2 = (mG1 + mG2) / mF := by
  rw [h1, h2]
  rcases eq_or_ne mF 0 with hmF | hmF
  · simp [hmF]
  · field_simp; ring

/-! ## GAPCOUNT at feedback vertex number two -/

/-- **GAPCOUNT at feedback vertex number two, conditionally.**

`NG`, `N1`, `NF` are the root counts of `μ_G`, `μ_{G-v₁}` and `μ_{G-v₁-v₂}` above the cut;
`delta` is the trace of the negative spectral projection of the `2×2` Schur complement;
`trS` is `τ(S(x))`.

* `hinertia` is Haynsworth additivity.
* `hdelta` is the K-theoretic integrality: `δ ∈ {0,1,2}`.
* `hstep1`, `hstep2` are vertex-deletion interlacing.
* `hparity` is the sign of `μ_G/μ_F` under the trace formula.
* `htie` is definiteness: `δ = 0` forces `S > 0` and `δ = 2` forces `S < 0`, so the sign of
  `τ(S)` separates them, and `hcount0` reads that sign back as the root count.

The conclusion is GAPCOUNT for graphs whose cycles pass through two vertices. -/
theorem gapcount_fvs_two_of {NG N1 NF delta kappa : ℝ → ℕ} {trS : ℝ → ℝ}
    (hinertia : ∀ x, kappa x = NF x + delta x)
    (hdelta : ∀ x, delta x = 0 ∨ delta x = 1 ∨ delta x = 2)
    (hstep1 : ∀ x, NG x = N1 x ∨ NG x = N1 x + 1)
    (hstep2 : ∀ x, N1 x = NF x ∨ N1 x = NF x + 1)
    (hparity : ∀ x, (-1 : ℝ) ^ (NG x) = (-1 : ℝ) ^ (NF x + delta x))
    (htie : ∀ x, delta x ≠ 1 → (0 < trS x ↔ delta x = 0))
    (hcount0 : ∀ x, delta x ≠ 1 → (NG x = NF x ↔ 0 < trS x)) :
    ∀ x, NG x = kappa x := by
  intro x
  rw [hinertia x]
  refine eq_of_window3 (window_two (hstep1 x) (hstep2 x)) (hdelta x) (hparity x) ?_
  intro hne
  exact (hcount0 x hne).trans (htie x hne)

/-- **The same, with `hcount0` discharged.**

`TieBreak.tiebreak_iff` supplies the tie-break from the sign data, so the caller no longer
has to assume it.  What is left to assume, besides the classical inputs, is `hparity`
alone: see the note at the head of this file. -/
theorem gapcount_fvs_two_sign {NG N1 N2 NF delta kappa : ℝ → ℕ}
    {mB1 mB2 mF : ℝ → ℝ}
    (hsB1 : ∀ x, 0 < (-1 : ℝ) ^ (N1 x) * mB1 x)
    (hsB2 : ∀ x, 0 < (-1 : ℝ) ^ (N2 x) * mB2 x)
    (hsF : ∀ x, 0 < (-1 : ℝ) ^ (NF x) * mF x)
    (hinertia : ∀ x, kappa x = NF x + delta x)
    (hdelta : ∀ x, delta x = 0 ∨ delta x = 1 ∨ delta x = 2)
    (hstep1 : ∀ x, NG x = N1 x ∨ NG x = N1 x + 1)
    (hstep1' : ∀ x, N1 x = NF x ∨ N1 x = NF x + 1)
    (hstep2 : ∀ x, NG x = N2 x ∨ NG x = N2 x + 1)
    (hstep2' : ∀ x, N2 x = NF x ∨ N2 x = NF x + 1)
    (hparity : ∀ x, (-1 : ℝ) ^ (NG x) = (-1 : ℝ) ^ (NF x + delta x))
    (htie : ∀ x, delta x ≠ 1 → (0 < mF x * (mB1 x + mB2 x) ↔ delta x = 0))
    (heven : ∀ x, delta x ≠ 1 → (NG x = NF x ∨ NG x = NF x + 2)) :
    ∀ x, NG x = kappa x := by
  refine gapcount_fvs_two_of hinertia hdelta hstep1 hstep1' hparity
    (fun x hx => htie x hx) (fun x hx => ?_)
  exact TieBreak.tiebreak_iff (hsB1 x) (hsB2 x) (hsF x)
    (hstep1 x) (hstep1' x) (hstep2 x) (hstep2' x) (heven x hx)

/-- **Conjecture 10 at feedback vertex number two, through GAPCOUNT.** -/
theorem conj10_fvs_two_of {R : Multiset ℝ} {N1 NF delta kappa : ℝ → ℕ} {trS : ℝ → ℝ}
    {a b : ℝ}
    (hinertia : ∀ x, kappa x = NF x + delta x)
    (hdelta : ∀ x, delta x = 0 ∨ delta x = 1 ∨ delta x = 2)
    (hstep1 : ∀ x, countAbove R x = N1 x ∨ countAbove R x = N1 x + 1)
    (hstep2 : ∀ x, N1 x = NF x ∨ N1 x = NF x + 1)
    (hparity : ∀ x, (-1 : ℝ) ^ (countAbove R x) = (-1 : ℝ) ^ (NF x + delta x))
    (htie : ∀ x, delta x ≠ 1 → (0 < trS x ↔ delta x = 0))
    (hcount0 : ∀ x, delta x ≠ 1 → (countAbove R x = NF x ↔ 0 < trS x))
    (hconst : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo a b, kappa u = kappa v)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo a b) : θ ∉ R :=
  conj10_of_gapcount R kappa
    (fun x _ => gapcount_fvs_two_of hinertia hdelta hstep1 hstep2 hparity htie hcount0 x)
    hconst hθ

end FeedbackTwo
