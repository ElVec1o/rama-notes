import Mathlib
import RamaLean.GapLabel
import RamaLean.Interlacing

/-!
# GAPCOUNT at feedback vertex number one

`FeedbackVertex` proves, modulo Pimsner–Voiculescu, that when `F = G - v` is a forest every
root of `μ_G` off the roots of `μ_F` lies in `spec(T)`.  That is Conjecture 10 for those
graphs.  This file upgrades it from non-vanishing to counting, which is GAPCOUNT, by the
same window-plus-parity move that `Interlacing` uses for Fell's lemma.

Write `N_G(x)` and `N_F(x)` for the number of roots of `μ_G` and `μ_F` above `x`, and
`κ(x) = τ_n(1_{(-∞,0)}(x I - A_T))` for the gap label.  Three facts combine.

* **Inertia.**  Eliminating the preimage of `F` splits the operator, and Sylvester's law in
  a von Neumann algebra with a trace, i.e. Haynsworth additivity, gives
  `κ(x) = N_F(x) + δ(x)`, where `δ(x) ∈ {0,1}` records whether the Schur complement
  `S_v(x)` is negative.  The forest contributes `N_F(x)` because `F` lifts homeomorphically,
  so `spec(A_F̃) = spec(A_F)` and `μ_F` is the characteristic polynomial of a forest.
  `δ` is `0` or `1` because `S_v(x)` is a single element of `C*_r(F_b)`, definite by
  Pimsner–Voiculescu, and `τ(1) = 1`.
* **Window.**  `μ_F` interlaces `μ_G`.  Classically: Godsil's path tree realises `μ_G` and
  `μ_F` as the characteristic polynomials of a tree and of that tree with its root deleted,
  a principal submatrix, so Cauchy interlacing applies.  Hence
  `N_G(x) - N_F(x) ∈ {0,1}`.
* **Parity.**  `τ(S_v(x)) = μ_G(x)/μ_F(x)`, and a definite element has strictly signed
  trace, so `sign(μ_G(x)/μ_F(x)) = (-1)^{δ(x)}`.  Since a monic real-rooted polynomial has
  sign `(-1)` to its root count above `x`, this says `N_G(x) ≡ N_F(x) + δ(x)` mod 2.

A window of width two and a parity determine the value.  So `N_G(x) = N_F(x) + δ(x) = κ(x)`,
which is GAPCOUNT.

Neither Pimsner–Voiculescu, nor Haynsworth additivity in a von Neumann algebra, nor Godsil's
path tree is in Mathlib.  All three appear as explicit hypotheses of `gapcount_fvs_one_of`.
What is proved here is that they close, and that the closing step is exactly the one already
isolated in `Interlacing.count_eq_of_window_of_parity`.
-/

namespace FeedbackGapCount

open GapLabel Interlacing

/-! ## The arithmetic step -/

/-- `(-1)^n` and `(-1)^(n+1)` differ. -/
theorem neg_one_pow_ne_succ (n : ℕ) : (-1 : ℝ) ^ n ≠ (-1 : ℝ) ^ (n + 1) := by
  intro h
  rw [pow_succ] at h
  have hne : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (1 : ℝ) = -1 := by
    field_simp at h
    linarith [h]
  norm_num at this

/-- **Window plus parity, in the shape the inertia split produces.**  If `N` sits in the
two-element window `{M, M+1}` and has the parity of `M + d` with `d ∈ {0,1}`, then
`N = M + d`. -/
theorem eq_of_window_of_parity {N M d : ℕ} (hwin : N = M ∨ N = M + 1)
    (hd : d = 0 ∨ d = 1) (hpar : (-1 : ℝ) ^ N = (-1 : ℝ) ^ (M + d)) :
    N = M + d := by
  rcases hd with rfl | rfl
  · simpa using count_eq_of_window_of_parity hwin (by simpa using hpar)
  · rcases hwin with h | h
    · exact absurd (h ▸ hpar) (neg_one_pow_ne_succ M)
    · exact h

/-! ## GAPCOUNT for feedback vertex number one -/

/-- **GAPCOUNT at feedback vertex number one, conditionally.**

`NG`, `NF` are the root counts of `μ_G` and `μ_{G-v}` above the cut, `delta` the negativity
indicator of the Schur complement, and `kappa` the gap label.

* `hinertia` is Haynsworth additivity in the traced von Neumann algebra.
* `hdelta` is Pimsner–Voiculescu: `S_v(x)` is definite, so its negative part has trace `0`
  or `1`.
* `hwindow` is Cauchy interlacing through Godsil's path tree: `μ_{G-v}` interlaces `μ_G`.
* `hparity` is the trace formula together with definiteness, read as a sign.

The conclusion is GAPCOUNT: the root count of `μ_G` above `x` is the gap label.  With
`GapLabel.conj10_of_gapcount` this recovers Conjecture 10 for these graphs, now with the
count rather than only the non-vanishing. -/
theorem gapcount_fvs_one_of {NG NF delta kappa : ℝ → ℕ}
    (hinertia : ∀ x, kappa x = NF x + delta x)
    (hdelta : ∀ x, delta x = 0 ∨ delta x = 1)
    (hwindow : ∀ x, NG x = NF x ∨ NG x = NF x + 1)
    (hparity : ∀ x, (-1 : ℝ) ^ (NG x) = (-1 : ℝ) ^ (NF x + delta x)) :
    ∀ x, NG x = kappa x := by
  intro x
  rw [hinertia x]
  exact eq_of_window_of_parity (hwindow x) (hdelta x) (hparity x)

/-- The same conclusion stated against the root multiset, so that it plugs directly into
`GapLabel.conj10_of_gapcount` and hence yields Conjecture 10 on every gap. -/
theorem gapcount_multiset_of {R : Multiset ℝ} {NF delta kappa : ℝ → ℕ}
    (hinertia : ∀ x, kappa x = NF x + delta x)
    (hdelta : ∀ x, delta x = 0 ∨ delta x = 1)
    (hwindow : ∀ x, countAbove R x = NF x ∨ countAbove R x = NF x + 1)
    (hparity : ∀ x, (-1 : ℝ) ^ (countAbove R x) = (-1 : ℝ) ^ (NF x + delta x)) :
    ∀ x, countAbove R x = kappa x :=
  gapcount_fvs_one_of hinertia hdelta hwindow hparity

/-- **Conjecture 10 for feedback vertex number one, through GAPCOUNT.**  Once the count is
the gap label, and the gap label is constant on a gap, no root lies in the gap. -/
theorem conj10_fvs_one_of {R : Multiset ℝ} {NF delta kappa : ℝ → ℕ} {a b : ℝ}
    (hinertia : ∀ x, kappa x = NF x + delta x)
    (hdelta : ∀ x, delta x = 0 ∨ delta x = 1)
    (hwindow : ∀ x, countAbove R x = NF x ∨ countAbove R x = NF x + 1)
    (hparity : ∀ x, (-1 : ℝ) ^ (countAbove R x) = (-1 : ℝ) ^ (NF x + delta x))
    (hconst : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo a b, kappa u = kappa v)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo a b) : θ ∉ R :=
  conj10_of_gapcount R kappa
    (fun x _ => gapcount_multiset_of hinertia hdelta hwindow hparity x) hconst hθ

end FeedbackGapCount
