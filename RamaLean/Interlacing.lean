import Mathlib
import RamaLean.GapLabel

/-!
# The common interlacing lemma

`BandTheorem` derives BAND from two classical inputs, Godsil–Gutman and
Marcus–Spielman–Srivastava, and carries both as hypotheses.  This file removes the second
one's engine from the dependency chain by proving the lemma it rests on.

**Fell's lemma.**  If `p_1, …, p_m` are monic real-rooted of degree `n` with a common
interlacing, and `p = ∑ c_i p_i` with `c_i ≥ 0` not all zero, then for every `k`

  `min_i λ_k(p_i) ≤ λ_k(p) ≤ max_i λ_k(p_i)`.

The proof splits into two independent halves, and neither is the whole thing.

* **Parity.**  If every `p_i(M)` has the same sign, so does `p(M)`, because a nonnegative
  combination of same-signed reals keeps that sign.  Since a monic polynomial's sign at `M`
  is `(-1)` to the number of roots above `M`, this pins the root count of `p` **modulo 2**
  and no further.  That is `parity_of_combination`.
* **The window.**  Common interlacing confines the count of `p` above `M` to `{j, j+1}` for
  the appropriate `j`, because `p` has exactly one root in each interval cut by the
  interlacing points and `M` lies in one of them.

Modulo 2 plus a window of width 2 is equality.  That is `count_eq_of_window_of_parity`, and
it is the whole trick: neither half alone gives more than a congruence or a two-way choice.

Polynomials are represented by their root multisets, with

  `ev r x = ∏_{t ∈ r} (x - t)`

the monic polynomial with those roots.  This keeps the argument on the sign and counting
content, which is where Fell's lemma lives, rather than in the polynomial API.

What is **not** here is that the `±1` signings of a graph actually have a common
interlacing.  That is the substantial half of Marcus–Spielman–Srivastava and it still
enters `BandTheorem.band_of` as a hypothesis.
-/

namespace Interlacing

open Finset GapLabel

/-! ## Monic polynomials from their roots -/

/-- `ev r x = ∏_{t ∈ r} (x - t)`: the monic polynomial with root multiset `r`. -/
noncomputable def ev (r : Multiset ℝ) (x : ℝ) : ℝ := (r.map (fun t => x - t)).prod

@[simp] theorem ev_zero (x : ℝ) : ev 0 x = 1 := by simp [ev]

@[simp] theorem ev_cons (t : ℝ) (r : Multiset ℝ) (x : ℝ) :
    ev (t ::ₘ r) x = (x - t) * ev r x := by simp [ev]

/-- **Sign from count.**  Off its roots, a monic polynomial has sign `(-1)` to the number of
roots above the point.  Every factor `x - t` is negative exactly when `t` is above `x`. -/
theorem ev_sign (r : Multiset ℝ) {x : ℝ} (hx : x ∉ r) :
    0 < (-1 : ℝ) ^ (countAbove r x) * ev r x := by
  classical
  induction r using Multiset.induction with
  | empty => simp [countAbove]
  | cons t r ih =>
      have hxr : x ∉ r := fun h => hx (Multiset.mem_cons_of_mem h)
      have hxt : x ≠ t := fun h => hx (by rw [h]; exact Multiset.mem_cons_self _ _)
      have hprev := ih hxr
      rcases lt_or_gt_of_ne hxt with hlt | hgt
      · -- `x < t`: the new factor is negative and the count goes up by one
        have hc : countAbove (t ::ₘ r) x = countAbove r x + 1 := by
          simp only [countAbove]; exact Multiset.countP_cons_of_pos _ hlt
        rw [hc, ev_cons, pow_succ]
        have hneg : x - t < 0 := by linarith
        nlinarith [hprev]
      · -- `t < x`: the new factor is positive and the count is unchanged
        have hc : countAbove (t ::ₘ r) x = countAbove r x := by
          simp only [countAbove]
          exact Multiset.countP_cons_of_neg _ (not_lt.mpr hgt.le)
        rw [hc, ev_cons]
        have hpos : 0 < x - t := by linarith
        nlinarith [hprev]

/-! ## Parity: half of Fell's lemma, and only half -/

/-- A nonnegative combination of reals all of one sign keeps that sign, provided one term
is strictly signed and carries positive weight. -/
theorem sign_of_combination {ι : Type*} (I : Finset ι) (c f : ι → ℝ) {s : ℝ}
    (hc : ∀ i ∈ I, 0 ≤ c i) (hf : ∀ i ∈ I, 0 ≤ s * f i)
    {i₀ : ι} (hi₀ : i₀ ∈ I) (hc₀ : 0 < c i₀) (hf₀ : 0 < s * f i₀) :
    0 < s * ∑ i ∈ I, c i * f i := by
  have hrw : s * ∑ i ∈ I, c i * f i = ∑ i ∈ I, c i * (s * f i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw]
  refine Finset.sum_pos' (fun i hi => mul_nonneg (hc i hi) (hf i hi)) ⟨i₀, hi₀, ?_⟩
  exact mul_pos hc₀ hf₀

/-- **Parity.**  If every member of the family has the same number of roots above `M`, the
combination has that number modulo 2.  This is as far as signs go. -/
theorem parity_of_combination {ι : Type*} (I : Finset ι) (c : ι → ℝ) (r : ι → Multiset ℝ)
    (ρ : Multiset ℝ) (M : ℝ) (j : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hroot : ∀ i ∈ I, M ∉ r i) (hρ : M ∉ ρ)
    (hcount : ∀ i ∈ I, countAbove (r i) M = j)
    {i₀ : ι} (hi₀ : i₀ ∈ I) (hc₀ : 0 < c i₀)
    (havg : ev ρ M = ∑ i ∈ I, c i * ev (r i) M) :
    (-1 : ℝ) ^ (countAbove ρ M) = (-1 : ℝ) ^ j := by
  -- every member has sign `(-1)^j` at `M`, hence so does the combination
  have hmem : ∀ i ∈ I, 0 < (-1 : ℝ) ^ j * ev (r i) M := fun i hi => by
    have := ev_sign (r i) (hroot i hi)
    rwa [hcount i hi] at this
  have hcomb : 0 < (-1 : ℝ) ^ j * ∑ i ∈ I, c i * ev (r i) M :=
    sign_of_combination I c (fun i => ev (r i) M) hc
      (fun i hi => (hmem i hi).le) hi₀ hc₀ (hmem i₀ hi₀)
  rw [← havg] at hcomb
  -- and the combination's own sign is `(-1)` to its root count
  have hself := ev_sign ρ hρ
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_one_pow] at hcomb
    rcases Nat.even_or_odd (countAbove ρ M) with hp | hp
    · rw [hj.neg_one_pow, hp.neg_one_pow]
    · rw [hp.neg_one_pow] at hself; nlinarith
  · rw [hj.neg_one_pow] at hcomb
    rcases Nat.even_or_odd (countAbove ρ M) with hp | hp
    · rw [hp.neg_one_pow] at hself; nlinarith
    · rw [hj.neg_one_pow, hp.neg_one_pow]

/-! ## The window, and the trick -/

/-- **Parity plus a window of width two is equality.**  Common interlacing confines the
count to `{j, j+1}`; the sign argument fixes its parity; the two together determine it. -/
theorem count_eq_of_window_of_parity {N j : ℕ} (hwin : N = j ∨ N = j + 1)
    (hpar : (-1 : ℝ) ^ N = (-1 : ℝ) ^ j) : N = j := by
  rcases hwin with h | h
  · exact h
  · exfalso
    rw [h, pow_succ] at hpar
    have hne : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have : (-1 : ℝ) = 1 := by
      field_simp at hpar
      linarith [hpar]
    norm_num at this

/-! ## Fell's lemma -/

/-- **Fell's lemma, in the form BAND consumes.**

`r i` are the root multisets of the family, `ρ` that of the nonnegative combination, and
`M` a point at which every member has exactly `j` roots above it.  The window hypothesis
`hwin` is what common interlacing supplies: the combination has one root in each interval
cut by the interlacing points, and `M` lies in one of them, so its count above `M` is `j`
or `j+1`.

The conclusion is that the combination has exactly `j` roots above `M` too.  Applied at
`M = max_i λ_k(p_i)` with `j = k-1` this gives `λ_k(p) ≤ M`, and at `M = min_i λ_k(p_i)`
with `j = k` it gives `λ_k(p) ≥ M`. -/
theorem fell {ι : Type*} (I : Finset ι) (c : ι → ℝ) (r : ι → Multiset ℝ)
    (ρ : Multiset ℝ) (M : ℝ) (j : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hroot : ∀ i ∈ I, M ∉ r i) (hρ : M ∉ ρ)
    (hcount : ∀ i ∈ I, countAbove (r i) M = j)
    {i₀ : ι} (hi₀ : i₀ ∈ I) (hc₀ : 0 < c i₀)
    (havg : ev ρ M = ∑ i ∈ I, c i * ev (r i) M)
    (hwin : countAbove ρ M = j ∨ countAbove ρ M = j + 1) :
    countAbove ρ M = j :=
  count_eq_of_window_of_parity hwin
    (parity_of_combination I c r ρ M j hc hroot hρ hcount hi₀ hc₀ havg)

end Interlacing
