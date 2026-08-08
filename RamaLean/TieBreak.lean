import Mathlib

/-!
# The tie-break sign at feedback vertex number two

`FeedbackTwo` reduces the case of two feedback vertices to one statement about matching
polynomials, carried there as the unearned hypothesis `hcount0`.  This file proves it, and
proves more than was asked: no condition on `spec(T)` is needed, and no operator algebra
appears.  Only vertex-deletion interlacing.

Write `a, b₁, b₂, c` for the number of roots above `x` of `μ_G`, `μ_{G-v₁}`, `μ_{G-v₂}` and
`μ_F` with `F = G - v₁ - v₂`.  Vertex-deletion interlacing gives four relations,

  `a - b₁ ∈ {0,1}`,  `b₁ - c ∈ {0,1}`,  `a - b₂ ∈ {0,1}`,  `b₂ - c ∈ {0,1}`,

so `a - c ∈ {0,1,2}`.  The observation is that in the two **even** cases the intermediate
counts are forced:

* `a = c` squeezes `c ≤ b_i ≤ a = c`, so `b₁ = b₂ = c`;
* `a = c+2` squeezes `c+1 = a-1 ≤ b_i ≤ c+1`, so `b₁ = b₂ = c+1`.

Either way `b₁ = b₂`, so `μ_{G-v₁}(x)` and `μ_{G-v₂}(x)` have the **same** sign and their
sum has it too.  Comparing with the sign of `μ_F(x)` then reads off which of the two cases
holds, which is exactly the missing bit.

`counts_forced` is the squeeze, `sign_sum_of_eq_counts` the sign consequence, and
`tiebreak_iff` the statement `FeedbackTwo` needs.  The proof explains the numerics too: the
statement was verified at every sample point, inside `spec(T)` as well as outside, because
`spec(T)` never enters it.

This does **not** finish feedback vertex number two.  See the note at the end of
`FeedbackTwo`: the remaining gap is the parity link, `a - c = 1` if and only if the Schur
complement is indefinite, and that is untouched here.
-/

namespace TieBreak

/-! ## The squeeze -/

/-- **Interlacing forces the intermediate counts in the even cases.**  If deleting either
vertex moves the count by at most one, and deleting both moves it by exactly zero or
exactly two, then both single deletions move it by the same amount. -/
theorem counts_forced {a b₁ b₂ c : ℕ}
    (h1 : a = b₁ ∨ a = b₁ + 1) (h2 : b₁ = c ∨ b₁ = c + 1)
    (h3 : a = b₂ ∨ a = b₂ + 1) (h4 : b₂ = c ∨ b₂ = c + 1)
    (heven : a = c ∨ a = c + 2) :
    (a = c ∧ b₁ = c ∧ b₂ = c) ∨ (a = c + 2 ∧ b₁ = c + 1 ∧ b₂ = c + 1) := by
  rcases heven with rfl | h
  · left
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  · right
    refine ⟨h, ?_, ?_⟩ <;> omega

/-! ## Signs -/

/-- A monic real-rooted polynomial's sign at `x` is `(-1)` to its root count above `x`;
squaring that factor is the identity. -/
theorem neg_one_pow_sq (c : ℕ) : ((-1 : ℝ) ^ c) * ((-1 : ℝ) ^ c) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨c, rfl⟩

/-- **The sign of the sum.**  When the two single deletions have the same count, the two
polynomials have the same sign and so does their sum, and comparing with `μ_F` reads off
that common count's parity relative to `c`. -/
theorem sign_sum_of_eq_counts {B₁ B₂ C : ℝ} {b c : ℕ}
    (hB₁ : 0 < (-1 : ℝ) ^ b * B₁) (hB₂ : 0 < (-1 : ℝ) ^ b * B₂)
    (hC : 0 < (-1 : ℝ) ^ c * C) :
    0 < ((-1 : ℝ) ^ b * (-1 : ℝ) ^ c) * (C * (B₁ + B₂)) := by
  have hsum : 0 < (-1 : ℝ) ^ b * (B₁ + B₂) := by
    have : (-1 : ℝ) ^ b * (B₁ + B₂) = (-1 : ℝ) ^ b * B₁ + (-1 : ℝ) ^ b * B₂ := by ring
    rw [this]; linarith
  have hmul : 0 < ((-1 : ℝ) ^ c * C) * ((-1 : ℝ) ^ b * (B₁ + B₂)) := mul_pos hC hsum
  calc (0:ℝ) < ((-1 : ℝ) ^ c * C) * ((-1 : ℝ) ^ b * (B₁ + B₂)) := hmul
    _ = ((-1 : ℝ) ^ b * (-1 : ℝ) ^ c) * (C * (B₁ + B₂)) := by ring

/-! ## The tie-break -/

/-- **The tie-break, proved.**

`A, B₁, B₂, C` are the values of `μ_G, μ_{G-v₁}, μ_{G-v₂}, μ_F` at `x`, and `a, b₁, b₂, c`
their root counts above `x`, so the sign hypotheses say each is monic real-rooted with `x`
not a root.  Given the four interlacing relations and that `a - c` is even,

  `a = c`  if and only if  `μ_F(x)` and `μ_{G-v₁}(x) + μ_{G-v₂}(x)` agree in sign.

This is `FeedbackTwo.hcount0`, and nothing in it mentions the universal cover. -/
theorem tiebreak_iff {B₁ B₂ C : ℝ} {a b₁ b₂ c : ℕ}
    (hB₁ : 0 < (-1 : ℝ) ^ b₁ * B₁) (hB₂ : 0 < (-1 : ℝ) ^ b₂ * B₂)
    (hC : 0 < (-1 : ℝ) ^ c * C)
    (h1 : a = b₁ ∨ a = b₁ + 1) (h2 : b₁ = c ∨ b₁ = c + 1)
    (h3 : a = b₂ ∨ a = b₂ + 1) (h4 : b₂ = c ∨ b₂ = c + 1)
    (heven : a = c ∨ a = c + 2) :
    (a = c ↔ 0 < C * (B₁ + B₂)) := by
  rcases counts_forced h1 h2 h3 h4 heven with ⟨ha, hb₁, hb₂⟩ | ⟨ha, hb₁, hb₂⟩
  · -- `b₁ = b₂ = c`: the sum agrees in sign with `μ_F`
    rw [hb₁] at hB₁
    rw [hb₂] at hB₂
    have h := sign_sum_of_eq_counts (b := c) hB₁ hB₂ hC
    rw [neg_one_pow_sq, one_mul] at h
    exact ⟨fun _ => h, fun _ => ha⟩
  · -- `b₁ = b₂ = c+1`: the sum disagrees, so `a ≠ c`
    rw [hb₁] at hB₁
    rw [hb₂] at hB₂
    have h := sign_sum_of_eq_counts (b := c + 1) hB₁ hB₂ hC
    have hcoef : ((-1 : ℝ) ^ (c + 1) * (-1 : ℝ) ^ c) = -1 := by
      rw [← pow_add]
      have he : c + 1 + c = 2 * c + 1 := by ring
      rw [he, pow_succ, pow_mul]
      norm_num
    rw [hcoef] at h
    have hneg : C * (B₁ + B₂) < 0 := by linarith
    constructor
    · intro hac; exfalso; omega
    · intro hpos; linarith

end TieBreak
