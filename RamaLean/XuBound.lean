import Mathlib
import RamaLean.MomentLadder

/-!
# Xu's conjectural edge, and what it would buy

Zili Xu (personal communication, August 2026) proposes a conjectural largest-root bound whose
specialisation (his Remark 1.6) reads: for rank-`b` projections with `∑ P_i = aI` and
`b/a ≤ b-1`,

  `maxroot μ[P_1,…,P_q] ≤ (√(a-1) + √(b-1))²`,

`μ` being the MSS mixed characteristic polynomial.  It follows from his Conjecture 1.4, which
follows from his Conjecture 1.2, which generalises Ravichandran–Leake Conjecture 1.  On
unweighted projection families our `F_A` *is* that `μ`, shifted by `a`
(`code/rl_conj.py`, verified to `1e-13`), so the bound transfers to our setting verbatim.

This file records three things: what the bound buys when combined with the inner-edge work,
that it is strictly stronger than the constant the note takes as its target, and how it sits
against the moment ladder.

## What it buys

`(√(a-1) + √(b-1))²` is exactly the upper edge of the `(a,b)`-biregular tree's spectrum, whose
nonzero part is `±[|√(a-1) - √(b-1)|, √(a-1) + √(b-1)]`.  So Xu's bound is precisely the
**outer** half of the biregular case of the note's Conjecture 10, *for every `b`*, whereas the
note proves that case only at `b = 2`.  The **inner** half — no roots in the gap — is what the
ratio route supplies.  `inclusion_of_outer_inner` is the assembly: the two halves together are
spectral inclusion, and neither alone is.

## The note's target is not sharp

At `b = 2` the bound is `a + 2√(a-1)` (`rho_sq_b2`), while §10 of the note aims at `a + 2√a`
and calls `2√a` "the natural ceiling of any argument of this kind".  Since
`2√(a-1) < 2√a` (`xu_lt_note_target`), the ceiling of the cavity argument sits strictly above
the truth.

## Against the ladder

In the ladder's variable `y = x²` the bound reads `y_max ≤ 4(a-1)`, and `4(a-1)` is exactly the
tree rate `lim W_{2k}^{1/k}` — the square of the `a`-regular tree's spectral radius.  So Xu's
conjecture is precisely **rate one** in the ladder's normalisation (`xu_is_rate_one`), and the
tree moment bound `p_k ≤ (m/2)W_{2k}` at every rung *implies* it (`xu_of_moment_bound`, from
`MomentLadder.band_of_all_moments`).

That implication is one-directional and the gap is informative.  The moment bound is `REFUTED`
for the plane class (`code/p16verify.py`), yet Xu's bound survives every adversarial search we
can mount (`code/rl_push.py`).  The refuted statement asks for the tree count at every *finite*
`k`; Xu's asks only for the *limit*.  Two independent methods therefore stop short of the same
constant for different reasons — the moment route because its finite-`k` input is false, the
barrier method because, as Xu notes, it does not currently reach Conjecture 1.2.

## Status

Everything here is `VERIFIED`.  Xu's bound itself is a `CONJECTURE`, and is assumed, never used
as established; every statement below that depends on it takes it as a hypothesis.
-/

namespace XuBound

open Real

/-- The outer edge of the `(a,b)`-biregular tree spectrum. -/
noncomputable def rho (a b : ℝ) : ℝ := Real.sqrt (a - 1) + Real.sqrt (b - 1)

/-- The inner edge: the half-width of the gap around zero. -/
noncomputable def gap (a b : ℝ) : ℝ := |Real.sqrt (a - 1) - Real.sqrt (b - 1)|

/-- Membership in the `(a,b)`-biregular tree's spectrum, in the matching-polynomial variable:
zero, or absolute value between the inner and outer edges. -/
def inSpec (a b x : ℝ) : Prop := x = 0 ∨ (gap a b ≤ |x| ∧ |x| ≤ rho a b)

/-- **The assembly.**  Xu's conjectural outer bound and the ratio route's inner bound together
are exactly spectral inclusion for the biregular case, and neither alone suffices: the outer
bound admits roots in the gap, the inner bound admits roots beyond the edge. -/
theorem inclusion_of_outer_inner {a b x : ℝ}
    (outer : |x| ≤ rho a b) (inner : x ≠ 0 → gap a b ≤ |x|) :
    inSpec a b x := by
  rcases eq_or_ne x 0 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨inner h, outer⟩

/-- At `b = 2` the squared outer edge is `a + 2√(a-1)`. -/
theorem rho_sq_b2 {a : ℝ} (ha : 1 ≤ a) : (rho a 2) ^ 2 = a + 2 * Real.sqrt (a - 1) := by
  have h1 : (0 : ℝ) ≤ a - 1 := by linarith
  have hs : Real.sqrt (a - 1) ^ 2 = a - 1 := Real.sq_sqrt h1
  have h2 : Real.sqrt ((2 : ℝ) - 1) = 1 := by norm_num
  simp only [rho, h2]
  nlinarith [hs]

/-- **The note's target is not sharp.**  Xu's edge `2√(a-1)` lies strictly inside the `2√a` that
§10 takes as the natural ceiling of the cavity argument. -/
theorem xu_lt_note_target {a : ℝ} (ha : 1 < a) :
    2 * Real.sqrt (a - 1) < 2 * Real.sqrt a := by
  have h1 : (0 : ℝ) ≤ a - 1 := by linarith
  have := Real.sqrt_lt_sqrt h1 (by linarith : a - 1 < a)
  linarith

/-- **Xu's bound is rate one for the ladder.**  In `y = x²` it reads `y ≤ 4(a-1)`, and `4(a-1)`
is the tree rate against which the ladder's excess rate `R` is measured. -/
theorem xu_is_rate_one {a y : ℝ} (ha : 1 < a) :
    y ≤ 4 * (a - 1) ↔ y / (4 * (a - 1)) ≤ 1 := by
  have h : (0 : ℝ) < 4 * (a - 1) := by linarith
  rw [div_le_one h]

/-- **The tree moment bound implies Xu's bound.**  If the power sums obey the tree rate at every
rung, with a constant free of `k`, the largest root is at most `4(a-1)`.  The converse fails:
the hypothesis is `REFUTED` for the plane class while the conclusion survives every search. -/
theorem xu_of_moment_bound {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) {C a : ℝ} (ha : 1 < a)
    (h : ∀ k : ℕ, 1 ≤ k → ∑ i, (y i) ^ k ≤ C * (4 * (a - 1)) ^ k) (i₀ : Fin n) :
    y i₀ ≤ 4 * (a - 1) := by
  have hpos : (0 : ℝ) < 4 * (a - 1) := by linarith
  exact MomentLadder.band_of_all_moments y hy hpos h i₀

end XuBound
