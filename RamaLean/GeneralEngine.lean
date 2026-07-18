import Mathlib
import RamaLean.OddPermanentBound
import RamaLean.Paper3LinearRate
import RamaLean.OddEngine
open Matrix Equiv Finset BigOperators

/-!
# The generalized odd-permanent engine (size `2^a + d`)

Generalizes `OddEngine` from sizes `2^a`, `2^a+1` to any `s = 2^a + d` whose offset `d` has all its
prefix digit-sums small: if `max_{y ≤ d} s₂(y) ≤ a − 2`, then in the expansion
`per(2e+J) = Σ_t 2^{|t|}(s−|t|)! π_{|t|}` the digit-sum `s₂(s−t)` is maximized **uniquely** at
`s−t = 2^a−1` (i.e. `t = d+1`), because any `x = 2^a + y` (`y ≤ d`) has `s₂(x) = 1 + s₂(y) ≤ a−1`
and the only `x < 2^a` with `s₂(x) = a` is `2^a−1`.

Machine-checked here:
- `s2_two_pow_add` : `s₂(2^a + y) = 1 + s₂(y)` for `y < 2^a`;
- `s2_eq_of_lt_two_pow` : `x < 2^a` and `s₂(x) = a` ⟹ `x = 2^a − 1`;
- `s2_le_of_le` : `x ≤ 2^a + d` (with the offset hypothesis) ⟹ `s₂(x) ≤ a` — the digit bound;
- `two_pow_dvd_permanent_odd_general` : the **lower half** at every such size:
  `2^(s − a) ∣ per(2e+J)` for all-odd matrices of size `s = 2^a + d`.

This is the divisibility half of the adaptive-peak engine (Paper 3 §7); the exactness half (`π_{d+1}`
odd ⟹ equality) needs the `|t| = d+1` term evaluation — the multi-column generalization of
`OddEngine.permanent_ones_except_col` — and is deferred.
-/
namespace GeneralEngine

/-- `s₂(2^a + y) = 1 + s₂(y)` for `y < 2^a`. -/
lemma s2_two_pow_add : ∀ (a : ℕ) (y : ℕ), y < 2 ^ a →
    (Nat.digits 2 (2 ^ a + y)).sum = 1 + (Nat.digits 2 y).sum := by
  intro a
  induction a with
  | zero =>
    intro y hy
    interval_cases y
    simp
  | succ b ih =>
    intro y hy
    have hpos : 0 < 2 ^ (b + 1) + y := by positivity
    rw [Nat.digits_def' (b := 2) (by norm_num) hpos]
    have hmod : (2 ^ (b + 1) + y) % 2 = y % 2 := by
      have : 2 ^ (b + 1) % 2 = 0 := by rw [pow_succ]; omega
      omega
    have hdiv : (2 ^ (b + 1) + y) / 2 = 2 ^ b + y / 2 := by
      rw [pow_succ]; omega
    rw [hmod, hdiv, List.sum_cons]
    have hy2 : y / 2 < 2 ^ b := by
      rw [pow_succ] at hy; omega
    rw [ih (y / 2) hy2]
    -- s₂(y) = y % 2 + s₂(y / 2)
    rcases Nat.eq_zero_or_pos y with h0 | hyp
    · subst h0; simp
    · rw [Nat.digits_def' (b := 2) (by norm_num) hyp, List.sum_cons]
      omega

/-- Digit-sum bound below a power of two: `m < 2^a ⟹ s₂(m) ≤ a`. -/
lemma s2_le_of_lt_two_pow : ∀ (a m : ℕ), m < 2 ^ a → (Nat.digits 2 m).sum ≤ a := by
  intro a
  induction a with
  | zero => intro m hm; interval_cases m; simp
  | succ b ih =>
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp
    · rw [Nat.digits_def' (b := 2) (by norm_num) hpos, List.sum_cons]
      have h2 : m / 2 < 2 ^ b := by rw [pow_succ] at hm; omega
      have := ih (m / 2) h2
      have : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega

/-- If `x < 2^a` and `s₂(x) = a` then `x = 2^a − 1`. -/
lemma s2_eq_of_lt_two_pow : ∀ (a x : ℕ), x < 2 ^ a →
    (Nat.digits 2 x).sum = a → x = 2 ^ a - 1 := by
  intro a
  induction a with
  | zero => intro x hx _; omega
  | succ b ih =>
    intro x hx hs
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h0 | h
      · subst h0; simp at hs
      · exact h
    rw [Nat.digits_def' (b := 2) (by norm_num) hxpos, List.sum_cons] at hs
    have hdiv2 : x / 2 < 2 ^ b := by rw [pow_succ] at hx; omega
    have hsum2 : (Nat.digits 2 (x / 2)).sum ≤ b := s2_le_of_lt_two_pow b (x / 2) hdiv2
    have hmod2 : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
    -- forces x % 2 = 1 and s₂(x/2) = b
    have hm1 : x % 2 = 1 := by omega
    have hsb : (Nat.digits 2 (x / 2)).sum = b := by omega
    have hxd := ih (x / 2) hdiv2 hsb
    have hdm := Nat.div_add_mod x 2
    have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    rw [pow_succ]; omega

/-- **Unique-maximizer digit bound** for sizes `s = 2^a + d` with small-offset hypothesis
`max_{y ≤ d} s₂(y) ≤ a − 2`: every `x ≤ s` has `s₂(x) ≤ a`, with equality only at `x = 2^a − 1`. -/
lemma s2_le_and_unique {a d : ℕ} (ha : 2 ≤ a)
    (hd : ∀ y ≤ d, (Nat.digits 2 y).sum ≤ a - 2) :
    ∀ x ≤ 2 ^ a + d, (Nat.digits 2 x).sum ≤ a ∧
      ((Nat.digits 2 x).sum = a → x = 2 ^ a - 1) := by
  intro x hx
  rcases lt_or_ge x (2 ^ a) with hlt | hge
  · exact ⟨s2_le_of_lt_two_pow a x hlt, fun hs => s2_eq_of_lt_two_pow a x hlt hs⟩
  · -- x = 2^a + y with y ≤ d: s₂ = 1 + s₂(y) ≤ 1 + (a−2) = a−1 < a
    obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ a + y := ⟨x - 2 ^ a, by omega⟩
    have hyd : y ≤ d := by omega
    have hylt : y < 2 ^ a := by
      -- hd forces d < 2^a: otherwise y₀ = 2^a − 1 ≤ d has s₂(y₀) = a > a − 2.
      by_contra hc
      push Not at hc
      have hda : 2 ^ a - 1 ≤ d := by omega
      have := hd (2 ^ a - 1) hda
      rw [OddEngine.s2_two_pow_sub_one] at this
      omega
    have hadd := s2_two_pow_add a y hylt
    have hyb := hd y hyd
    refine ⟨by omega, fun hs => by omega⟩

/-- **Generalized engine, lower half.** For any size `s = 2^a + d` with the small-offset digit
hypothesis, every all-odd `s×s` matrix has `2^(s − a) ∣ per(2e+J)`. -/
theorem two_pow_dvd_permanent_odd_general {a d : ℕ} (ha : 2 ≤ a)
    (hd : ∀ y ≤ d, (Nat.digits 2 y).sum ≤ a - 2)
    (e : Matrix (Fin (2 ^ a + d)) (Fin (2 ^ a + d)) ℤ) :
    (2 : ℤ) ^ (2 ^ a + d - a) ∣ (Matrix.of (fun k i => 2 * e k i + 1)).permanent := by
  classical
  rw [OddPerm.permanent_two_mul_add_one]
  apply Finset.dvd_sum
  intro t _
  have h1 : (2 : ℤ) ^ (t.card + (2 ^ a + d - t.card - (Nat.digits 2 (2 ^ a + d - t.card)).sum))
      ∣ 2 ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
    rw [pow_add]
    refine mul_dvd_mul_left _ ?_
    have hf : (2 : ℤ) ^ (2 ^ a + d - t.card - (Nat.digits 2 (2 ^ a + d - t.card)).sum)
        ∣ ((2 ^ a + d - t.card).factorial : ℤ) := by
      exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial (2 ^ a + d - t.card)
    exact hf.trans (OddPerm.factorial_dvd_permanent_off (2 ^ a + d) e t)
  have htc : t.card ≤ 2 ^ a + d := (Finset.card_le_univ t).trans_eq (by simp)
  have hs : (Nat.digits 2 (2 ^ a + d - t.card)).sum ≤ a :=
    (s2_le_and_unique ha hd (2 ^ a + d - t.card) (Nat.sub_le _ _)).1
  have hds : (Nat.digits 2 (2 ^ a + d - t.card)).sum ≤ 2 ^ a + d - t.card := Nat.digit_sum_le 2 _
  have hexp : 2 ^ a + d - a
      ≤ t.card + (2 ^ a + d - t.card - (Nat.digits 2 (2 ^ a + d - t.card)).sum) := by omega
  exact dvd_trans (pow_dvd_pow 2 hexp) h1

end GeneralEngine
