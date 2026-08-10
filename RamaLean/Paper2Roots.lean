import Mathlib
import RamaLean.Paper2General
import RamaLean.Paper2Unicyclic

/-!
# Real-rootedness of `Φ_{n,r}`, end to end

The corollary that every root of `Φ_{n,r}` lies in `[-2,2]` was formalized only through the
trigonometric factorization (`Paper2.cor1_factored`), not as the statement about roots.  This
file proves the statement.

## The reduction

By the factorization `Φ_{n,r} = χ_{C_n} · U_{r-1}(T_n(x/2))`, that is
`cG Y r = (2Y - 2) · cU Y (r-1)` with `Y = cT (x/2) n`, it suffices that both factors are
nonzero when `|x| > 2`.  `Paper2Unicyclic.cU_ne_zero_of_one_le_abs` already gives the second,
needing `1 ≤ |Y|`.  What is missing is the first factor and the passage from `|x| > 2` to
`|Y| > 1`, both of which come from the same monotonicity: for `z ≥ 1` the Chebyshev values
`cT z n` are increasing and at least one, so for `z > 1` and `n ≥ 1` they exceed one, and the
case `z < -1` follows from `cT (-z) n = (-1)^n cT z n`.

Since `|Y| > 1` gives `2Y - 2 ≠ 0` as well, no root of `Φ_{n,r}` lies outside `[-2,2]`.
-/

namespace Paper2Roots

open Paper2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Chebyshev of the first kind outside the interval -/

/-- For `z ≥ 1` the values `cT z n` are at least one and increasing. -/
lemma cT_ge_one_of_one_le {z : K} (hz : 1 ≤ z) :
    ∀ n, 1 ≤ cT z n ∧ cT z n ≤ cT z (n + 1) := by
  intro n
  induction n with
  | zero =>
      refine ⟨by simp [cT], ?_⟩
      rw [cT_zero, cT_one]; exact hz
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have hk1 : 1 ≤ cT z (k + 1) := le_trans h1 h2
      refine ⟨hk1, ?_⟩
      have hrec : cT z (k + 2) = 2 * z * cT z (k + 1) - cT z k := by
        simp [cT]
      rw [hrec]
      nlinarith [h1, h2, hk1, hz]

lemma cT_ge_one {z : K} (hz : 1 ≤ z) (n : ℕ) : 1 ≤ cT z n := (cT_ge_one_of_one_le hz n).1

/-- For `z > 1` and `n ≥ 1` the value exceeds one, since `cT z 1 = z` and the sequence is
increasing. -/
lemma one_lt_cT {z : K} (hz : 1 < z) : ∀ n, 1 ≤ n → 1 < cT z n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [cT_one]; exact hz
      · have hprev := ih hk
        have hmono := (cT_ge_one_of_one_le (le_of_lt hz) k).2
        exact lt_of_lt_of_le hprev hmono

/-- `cT (-z) n = (-1)^n cT z n`. -/
lemma cT_neg (z : K) : ∀ n, cT (-z) n = (-1 : K) ^ n * cT z n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [cT]
    | 1 => simp [cT]
    | (k + 2) =>
        have h0 := ih k (by omega)
        have h1 := ih (k + 1) (by omega)
        have e : ∀ w : K, cT w (k + 2) = 2 * w * cT w (k + 1) - cT w k := by
          intro w; simp [cT]
        rw [e, e, h0, h1, pow_succ, pow_succ]
        ring

/-- **Outside the interval the Chebyshev value leaves it too**: `|z| > 1` and `n ≥ 1` give
`|cT z n| > 1`. -/
theorem one_lt_abs_cT {z : K} (hz : 1 < |z|) {n : ℕ} (hn : 1 ≤ n) : 1 < |cT z n| := by
  rcases abs_cases z with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hz
    have := one_lt_cT hz n hn
    rw [abs_of_pos (lt_trans one_pos this)]
    exact this
  · have hneg : (1 : K) < -z := by rw [he] at hz; exact hz
    have hval : 1 < cT (-z) n := one_lt_cT hneg n hn
    have hrel : cT (-z) n = (-1 : K) ^ n * cT z n := cT_neg z n
    have : |cT z n| = |cT (-z) n| := by
      rw [hrel, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [this, abs_of_pos (lt_trans one_pos hval)]
    exact hval

/-! ## No root outside the interval -/

/-- **The factored polynomial does not vanish when `|Y| > 1`.**  Both factors are nonzero: the
linear one because `Y ≠ 1`, and the Chebyshev one by `cU_ne_zero_of_one_le_abs`. -/
theorem cG_ne_zero_of_one_lt_abs {Y : K} (hY : 1 < |Y|) (k : ℕ) : cG Y (k + 1) ≠ 0 := by
  rw [cG_factored]
  refine mul_ne_zero ?_ (Paper2Unicyclic.cU_ne_zero_of_one_le_abs (le_of_lt hY) k)
  have hne : Y ≠ 1 := by
    intro h; rw [h] at hY; simp at hY
  intro hzero
  exact hne (by linarith [sub_eq_zero.mp (by linarith [hzero] : 2 * Y - 2 = 0)])

/-- **Corollary: every root of `Φ_{n,r}` lies in `[-2,2]`.**  Stated as the contrapositive: for
`n ≥ 1` and `r ≥ 1`, if `|x| > 2` then `Φ_{n,r}(x) ≠ 0`, where `Φ_{n,r}(x) = cG (cT (x/2) n) r`.

This is the root statement of the corollary, which was previously formalized only through the
trigonometric factorization. -/
theorem Phi_ne_zero_of_two_lt_abs {x : K} (hx : 2 < |x|) {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    cG (cT (x / 2) n) r ≠ 0 := by
  have h2 : (0 : K) < 2 := by norm_num
  have hhalf : 1 < |x / 2| := by
    rw [abs_div, abs_of_pos h2, lt_div_iff₀ h2]
    linarith
  have hY : 1 < |cT (x / 2) n| := one_lt_abs_cT hhalf hn
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact cG_ne_zero_of_one_lt_abs hY k

end Paper2Roots
