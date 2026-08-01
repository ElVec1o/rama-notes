import Mathlib

/-!
# The coefficient extraction behind `prop:top`

Paper 4 proves that for each fixed `k` the coefficient of `x^{|V|d-2k}` in the
`d`-matching polynomial is a polynomial `c_k(d)` in `d` of degree `k`, and computes its
top two coefficients:

  `[d^k] c_k = |E|^k / k!`,      `[d^{k-1}] c_k = -(|E|^{k-2}/(k-2)!)(|E|/2 + P)`.

The proof runs an inclusion–exclusion, `m_k = C(M,k) - p_2 C(M-2,k-2) + ⋯` with `M = |E|d`
and `p_2 = P d`, and then reads off the top two coefficients of `C(M,k)` as a polynomial
in `d`.  That reading-off is the step formalized here, and it is the only genuinely
computational step in the proof: everything else is bookkeeping about which
inclusion–exclusion terms can reach order `d^{k-1}`.

Writing `L E k = ∏_{i<k} (E·X - i)`, so that `C(Ed,k) = L E k / k!` evaluated at `d`, the
content is

  `(L E k).coeff k = E^k`,     `(L E (k+1)).coeff k = -(∑_{i<k+1} i)·E^k`,

the second giving the `-C(k,2) E^{k-1}` of the paper.  `binom_two_div_factorial` is the
arithmetic that turns `-C(k,2)/k!` into `-1/(2(k-2)!)`, and `top_two_coeff` assembles the
two contributions into the stated formula.

Nothing here needs the `d`-matching polynomial itself; the statement is about the falling
factorial, which is what the paper's proof actually manipulates.
-/

namespace Paper4Coeff

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- `L E k = ∏_{i<k} (E·X - i)`, the falling factorial in the variable scaled by `E`.
Over `ℚ`, `C(E·d, k) = (L E k).eval d / k!`. -/
noncomputable def L (E : R) (k : ℕ) : Polynomial R :=
  ∏ i ∈ range k, (C E * X - C (i : R))

@[simp] theorem L_zero (E : R) : L E 0 = 1 := by simp [L]

theorem L_succ (E : R) (k : ℕ) : L E (k + 1) = L E k * (C E * X - C (k : R)) := by
  simp [L, Finset.prod_range_succ]

/-- The coefficient recurrence for a linear factor. -/
theorem coeff_mul_linear (p : Polynomial R) (E c : R) (n : ℕ) :
    (p * (C E * X - C c)).coeff (n + 1) = E * p.coeff n - c * p.coeff (n + 1) := by
  have h : p * (C E * X - C c) = C E * (p * X) - C c * p := by ring
  rw [h, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_mul_X]

/-- `L E k` has degree at most `k`. -/
theorem L_natDegree_le (E : R) (k : ℕ) : (L E k).natDegree ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [L_succ]
      refine le_trans (natDegree_mul_le) ?_
      have hCX : (C E * X : Polynomial R).natDegree ≤ 1 :=
        le_trans (natDegree_C_mul_le _ _) natDegree_X_le
      have h1 : (C E * X - C (k : R)).natDegree ≤ 1 := by
        refine le_trans (natDegree_sub_le _ _) ?_
        simp [hCX]
      omega

/-- Coefficients above the degree vanish. -/
theorem L_coeff_of_gt (E : R) (k n : ℕ) (h : k < n) : (L E k).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (L_natDegree_le E k) h)

/-- **The leading coefficient.**  `[X^k] L E k = E^k`, which is the `|E|^k d^k/k!` of the
paper once divided by `k!`. -/
theorem L_coeff_top (E : R) (k : ℕ) : (L E k).coeff k = E ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [L_succ, coeff_mul_linear, ih, L_coeff_of_gt E k (k + 1) (Nat.lt_succ_self k)]
      ring

/-- **The next coefficient.**  `[X^k] L E (k+1) = -(∑_{i<k+1} i)·E^k`; with
`∑_{i<k+1} i = C(k+1,2)` this is the `-C(k,2)|E|^{k-1}` of the paper (at `k+1` in place of
`k`). -/
theorem L_coeff_next (E : R) (k : ℕ) :
    (L E (k + 1)).coeff k = -((∑ i ∈ range (k + 1), (i : R)) * E ^ k) := by
  induction k with
  | zero => simp [L_succ]
  | succ k ih =>
      rw [L_succ, coeff_mul_linear, ih, L_coeff_top E (k + 1)]
      rw [Finset.sum_range_succ (fun i => (i : R)) (k + 1)]
      push_cast
      ring

/-- The arithmetic that converts the paper's two contributions into one: for `k ≥ 2`,
`C(k,2)/k! = 1/(2·(k-2)!)`. -/
theorem binom_two_div_factorial (k : ℕ) (hk : 2 ≤ k) :
    (Nat.choose k 2 : ℚ) / (Nat.factorial k : ℚ)
      = 1 / (2 * (Nat.factorial (k - 2) : ℚ)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hfac : (Nat.factorial (j + 2) : ℚ)
      = ((j + 2 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ) * (Nat.factorial j : ℚ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hch : (Nat.choose (j + 2) 2 : ℚ) = ((j + 2 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hpos : (Nat.factorial j : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  simp only [Nat.add_sub_cancel]
  rw [hch, hfac]
  field_simp

/-- **The top two coefficients, assembled.**  The paper's `prop:top` reads
`[d^{k-1}] c_k = -(E^{k-2}/(k-2)!)(E/2 + P)`; the two contributions are
`-C(k,2) E^{k-1}/k!` from `C(Ed,k)` and `-P E^{k-2}/(k-2)!` from `-p_2 C(Ed-2,k-2)`, and
they combine exactly. -/
theorem top_two_coeff (E P : ℚ) (k : ℕ) (hk : 2 ≤ k) :
    -((Nat.choose k 2 : ℚ) / (Nat.factorial k : ℚ)) * E ^ (k - 1)
      - P * E ^ (k - 2) / (Nat.factorial (k - 2) : ℚ)
      = -(E ^ (k - 2) / (Nat.factorial (k - 2) : ℚ)) * (E / 2 + P) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [binom_two_div_factorial (j + 2) hk]
  have hpow : E ^ (j + 2 - 1) = E ^ j * E := by
    have : j + 2 - 1 = j + 1 := by omega
    rw [this, pow_succ]
  have hpos : (Nat.factorial j : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  simp only [Nat.add_sub_cancel, hpow]
  field_simp
  ring

end Paper4Coeff
