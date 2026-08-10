import Mathlib
import RamaLean.Paper2

/-!
# The Fibonacci-Lucas evaluation, in general

`Paper2.cor2_fibLucas` and `Paper2.cor2_phi3` were `native_decide` checks over `n ≤ 6`, `r ≤ 6`.
This file proves both for all `n` and `r`, so the corollary is no longer bounded.

## What has to be shown

Writing `u` for the Chebyshev-like sequence `useq t` with `t = L_m`, the content is

  `F_m · u_k = F_{m(k+1)}`   for even `m`,

which by the recurrence `u_{k+2} = t u_{k+1} - u_k` reduces to the Fibonacci identity

  `F_{j+2m} + F_j = L_m · F_{j+m}`   for even `m`,

valid for every `j`.  Stated that way it has no subtraction, so it can be proved in `ℕ` cast to
`ℤ` by a two-step induction on `j`: the statement is linear in the Fibonacci sequence, so the
step is just the sum of the two previous cases.

The two base cases are the classical ones.  At `j = 0` it is `F_{2m} = L_m F_m`, which is
Mathlib's `Nat.fib_two_mul` once `L_m` is written as `2F_{m+1} - F_m`, an identity that avoids
`m - 1` and so avoids truncated subtraction.  At `j = 1` it is `F_{2m+1} + 1 = L_m F_{m+1}`,
which is `Nat.fib_two_mul_add_one` together with Cassini's identity
`F_{m+1}² - F_m F_{m+1} - F_m² = (-1)^m`, proved here by induction; the parity of `m` enters
exactly once, and it is where the hypothesis that `m` is even is used.
-/

namespace Paper2FibLucas

open Nat

/-! ## Lucas numbers without truncated subtraction -/

/-- `L_m = 2F_{m+1} - F_m`.  This is the form that avoids `F_{m-1}` and hence avoids natural
subtraction throughout. -/
theorem lucas_eq (m : ℕ) : (Paper2.lucas m : ℤ) = 2 * (fib (m + 1) : ℤ) - (fib m : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [Paper2.lucas]
    | 1 => simp [Paper2.lucas]
    | (k + 2) =>
      have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      have hf : (fib (k + 2) : ℤ) = fib k + fib (k + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have hf2 : (fib (k + 3) : ℤ) = fib (k + 1) + fib (k + 2) := by
        rw [show k + 3 = (k + 1) + 2 by ring, Nat.fib_add_two]; push_cast; ring
      show (Paper2.lucas k + Paper2.lucas (k + 1) : ℤ) = _
      rw [h1, h2, hf2, hf]; ring

/-! ## Cassini -/

/-- Cassini's identity in the form needed: `F_{m+1}² - F_m F_{m+1} - F_m² = (-1)^m`. -/
theorem cassini (m : ℕ) :
    (fib (m + 1) : ℤ) ^ 2 - (fib m : ℤ) * (fib (m + 1) : ℤ) - (fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hf : (fib (k + 1 + 1) : ℤ) = fib k + fib (k + 1) := by
        rw [show k + 1 + 1 = k + 2 by ring, Nat.fib_add_two]; push_cast; ring
      rw [hf, show ((-1 : ℤ)) ^ (k + 1) = -((-1 : ℤ) ^ k) by ring]
      linear_combination -ih

/-! ## The two base cases -/

/-- `F_{2m} = L_m F_m`. -/
theorem fib_two_mul_lucas (m : ℕ) :
    (fib (2 * m) : ℤ) = (Paper2.lucas m : ℤ) * (fib m : ℤ) := by
  have hle : fib m ≤ 2 * fib (m + 1) := by
    have := Nat.fib_le_fib_succ (n := m)
    omega
  have h := Nat.fib_two_mul m
  have : (fib (2 * m) : ℤ) = (fib m : ℤ) * (2 * (fib (m + 1) : ℤ) - (fib m : ℤ)) := by
    rw [h]; push_cast [Nat.cast_sub hle]; ring
  rw [this, lucas_eq]; ring

/-- `F_{2m+1} + 1 = L_m F_{m+1}` for even `m`.  This is where the parity is used. -/
theorem fib_two_mul_add_one_lucas {m : ℕ} (hm : Even m) :
    (fib (2 * m + 1) : ℤ) + 1 = (Paper2.lucas m : ℤ) * (fib (m + 1) : ℤ) := by
  have hc := cassini m
  have hpar : ((-1 : ℤ)) ^ m = 1 := hm.neg_one_pow
  rw [hpar] at hc
  have h := Nat.fib_two_mul_add_one m
  have hcast : (fib (2 * m + 1) : ℤ) = (fib (m + 1) : ℤ) ^ 2 + (fib m : ℤ) ^ 2 := by
    rw [h]; push_cast; ring
  rw [hcast, lucas_eq]
  nlinarith [hc]

/-! ## The shift identity -/

/-- **The identity the recursion needs.**  For even `m` and every `j`,
`F_{j+2m} + F_j = L_m F_{j+m}`.  Two-step induction on `j`: the statement is linear in the
Fibonacci sequence, so the step is the sum of the two previous cases. -/
theorem fib_shift {m : ℕ} (hm : Even m) :
    ∀ j : ℕ, (fib (j + 2 * m) : ℤ) + (fib j : ℤ) = (Paper2.lucas m : ℤ) * (fib (j + m) : ℤ) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simpa using fib_two_mul_lucas m
    | 1 => simpa [Nat.add_comm] using fib_two_mul_add_one_lucas hm
    | (k + 2) =>
      have h0 := ih k (by omega)
      have h1 := ih (k + 1) (by omega)
      have e1 : (fib (k + 2 + 2 * m) : ℤ) = fib (k + 2 * m) + fib (k + 1 + 2 * m) := by
        rw [show k + 2 + 2 * m = (k + 2 * m) + 2 by ring, Nat.fib_add_two]
        push_cast; ring
      have e2 : (fib (k + 2) : ℤ) = fib k + fib (k + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have e3 : (fib (k + 2 + m) : ℤ) = fib (k + m) + fib (k + 1 + m) := by
        rw [show k + 2 + m = (k + m) + 2 by ring, Nat.fib_add_two]
        push_cast; ring
      rw [e1, e2, e3]; linarith [h0, h1]

/-! ## The evaluation, for all `n` and `r` -/

/-- **`F_m · u_k = F_{m(k+1)}` for even `m`, all `k`.**  This is `Paper2.cor2_fibLucas` without
the bound on `n` and `k`. -/
theorem useq_fib {m : ℕ} (hm : Even m) :
    ∀ k : ℕ, (fib m : ℤ) * Paper2.useq (Paper2.lucas m) k = (fib (m * (k + 1)) : ℤ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [Paper2.useq]
    | 1 =>
        show (fib m : ℤ) * Paper2.lucas m = _
        rw [show m * (1 + 1) = 2 * m by ring, fib_two_mul_lucas]; ring
    | (j + 2) =>
      have h0 := ih j (by omega)
      have h1 := ih (j + 1) (by omega)
      have hs := fib_shift hm (m * (j + 1))
      have em1 : m * (j + 1) + m = m * (j + 2) := by ring
      have em2 : m * (j + 1) + 2 * m = m * (j + 3) := by ring
      rw [em1, em2] at hs
      show (fib m : ℤ) * (Paper2.lucas m * Paper2.useq (Paper2.lucas m) (j + 1)
            - Paper2.useq (Paper2.lucas m) j) = _
      have expand : (fib m : ℤ) * (Paper2.lucas m * Paper2.useq (Paper2.lucas m) (j + 1)
            - Paper2.useq (Paper2.lucas m) j)
          = Paper2.lucas m * ((fib m : ℤ) * Paper2.useq (Paper2.lucas m) (j + 1))
            - (fib m : ℤ) * Paper2.useq (Paper2.lucas m) j := by ring
      rw [expand, h0, h1, show j + 1 + 1 = j + 2 by ring]
      have : m * (j + 2 + 1) = m * (j + 3) := by ring
      rw [this]
      linarith [hs]

/-- **Corollary 2, for all `n` and `r`.**  `F_{2n} · Φ_{C_n,r}(3) = (L_{2n} - 2) · F_{2nr}`,
replacing the `native_decide` check over `n, r ≤ 6`.  The parity hypothesis of `useq_fib` is
automatic here, the index being `2n`. -/
theorem cor2_phi3_general (n r : ℕ) (hr : 1 ≤ r) :
    (fib (2 * n) : ℤ) * Paper2.Phi3 n r
      = ((Paper2.lucas (2 * n) : ℤ) - 2) * (fib (2 * n * r) : ℤ) := by
  have hm : Even (2 * n) := ⟨n, by ring⟩
  match r, hr with
  | 1, _ =>
      show (fib (2 * n) : ℤ)
          * (Paper2.useq (Paper2.lucas (2 * n)) 1 - 2 * Paper2.useq (Paper2.lucas (2 * n)) 0) = _
      have h := useq_fib hm 0
      simp only [Paper2.useq] at h ⊢
      rw [show 2 * n * 1 = 2 * n by ring]
      simp only [mul_one] at h
      linarith [h]
  | (k + 2), _ =>
      have hred := Paper2.cor2_reduction (Paper2.lucas (2 * n)) k
      have h := useq_fib hm (k + 1)
      show (fib (2 * n) : ℤ)
          * (Paper2.useq (Paper2.lucas (2 * n)) (k + 2)
             - 2 * Paper2.useq (Paper2.lucas (2 * n)) (k + 1)
             + Paper2.useq (Paper2.lucas (2 * n)) k) = _
      rw [hred, show 2 * n * (k + 2) = 2 * n * (k + 1 + 1) by ring]
      have : (fib (2 * n) : ℤ)
          * ((Paper2.lucas (2 * n) - 2) * Paper2.useq (Paper2.lucas (2 * n)) (k + 1))
          = (Paper2.lucas (2 * n) - 2)
            * ((fib (2 * n) : ℤ) * Paper2.useq (Paper2.lucas (2 * n)) (k + 1)) := by ring
      rw [this, h]

end Paper2FibLucas
