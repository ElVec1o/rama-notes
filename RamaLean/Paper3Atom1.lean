import Mathlib
open Finset
/-!
# Atom 1: `v₂(A(2^k+1)) = v₂((2^k+1)!) − 1`

`A(n)` is the **odd-φ part** of `a(n)=per[gcd]` in the Smith expansion (the terms with divisor
choice `f(i)∈{1,2}`). It is itself a permanent — of the matrix with `p=⌈n/2⌉` all-ones rows and
`m=⌊n/2⌋` rows `[1,2,1,2,…]` — so by the two identical row-groups it equals
`A(n) = p!·m!·e_m(1^p,2^m)`, where `e_m = Σ_j C(m,j)C(p,m−j)2^j ≡ C(p,m) (mod 2)`.

For `n=2^k+1`: `C(p,m)=C(2^{k−1}+1,2^{k−1})=2^{k−1}+1` is ODD, so `e_m` is odd and
`v₂(A) = v₂(p!)+v₂(m!) = 2(2^{k−1}−1) = 2^k−2 = v₂((2^k+1)!)−1`.  (Machine-checked below.)
This is the rigorous crumb toward the deficit conjecture `v₂(a(2^k+1)) = v₂(n!)−(2k−4)`.
-/

namespace Paper3Atom1

/-- `e_m(1^p, 2^m) = ∑_j C(m,j)·C(p,m−j)·2^j`. -/
def em (p m : ℕ) : ℕ := ∑ j ∈ range (m + 1), m.choose j * p.choose (m - j) * 2 ^ j

/-- Only the `j=0` term is odd, so `e_m ≡ C(p,m) (mod 2)`. -/
lemma em_mod_two (p m : ℕ) : em p m % 2 = p.choose m % 2 := by
  unfold em
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, one_mul, pow_zero, mul_one, Nat.sub_zero]
  have heven : 2 ∣ (∑ j ∈ range m, m.choose (j + 1) * p.choose (m - (j + 1)) * 2 ^ (j + 1)) := by
    apply Finset.dvd_sum
    intro j _
    exact Dvd.dvd.mul_left (dvd_pow_self 2 (Nat.succ_ne_zero j)) _
  omega

/-- `v₂(n!) = n − s₂(n)`. -/
lemma v2_factorial (n : ℕ) : (n.factorial).factorization 2 = n - (Nat.digits 2 n).sum := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  simpa using h

/-- `s₂(2^j) = 1`. -/
lemma s2_two_pow (j : ℕ) : (Nat.digits 2 (2 ^ j)).sum = 1 := by
  induction j with
  | zero => simp
  | succ i ih =>
    have hpos : 0 < 2 ^ (i + 1) := by positivity
    rw [Nat.digits_def' (b := 2) (by norm_num) hpos]
    have h1 : 2 ^ (i + 1) % 2 = 0 := by
      rw [pow_succ]; omega
    have h2 : 2 ^ (i + 1) / 2 = 2 ^ i := by
      rw [pow_succ]; omega
    rw [h1, h2]; simpa using ih

/-- `s₂(2^j + 1) = 2` for `j ≥ 1`. -/
lemma s2_two_pow_succ (j : ℕ) (hj : 1 ≤ j) : (Nat.digits 2 (2 ^ j + 1)).sum = 2 := by
  have hpos : 0 < 2 ^ j + 1 := by positivity
  rw [Nat.digits_def' (b := 2) (by norm_num) hpos]
  have h1 : (2 ^ j + 1) % 2 = 1 := by
    have : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    omega
  have h2 : (2 ^ j + 1) / 2 = 2 ^ (j - 1) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    have e1 : 1 + t - 1 = t := by omega
    rw [e1, pow_add, pow_one]; omega
  rw [h1, h2, List.sum_cons, s2_two_pow]

/-- **Atom 1 (machine-checked).**  `A(2^k+1) = p!·m!·e_m` with `p=2^{k−1}+1`, `m=2^{k−1}`
has `v₂ = 2^k − 2`. -/
theorem v2_A_two_pow_add_one (k : ℕ) (hk : 2 ≤ k) :
    ((2 ^ (k - 1) + 1).factorial * (2 ^ (k - 1)).factorial *
        em (2 ^ (k - 1) + 1) (2 ^ (k - 1))).factorization 2 = 2 ^ k - 2 := by
  set p := 2 ^ (k - 1) + 1 with hp
  set m := 2 ^ (k - 1) with hm
  have hk1 : 1 ≤ k - 1 := by omega
  -- e_m is odd
  have hemodd : em p m % 2 = 1 := by
    rw [em_mod_two, hp, hm]
    have : (2 ^ (k - 1) + 1).choose (2 ^ (k - 1)) = 2 ^ (k - 1) + 1 :=
      Nat.choose_succ_self_right _
    rw [this]
    have : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
    omega
  have hem0 : (em p m).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  -- v₂ of the product
  have hpne : p.factorial ≠ 0 := Nat.factorial_ne_zero p
  have hmne : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hemne : em p m ≠ 0 := by omega
  rw [Nat.factorization_mul (by positivity) hemne, Nat.factorization_mul hpne hmne]
  simp only [Finsupp.add_apply, hem0, add_zero]
  rw [v2_factorial, v2_factorial, hp, hm, s2_two_pow, s2_two_pow_succ _ hk1]
  -- (2^{k-1}+1 - 2) + (2^{k-1} - 1) = 2^k - 2
  have hge : 2 ^ (k - 1) ≥ 2 := by
    calc 2 ^ (k - 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

end Paper3Atom1
