import Mathlib
import RamaLean.Paper3FourDivides
import RamaLean.PermanentFactorial
open Matrix Equiv Finset BigOperators Paper3Four
/-!
# Linear 2-adic lower bound for `a(n) = per[gcd(i,j)]` — fully formalized

`Paper3Linear.two_pow_dvd_permanent : (2:ℤ)^(⌈n/2⌉ − ⌊log₂ n⌋ − 1) ∣ (gcdMat n).permanent`,
i.e. `v₂(a(n)) ≥ ⌈n/2⌉ − log₂ n − 1 ~ n/2` — a **linear** rate (constant `c = ½`),
machine-checked end to end (standard axioms, no `sorry`). Replaces the `½·log₂ n` tower bound
and matches the paper's hand-proof exactly.

Proof pipeline (see `code/v2_linear_rate_proof.md`):
* `gcd_eq_sum_divisors` — Smith pointwise: `gcd(a,b) = ∑_{d∣b} [d∣a] φ(d)`.
* `permanent_expansion` — Smith expansion of the **permanent**:
  `a(n) = ∑_x (∏_i φ(x i)) · per(M_x)` via `Finset.prod_univ_sum` (column multilinearity).
* `factorial_dvd_perm_Mx` — the all-ones columns (`x i = 1`) give `c₁! ∣ per(M_x)`
  (from `PermanentFactorial.factorial_dvd_permanent_of_ones_rows`).
* `two_pow_sub_digitsum_dvd_factorial` (`2^{m−s₂(m)}∣m!`, exact `v₂`), `φ(≥3)` even, and
  `#{x i = 2} ≤ n/2` (`card_even_succ_le`) combine to `2^{(c₁−s₂(c₁))+c₃} ∣` each term, with
  `(c₁−s₂(c₁))+c₃ ≥ ⌈n/2⌉−log₂n−1`.

The sharp constant comes from the **exact** factorial valuation `v₂(c₁!) = c₁ − s₂(c₁)`
(`two_pow_sub_digitsum_dvd_factorial`, from `Nat.sub_one_mul_factorization_factorial`) plus
`s₂(c₁) ≤ log₂ c₁ + 1`.  The tighter `c = 1` (`v₂(a(n)) ~ v₂(n!)`) needs a cancellation
argument and stays open.
-/

namespace Paper3Linear

/-- Milestone 1 (pointwise Smith expansion): `gcd(a,b) = ∑_{d ∣ b} [d ∣ a] · φ(d)`. -/
lemma gcd_eq_sum_divisors (a b : ℕ) (hb : b ≠ 0) :
    (Nat.gcd a b : ℤ) = ∑ d ∈ b.divisors, (if d ∣ a then (Nat.totient d : ℤ) else 0) := by
  have hset : b.divisors.filter (· ∣ a) = (Nat.gcd a b).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdb, _⟩, hda⟩
      exact ⟨⟨hda, hdb⟩, by simp [Nat.gcd_eq_zero_iff, hb]⟩
    · rintro ⟨⟨hda, hdb⟩, _⟩
      exact ⟨⟨hdb, hb⟩, hda⟩
  calc (Nat.gcd a b : ℤ)
      = ((∑ d ∈ (Nat.gcd a b).divisors, Nat.totient d : ℕ) : ℤ) := by rw [Nat.sum_totient]
    _ = ((∑ d ∈ b.divisors.filter (· ∣ a), Nat.totient d : ℕ) : ℤ) := by rw [hset]
    _ = ∑ d ∈ b.divisors, (if d ∣ a then (Nat.totient d : ℤ) else 0) := by
        rw [Nat.cast_sum, Finset.sum_filter]

/-- The 0-1 indicator matrix for a divisor-tuple `x`:  `Mx x k i = [ x i ∣ (k+1) ]`. -/
def Mx {n : ℕ} (x : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun k i => if x i ∣ ((k : ℕ) + 1) then 1 else 0

/-- Milestone 2 (Smith expansion of the **permanent**):
`a(n) = ∑_{x : x i ∣ i+1} (∏_i φ(x i)) · per(M_x)`. -/
lemma permanent_expansion (n : ℕ) :
    (gcdMat n).permanent
      = ∑ x ∈ Fintype.piFinset (fun i : Fin n => ((i : ℕ) + 1).divisors),
          (∏ i, (Nat.totient (x i) : ℤ)) * (Mx x).permanent := by
  have hp : ∀ (M : Matrix (Fin n) (Fin n) ℤ), M.permanent = ∑ σ : Perm (Fin n), ∏ i, M (σ i) i :=
    fun _ => rfl
  rw [hp]
  have hentry : ∀ (σ : Perm (Fin n)) (i : Fin n),
      gcdMat n (σ i) i
        = ∑ d ∈ ((i:ℕ)+1).divisors, if d ∣ ((σ i:ℕ)+1) then (Nat.totient d : ℤ) else 0 := by
    intro σ i
    simp only [gcdMat]
    exact gcd_eq_sum_divisors _ _ (by omega)
  simp_rw [hentry, Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Mx]
  split_ifs <;> simp

/-- Milestone 3: `c₁! ∣ per(M_x)`, where `c₁ = #{i : x i = 1}` indexes the all-ones
columns of `M_x` (equivalently all-ones rows of `M_xᵀ`). Direct from the kernel. -/
lemma factorial_dvd_perm_Mx {n : ℕ} (x : Fin n → ℕ) :
    (((univ.filter (fun i => x i = 1)).card).factorial : ℤ) ∣ (Mx x).permanent := by
  classical
  set s := univ.filter (fun i : Fin n => x i = 1) with hs
  let e : Fin s.card ↪ Fin n :=
    (s.equivFin.symm).toEmbedding.trans (Function.Embedding.subtype (· ∈ s))
  have hrow : ∀ (k : Fin s.card) (j : Fin n), (Mx x)ᵀ (e k) j = 1 := by
    intro k j
    have hmem : e k ∈ s := (s.equivFin.symm k).2
    have hk : x (e k) = 1 :=
      (mem_filter.mp (show e k ∈ univ.filter (fun i => x i = 1) from hmem)).2
    simp only [Matrix.transpose_apply, Mx, hk, one_dvd, if_true]
  have hd := factorial_dvd_permanent_of_ones_rows (Mx x)ᵀ e hrow
  have heq : (Mx x)ᵀ.permanent = (Mx x).permanent := Matrix.permanent_transpose _
  rw [← heq]; exact hd

/-- Binary digit-sum bound `s₂(m) ≤ log₂ m + 1` (each bit `≤ 1`, and `#bits = log₂ m + 1`). -/
lemma digitsum_le_log_succ (m : ℕ) (hm : m ≠ 0) :
    (Nat.digits 2 m).sum ≤ Nat.log 2 m + 1 := by
  calc (Nat.digits 2 m).sum
      ≤ (Nat.digits 2 m).length • 1 :=
        List.sum_le_card_nsmul _ 1 (fun d hd => by
          have := Nat.digits_lt_base (by norm_num) hd; omega)
    _ = Nat.log 2 m + 1 := by
        rw [smul_eq_mul, mul_one, Nat.length_digits 2 m (by norm_num) hm]

/-- **Exact** 2-adic valuation of a factorial (Legendre/Kummer): `2^(m − s₂(m)) ∣ m!`,
where `s₂(m)` is the binary digit sum.  (`v₂(m!) = m − s₂(m)`.) -/
lemma two_pow_sub_digitsum_dvd_factorial (m : ℕ) :
    2 ^ (m - (Nat.digits 2 m).sum) ∣ m.factorial := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two m.factorial_ne_zero]
    have h := Nat.sub_one_mul_factorization_factorial (n := m) Nat.prime_two
    simp only [show (2:ℕ) - 1 = 1 from rfl, one_mul] at h
    omega

/-- The "`i+1` even" indicator over `Fin n` sums to `≤ n/2` (Fin recursion; stated on the
sum so the recursive hypothesis is syntactically identical to the goal for `omega`). -/
lemma sum_even_succ_le : ∀ n : ℕ,
    (∑ i : Fin n, if 2 ∣ ((i:ℕ) + 1) then 1 else 0) ≤ n / 2
  | 0 => by simp
  | (m+1) => by
      have ih := sum_even_succ_le m
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      split_ifs with h
      · have heq : (m + 1) / 2 = m / 2 + 1 := by omega
        rw [heq]; exact Nat.add_le_add_right ih 1
      · rw [Nat.add_zero]; exact le_trans ih (by omega)

/-- At most `n/2` indices of `Fin n` have `i+1` even. -/
lemma card_even_succ_le (n : ℕ) :
    (univ.filter (fun i : Fin n => 2 ∣ ((i:ℕ)+1))).card ≤ n / 2 := by
  rw [Finset.card_filter]; exact sum_even_succ_le n

/-- **Linear 2-adic bound (fully formalized, sharpened to `c = ½`):**
`2^(⌈n/2⌉ − ⌊log₂ n⌋ − 1) ∣ a(n)`, i.e. `v₂(a(n)) ≥ ⌈n/2⌉ − log₂ n − 1 ~ n/2`. -/
theorem two_pow_dvd_permanent (n : ℕ) :
    (2 : ℤ) ^ ((n + 1) / 2 - Nat.log 2 n - 1) ∣ (gcdMat n).permanent := by
  classical
  rw [permanent_expansion]
  apply Finset.dvd_sum
  intro x hx
  rw [Fintype.mem_piFinset] at hx
  set c1 := (univ.filter (fun i : Fin n => x i = 1)).card with hc1
  set c3 := (univ.filter (fun i : Fin n => 3 ≤ x i)).card with hc3
  -- exact factorial valuation:  2^(c₁ − s₂(c₁)) | c₁! | per(M_x)
  have hper : (2 : ℤ) ^ (c1 - (Nat.digits 2 c1).sum) ∣ (Mx x).permanent := by
    have h1 : (2 : ℤ) ^ (c1 - (Nat.digits 2 c1).sum) ∣ (c1.factorial : ℤ) := by
      exact_mod_cast two_pow_sub_digitsum_dvd_factorial c1
    exact h1.trans (factorial_dvd_perm_Mx x)
  have hxpos : ∀ i, 1 ≤ x i := fun i => Nat.pos_of_mem_divisors (hx i)
  -- 2^c3 | ∏ φ(x i)
  have hphi : (2 : ℤ) ^ c3 ∣ ∏ i, (Nat.totient (x i) : ℤ) := by
    calc (2 : ℤ) ^ c3
        = ∏ _i ∈ univ.filter (fun i : Fin n => 3 ≤ x i), (2 : ℤ) := by
          rw [Finset.prod_const, hc3]
      _ ∣ ∏ i ∈ univ.filter (fun i : Fin n => 3 ≤ x i), (Nat.totient (x i) : ℤ) := by
          refine Finset.prod_dvd_prod_of_dvd _ _ (fun i hi => ?_)
          rw [mem_filter] at hi
          exact_mod_cast (Nat.totient_even (by omega : 2 < x i)).two_dvd
      _ ∣ ∏ i, (Nat.totient (x i) : ℤ) :=
          Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
  -- combine:  2^((c₁ − s₂(c₁)) + c₃) | term
  have hterm : (2 : ℤ) ^ ((c1 - (Nat.digits 2 c1).sum) + c3)
      ∣ (∏ i, (Nat.totient (x i) : ℤ)) * (Mx x).permanent := by
    rw [add_comm, pow_add]; exact mul_dvd_mul hphi hper
  -- counting:  ⌈n/2⌉ − log₂n − 1 ≤ (c₁ − s₂(c₁)) + c₃
  have hcount : (n + 1) / 2 - Nat.log 2 n - 1 ≤ (c1 - (Nat.digits 2 c1).sum) + c3 := by
    set c2 := (univ.filter (fun i : Fin n => x i = 2)).card with hc2def
    have hc2 : c2 ≤ n / 2 := by
      refine le_trans (Finset.card_le_card ?_) (card_even_succ_le n)
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      have := hx i; rw [hi] at this; exact (Nat.mem_divisors.mp this).1
    have hpart : c1 + c2 + c3 = n := by
      have hsum : c1 + c2 + c3
          = ∑ i : Fin n, ((if x i = 1 then 1 else 0) + (if x i = 2 then 1 else 0)
              + (if 3 ≤ x i then 1 else 0)) := by
        rw [hc1, hc2def, hc3]
        simp only [Finset.card_filter, Finset.sum_add_distrib]
      rw [hsum, Finset.sum_congr rfl (fun i _ => ?_), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
      have := hxpos i; split_ifs <;> omega
    have hsc1 : (Nat.digits 2 c1).sum ≤ c1 := Nat.digit_sum_le 2 c1
    have hc1n : c1 ≤ n := by
      rw [hc1]; exact (Finset.card_filter_le _ _).trans_eq (by rw [Finset.card_univ, Fintype.card_fin])
    have hs : (Nat.digits 2 c1).sum ≤ Nat.log 2 n + 1 := by
      rcases eq_or_ne c1 0 with h0 | h0
      · simp [h0]
      · exact le_trans (digitsum_le_log_succ c1 h0) (by gcongr)
    omega
  exact (pow_dvd_pow 2 hcount).trans hterm

end Paper3Linear
