import Mathlib
import RamaLean.Paper3CMinus1
open Finset BigOperators

/-!
# The digit-sum constant: `Σ_{v < 2^(k−1)} Ω₃(v) ≡ 1 (mod 2)`

In the telescope-vs-residue analysis (Paper 3 §7) the provable stratum of the window normal form
rests on: `Σ_{D∈P} ⌊2^(k−1)/D⌋ ≡ Σ_{v<2^(k−1)} Ω₃(v) (mod 2)` (hyperbola swap), and the right side
equals `#{v < 2^(k−1) : oddpart(v) ≡ 3 (mod 4)} = 2^(k−2) − 1`, which is **odd** — so the pure digit
sum contributes the constant `1` identically. Machine-checked here:

- `omega3_two_pow` — `Ω₃(2^e) = 0`;
- `omega3_ord_iff` — the pointwise identity extended to all `v`: `Ω₃(v)` odd ⟺
  `ordCompl[2] v ≡ 3 (mod 4)` (the odd part of `v`);
- `card_oddpart_three` — `#{v < 2^j : oddpart(v) ≡ 3 (4)} = 2^(j−1) − 1` (`j ≥ 2`), by the
  even/odd dyadic recursion;
- `sum_omega3_digit_odd` — the constant: for `k ≥ 3`, `(Σ_{v < 2^(k−1)} Ω₃(v)) % 2 = 1`.

Together with `Paper3CMinus1` this machine-checks both provable parity strata found by the
telescope analysis.
-/
namespace Paper3DigitSum
open Paper3CMinus1

lemma omega3_two_pow (e : ℕ) : omega3 (2 ^ e) = 0 := by
  unfold omega3
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  rw [Finsupp.sum_single_index (by simp)]
  norm_num

/-- `ordCompl[2]` of an odd number is itself. -/
lemma ord_compl_of_odd {v : ℕ} (hv : v % 2 = 1) : ordCompl[2] v = v := by
  have h2 : ¬ (2 ∣ v) := by omega
  rw [Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one]

/-- `ordCompl[2] (2w) = ordCompl[2] w`. -/
lemma ord_compl_two_mul (w : ℕ) : ordCompl[2] (2 * w) = ordCompl[2] w := by
  rw [Nat.ordCompl_mul]
  have h1 : ordCompl[2] 2 = 1 := by
    rw [Nat.Prime.factorization_self Nat.prime_two]
    norm_num
  rw [h1, one_mul]

/-- Pointwise identity, all `v`: `Ω₃(v)` odd ⟺ the odd part of `v` is `≡ 3 (mod 4)`. -/
lemma omega3_ord_iff (v : ℕ) : omega3 v % 2 = 1 ↔ ordCompl[2] v % 4 = 3 := by
  rcases Nat.eq_zero_or_pos v with h0 | hpos
  · subst h0; simp [omega3]
  · have hsplit := Nat.ordProj_mul_ordCompl_eq_self v 2
    have hx0 : 0 < ordCompl[2] v := Nat.ordCompl_pos 2 (by omega)
    have hxodd : ordCompl[2] v % 2 = 1 := by
      have hnd := Nat.not_dvd_ordCompl Nat.prime_two (by omega : v ≠ 0)
      omega
    have homega : omega3 v = omega3 (ordCompl[2] v) := by
      calc omega3 v = omega3 (ordProj[2] v * ordCompl[2] v) := by rw [hsplit]
        _ = omega3 (ordProj[2] v) + omega3 (ordCompl[2] v) := by
              exact omega3_mul (by positivity) (by omega)
        _ = omega3 (ordCompl[2] v) := by rw [omega3_two_pow]; omega
    rw [homega]
    exact odd_omega3_iff (ordCompl[2] v) hx0 hxodd

/-- `#{v < 2^j : oddpart(v) ≡ 3 (mod 4)} = 2^(j−1) − 1` for `j ≥ 2`. -/
lemma card_oddpart_three : ∀ j, 2 ≤ j →
    ((Finset.range (2 ^ j)).filter (fun v => ordCompl[2] v % 4 = 3)).card = 2 ^ (j - 1) - 1 := by
  intro j
  induction j with
  | zero => omega
  | succ i ih =>
    intro hj
    rcases eq_or_lt_of_le hj with hbase | hstep
    · -- base j = 2 (i = 1): the filter over range 4 is {3}
      have hi : i = 1 := by omega
      subst hi
      have hset : ((Finset.range (2 ^ 2)).filter (fun v => ordCompl[2] v % 4 = 3)) = {3} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨hlt, hc⟩
          interval_cases v
          · have h00 : ordCompl[2] 0 = 0 := Nat.zero_div _
            rw [h00] at hc; omega
          · rw [ord_compl_of_odd (by norm_num)] at hc; omega
          · have : ordCompl[2] 2 = 1 := by
              rw [Nat.Prime.factorization_self Nat.prime_two]; norm_num
            rw [this] at hc; omega
          · rfl
        · rintro rfl
          refine ⟨by norm_num, ?_⟩
          rw [ord_compl_of_odd (by norm_num)]
      rw [hset]
      simp
    · -- step: j = i+1 with i ≥ 2
      have hi2 : 2 ≤ i := by omega
      set F := (Finset.range (2 ^ (i + 1))).filter (fun v => ordCompl[2] v % 4 = 3) with hF
      have hcard := Finset.filter_card_add_filter_neg_card_eq_card
        (s := F) (p := fun v => v % 2 = 1)
      -- odd part of F  =  plain v%4=3 filter over the big range
      have hodd : F.filter (fun v => v % 2 = 1)
          = (Finset.range (2 ^ (i + 1))).filter (fun v => v % 4 = 3) := by
        ext v
        simp only [hF, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨⟨hlt, hc⟩, hoddv⟩
          rw [ord_compl_of_odd hoddv] at hc
          exact ⟨hlt, hc⟩
        · rintro ⟨hlt, hc⟩
          have hoddv : v % 2 = 1 := by omega
          rw [and_assoc]
          refine ⟨hlt, ?_, hoddv⟩
          rw [ord_compl_of_odd hoddv]
          exact hc
      -- even part of F  =  image (2·) of the level-i filter
      have heven : F.filter (fun v => ¬ v % 2 = 1)
          = ((Finset.range (2 ^ i)).filter
              (fun w => ordCompl[2] w % 4 = 3)).image (fun w => 2 * w) := by
        ext v
        simp only [hF, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨⟨hlt, hc⟩, hev⟩
          refine ⟨v / 2, ⟨?_, ?_⟩, by omega⟩
          · have : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
            omega
          · have hv2 : v = 2 * (v / 2) := by omega
            rw [hv2, ord_compl_two_mul] at hc
            exact hc
        · rintro ⟨w, ⟨hw, hcw⟩, rfl⟩
          have : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
          exact ⟨⟨by omega, by rw [ord_compl_two_mul]; exact hcw⟩, by omega⟩
      have hoddcard : (F.filter (fun v => v % 2 = 1)).card = 2 ^ (i - 1) := by
        rw [hodd]
        simpa using card_three_mod_four (by omega : 2 ≤ i + 1)
      have hevencard : (F.filter (fun v => ¬ v % 2 = 1)).card = 2 ^ (i - 1) - 1 := by
        rw [heven, Finset.card_image_of_injective _ (fun a b h => by omega)]
        exact ih hi2
      have hp1 : 1 ≤ 2 ^ (i - 1) := Nat.one_le_two_pow
      have hpow : 2 ^ ((i + 1) - 1) = 2 * 2 ^ (i - 1) := by
        have h1 : (i + 1) - 1 = (i - 1) + 1 := by omega
        rw [h1, pow_succ]; ring
      omega

/-- **The digit-sum constant is 1**: for `k ≥ 3`, `(Σ_{v < 2^(k−1)} Ω₃(v)) % 2 = 1`. -/
theorem sum_omega3_digit_odd {k : ℕ} (hk : 3 ≤ k) :
    (∑ v ∈ Finset.range (2 ^ (k - 1)), omega3 v) % 2 = 1 := by
  classical
  rw [Finset.sum_nat_mod]
  have hpt : ∀ v ∈ Finset.range (2 ^ (k - 1)),
      omega3 v % 2 = (if ordCompl[2] v % 4 = 3 then 1 else 0) := by
    intro v _
    by_cases h3 : ordCompl[2] v % 4 = 3
    · simp [h3, (omega3_ord_iff v).mpr h3]
    · simp only [h3, if_false]
      have : omega3 v % 2 ≠ 1 := fun hc => h3 ((omega3_ord_iff v).mp hc)
      omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_boole, Nat.cast_id,
      card_oddpart_three (k - 1) (by omega)]
  have h2 : 2 ≤ (k - 1) - 1 + 1 := by omega
  have hpow : 2 ^ ((k - 1) - 1) = 2 * 2 ^ ((k - 1) - 2) := by
    have h1 : (k - 1) - 1 = ((k - 1) - 2) + 1 := by omega
    rw [h1, pow_succ]; ring
  have hp1 : 1 ≤ 2 ^ ((k - 1) - 2) := Nat.one_le_two_pow
  omega

end Paper3DigitSum
