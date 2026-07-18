import Mathlib
import RamaLean.OddPermanentBound
import RamaLean.Paper3LinearRate
import RamaLean.Paper3Atom1
open Matrix Equiv Finset BigOperators

/-!
# The odd-permanent engine (power-of-2 size): `2^(2^a − a) ∣ per(2e+1)`

For an all-odd `n×n` matrix with `n = 2^a`, the multilinear expansion
`per(2e+1) = Σ_t 2^{|t|} per(M_t)` (`OddPerm.permanent_two_mul_add_one`) has every term divisible by
`2^(2^a − a)`: term `t` carries `2^{|t|}` and `(n−|t|)!`, and
`v₂(2^{|t|} · (n−|t|)!) = n − s₂(n − |t|) ≥ 2^a − a` since every `m ≤ 2^a` has `s₂(m) ≤ a`.

This is `two_pow_dvd_permanent_odd_pow2`, the **lower** half. The **upper** half is now also proven:
`engine_upper` shows that for `n = 2^a` (`a ≥ 2`) with `π₁` odd, `¬ 2^(2^a−a+1) ∣ per(2e+1)`. Together
they give the exact valuation **`v₂(per(2e+1)) = 2^a − a`** — the `k=1` term of the expansion is the
unique minimum-valuation term (no cancellation), driven by `π₁` odd.

The upper-half proof splits the column-subset expansion by `|t|`: the `|t|=0` term is `per J = n!` and
the `|t|≥2` terms vanish mod `2^(2^a−a+1)` (via the binary-complement digit identity `s2_compl`), while
the `|t|=1` terms sum to `2·(n−1)!·π₁` (via the fiber count `card_fiber_eq` and the `k=1` evaluation
`permanent_ones_except_col`); `π₁` odd then makes `v₂` land at exactly `2^a − a < 2^a−a+1`.

Contents: `permanent_all_ones` (`per J = n!`); the `Fiber` section
(`card_stabilizer_eq`, `card_fiber_eq`, `sum_perm_apply`, `permanent_ones_except_col`); the digit
lemmas (`s2_two_pow`, `s2_two_pow_sub_one`, `s2_compl`, `digitsum_pos`, `digitsum_le_of_le_two_pow`);
and the two engine halves (`two_pow_dvd_permanent_odd_pow2`, `engine_upper`).
-/
namespace OddEngine

/-- The permanent of the all-ones matrix is `n!`. -/
lemma permanent_all_ones {n : ℕ} :
    (Matrix.of (fun (_ _ : Fin n) => (1 : ℤ))).permanent = (n.factorial : ℤ) := by
  simp only [Matrix.permanent, Matrix.of_apply, Finset.prod_const_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp

section Fiber
open MulAction Function

lemma card_stabilizer_eq {n : ℕ} (j : Fin (n + 1)) :
    Fintype.card (stabilizer (Perm (Fin (n + 1))) j) = n.factorial := by
  haveI : IsPretransitive (Perm (Fin (n + 1))) (Fin (n + 1)) :=
    ⟨fun a b => ⟨Equiv.swap a b, Equiv.swap_apply_left a b⟩⟩
  have huniv : orbit (Perm (Fin (n + 1))) j = Set.univ :=
    orbit_eq_univ (M := Perm (Fin (n + 1))) j
  haveI : Fintype (orbit (Perm (Fin (n + 1))) j) := by rw [huniv]; infer_instance
  have hc : Fintype.card (orbit (Perm (Fin (n + 1))) j) = n + 1 := by
    rw [Fintype.card_congr (Equiv.setCongr huniv), Fintype.card_congr (Equiv.Set.univ _),
        Fintype.card_fin]
  have h := card_orbit_mul_card_stabilizer_eq_card_group (α := Perm (Fin (n + 1))) j
  rw [hc, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h

lemma card_fiber_eq {n : ℕ} (j r : Fin (n + 1)) :
    (Finset.univ.filter (fun σ : Perm (Fin (n + 1)) => σ j = r)).card = n.factorial := by
  rw [← Fintype.card_subtype, ← card_stabilizer_eq j]
  refine Fintype.card_congr (Equiv.mk (fun x => ⟨Equiv.swap r j * x.1, ?_⟩)
    (fun x => ⟨Equiv.swap r j * x.1, ?_⟩) ?_ ?_)
  · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, x.2]
    exact Equiv.swap_apply_left r j
  · show (Equiv.swap r j * x.1) j = r
    rw [Equiv.Perm.mul_apply]
    have hx : x.1 j = j := by
      have h := MulAction.mem_stabilizer_iff.mp x.2; rwa [Equiv.Perm.smul_def] at h
    rw [hx]; exact Equiv.swap_apply_right r j
  · intro x; apply Subtype.ext
    show Equiv.swap r j * (Equiv.swap r j * x.1) = x.1
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · intro x; apply Subtype.ext
    show Equiv.swap r j * (Equiv.swap r j * x.1) = x.1
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

lemma sum_perm_apply {n : ℕ} (c : Fin (n + 1) → ℤ) (j : Fin (n + 1)) :
    ∑ σ : Perm (Fin (n + 1)), c (σ j) = (n.factorial : ℤ) * ∑ r, c r := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Perm (Fin (n+1)) => σ j)
        (t := Finset.univ) (fun σ _ => Finset.mem_univ _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hce : ∀ σ ∈ Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ j = r), c (σ j) = c r :=
    fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]
  rw [Finset.sum_congr rfl hce, Finset.sum_const, card_fiber_eq, nsmul_eq_mul]

/-- Permanent of the matrix that is all-ones except column `j` equals `(column j sum)·(n-1)!`.
This is the `k=1` term of the odd-permanent engine's expansion. -/
lemma permanent_ones_except_col {n : ℕ} (c : Fin (n + 1) → ℤ) (j : Fin (n + 1)) :
    (Matrix.of (fun k i => if i = j then c k else 1)).permanent
      = (n.factorial : ℤ) * ∑ r, c r := by
  rw [← sum_perm_apply c j]
  simp only [Matrix.permanent, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_ite_eq' Finset.univ j (fun x => c (σ x))]
  simp

end Fiber

/-- `s₂(2^a) = 1`. -/
lemma s2_two_pow (a : ℕ) : (Nat.digits 2 (2 ^ a)).sum = 1 := by
  induction a with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ (k + 1) := by positivity
    rw [Nat.digits_def' (b := 2) (by norm_num) hpos]
    have hmod : 2 ^ (k + 1) % 2 = 0 := by
      rw [pow_succ]; omega
    have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
      rw [pow_succ]; omega
    rw [hmod, hdiv]
    simpa using ih

/-- Binary digit sum bound: `m ≤ 2^a ⟹ s₂(m) ≤ a`. -/
lemma digitsum_le_of_le_two_pow {a m : ℕ} (ha : 1 ≤ a) (hm : m ≤ 2 ^ a) :
    (Nat.digits 2 m).sum ≤ a := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  · rcases eq_or_lt_of_le hm with h | h
    · rw [h, s2_two_pow]; exact ha
    · -- 0 < m < 2^a ⟹ log₂ m < a, and s₂(m) ≤ log₂ m + 1 ≤ a
      have hlog : Nat.log 2 m < a := by
        rcases Nat.lt_or_ge (Nat.log 2 m) a with h' | h'
        · exact h'
        · exfalso
          have hp : 2 ^ a ≤ 2 ^ (Nat.log 2 m) := Nat.pow_le_pow_right (by norm_num) h'
          have hs : 2 ^ (Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 (by omega)
          omega
      have hds := Paper3Linear.digitsum_le_log_succ m (by omega)
      omega

/-- **`A`-engine lower half.** For `n = 2^a`, every all-odd `n×n` matrix has
`2^(2^a − a) ∣ per(2e+1)`. -/
theorem two_pow_dvd_permanent_odd_pow2 {a : ℕ} (ha : 1 ≤ a)
    (e : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℤ) :
    (2 : ℤ) ^ (2 ^ a - a) ∣ (Matrix.of (fun k i => 2 * e k i + 1)).permanent := by
  classical
  rw [OddPerm.permanent_two_mul_add_one]
  apply Finset.dvd_sum
  intro t _
  have h1 : (2 : ℤ) ^ (t.card + (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum))
      ∣ 2 ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
    rw [pow_add]
    refine mul_dvd_mul_left _ ?_
    have hf : (2 : ℤ) ^ (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum)
        ∣ ((2 ^ a - t.card).factorial : ℤ) := by
      exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial (2 ^ a - t.card)
    exact hf.trans (OddPerm.factorial_dvd_permanent_off (2 ^ a) e t)
  -- 2^a − a ≤ |t| + (2^a − |t|) − s₂(2^a − |t|) = 2^a − s₂(2^a − |t|)
  have htc : t.card ≤ 2 ^ a := (Finset.card_le_univ t).trans_eq (by simp)
  have hs : (Nat.digits 2 (2 ^ a - t.card)).sum ≤ a :=
    digitsum_le_of_le_two_pow ha (Nat.sub_le _ _)
  have hds : (Nat.digits 2 (2 ^ a - t.card)).sum ≤ 2 ^ a - t.card := Nat.digit_sum_le 2 _
  have hexp : 2 ^ a - a
      ≤ t.card + (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum) := by omega
  exact dvd_trans (pow_dvd_pow 2 hexp) h1

/-- `s₂(2^a − 1) = a`. -/
lemma s2_two_pow_sub_one (a : ℕ) : (Nat.digits 2 (2 ^ a - 1)).sum = a := by
  induction a with
  | zero => simp only [pow_zero, Nat.sub_self, Nat.digits_zero, List.sum_nil]
  | succ k ih =>
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h1 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [pow_succ]; omega
    rw [h1, Nat.digits_def' (b := 2) (by norm_num) (by omega)]
    have hmod : (2 * (2 ^ k - 1) + 1) % 2 = 1 := by omega
    have hdiv : (2 * (2 ^ k - 1) + 1) / 2 = 2 ^ k - 1 := by omega
    rw [hmod, hdiv, List.sum_cons, ih]
    omega

/-- Positive numbers have positive binary digit sum. -/
lemma digitsum_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ (Nat.digits 2 n).sum := by
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits 2 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hn
  have hmem : (Nat.digits 2 n).getLast hne ∈ Nat.digits 2 n := List.getLast_mem hne
  have hle : (Nat.digits 2 n).getLast hne ≤ (Nat.digits 2 n).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  omega

/-- Binary complement identity: `s₂(x) + s₂(2^a − 1 − x) = a` for `x ≤ 2^a − 1`. -/
lemma s2_compl (a : ℕ) : ∀ m, m ≤ 2 ^ a - 1 →
    (Nat.digits 2 m).sum + (Nat.digits 2 (2 ^ a - 1 - m)).sum = a := by
  induction a with
  | zero =>
    intro m hm
    simp only [pow_zero, Nat.sub_self, Nat.le_zero] at hm
    subst hm; simp
  | succ k ih =>
    intro m hm
    have hkp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hps : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.digits_zero, List.sum_nil, Nat.zero_add, Nat.sub_zero]
      exact s2_two_pow_sub_one (k + 1)
    rcases eq_or_lt_of_le hm with hmtop | hmlt
    · rw [hmtop]
      simp only [Nat.sub_self, Nat.digits_zero, List.sum_nil, Nat.add_zero]
      exact s2_two_pow_sub_one (k + 1)
    · have hdm := Nat.div_add_mod m 2
      have hr1 : m % 2 < 2 := Nat.mod_lt m (by norm_num)
      have hq : m / 2 ≤ 2 ^ k - 1 := by omega
      have hcpos : 0 < 2 ^ (k + 1) - 1 - m := by omega
      have hmod : (2 ^ (k + 1) - 1 - m) % 2 = 1 - m % 2 := by omega
      have hdiv : (2 ^ (k + 1) - 1 - m) / 2 = 2 ^ k - 1 - m / 2 := by omega
      rw [Nat.digits_def' (b := 2) (by norm_num) hmpos,
          Nat.digits_def' (b := 2) (by norm_num) hcpos, List.sum_cons, List.sum_cons,
          hmod, hdiv]
      have hihq := ih (m / 2) hq
      omega

theorem engine_upper {m a : ℕ} (ha : 2 ≤ a) (hm : m + 1 = 2 ^ a)
    (e : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hπ : Odd (∑ k, ∑ i, e k i)) :
    ¬ (2 : ℤ) ^ (2 ^ a - a + 1) ∣ (Matrix.of (fun k i => 2 * e k i + 1)).permanent := by
  classical
  intro hdvd
  rw [OddPerm.permanent_two_mul_add_one,
      ← Finset.sum_filter_add_sum_filter_not univ (fun t : Finset (Fin (m+1)) => t.card = 1)] at hdvd
  have hk1dvd : (2:ℤ) ^ (2 ^ a - a + 1) ∣
      ∑ t ∈ univ.filter (fun t : Finset (Fin (m+1)) => t.card = 1),
        (2:ℤ) ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
    have hrest : (2:ℤ) ^ (2 ^ a - a + 1) ∣
        ∑ t ∈ univ.filter (fun t : Finset (Fin (m+1)) => ¬ t.card = 1),
          (2:ℤ) ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
      apply Finset.dvd_sum
      intro t ht
      rw [mem_filter] at ht
      have htc : t.card ≤ 2 ^ a := by
        have h := Finset.card_le_univ t
        rw [Fintype.card_fin] at h; omega
      have hsub : (m + 1) - t.card = 2 ^ a - t.card := by omega
      have hfac : (2:ℤ) ^ (t.card + (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum))
          ∣ (2:ℤ) ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
        rw [pow_add]
        refine mul_dvd_mul_left _ ?_
        have hf : (2:ℤ) ^ (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum)
            ∣ ((2 ^ a - t.card).factorial : ℤ) := by
          exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial (2 ^ a - t.card)
        have hfp := OddPerm.factorial_dvd_permanent_off (m + 1) e t
        rw [hsub] at hfp
        exact hf.trans hfp
      refine dvd_trans (pow_dvd_pow 2 ?_) hfac
      have hs2 : (Nat.digits 2 (2 ^ a - t.card)).sum ≤ a - 1 := by
        rcases Nat.eq_zero_or_pos t.card with h0 | hpos
        · rw [h0, Nat.sub_zero, s2_two_pow]; omega
        · have hc2 : 2 ≤ t.card := by have := ht.2; omega
          have hco := s2_compl a (2 ^ a - t.card) (by omega)
          have heq : 2 ^ a - 1 - (2 ^ a - t.card) = t.card - 1 := by omega
          rw [heq] at hco
          have hp1 : 1 ≤ (Nat.digits 2 (t.card - 1)).sum := digitsum_pos (by omega)
          omega
      have hds : (Nat.digits 2 (2 ^ a - t.card)).sum ≤ 2 ^ a - t.card := Nat.digit_sum_le 2 _
      have haP : a ≤ 2 ^ a := Nat.le_of_lt Nat.lt_two_pow_self
      omega
    have := dvd_sub hdvd hrest
    simpa using this
  have hk1val : ∑ t ∈ univ.filter (fun t : Finset (Fin (m+1)) => t.card = 1),
        (2:ℤ) ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent
      = 2 * (m.factorial : ℤ) * (∑ k, ∑ i, e k i) := by
    have hset : (univ.filter (fun t : Finset (Fin (m+1)) => t.card = 1))
        = univ.image (fun j : Fin (m+1) => ({j} : Finset (Fin (m+1)))) := by
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_image, Finset.card_eq_one]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩
    rw [hset, Finset.sum_image (fun x _ y _ h => Finset.singleton_injective h)]
    have hper : ∀ j : Fin (m+1),
        (2:ℤ)^(({j}:Finset (Fin (m+1))).card) *
          (Matrix.of (fun k i => if i ∈ ({j}:Finset (Fin (m+1))) then e k i else 1)).permanent
        = 2 * ((m.factorial : ℤ) * ∑ r, e r j) := by
      intro j
      rw [Finset.card_singleton, pow_one]
      congr 1
      have hmateq : Matrix.of (fun (k i : Fin (m+1)) =>
            if i ∈ ({j}:Finset (Fin (m+1))) then e k i else 1)
          = Matrix.of (fun k i => if i = j then e k j else 1) := by
        ext k i; simp only [Matrix.of_apply, Finset.mem_singleton]
        by_cases h : i = j
        · subst h; simp
        · simp [h]
      rw [hmateq]
      exact permanent_ones_except_col (fun k => e k j) j
    rw [Finset.sum_congr rfl (fun j _ => hper j)]
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hk1val] at hk1dvd
  -- contradiction via natAbs + factorization
  have hne : (∑ k, ∑ i, e k i) ≠ 0 := by
    rintro h0; rw [h0, Int.odd_iff] at hπ; omega
  have hne_pi : (∑ k, ∑ i, e k i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
  have hπabs : ¬ (2 ∣ (∑ k, ∑ i, e k i).natAbs) := by
    have hodd := hπ; rw [← Int.natAbs_odd, Nat.odd_iff] at hodd; omega
  have hnat : (2 ^ (2 ^ a - a + 1) : ℕ) ∣ 2 * m.factorial * (∑ k, ∑ i, e k i).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hk1dvd
    rw [show ((2:ℤ) ^ (2 ^ a - a + 1)).natAbs = 2 ^ (2 ^ a - a + 1) by
          rw [Int.natAbs_pow]; rfl,
        show (2 * (m.factorial : ℤ) * (∑ k, ∑ i, e k i)).natAbs
           = 2 * m.factorial * (∑ k, ∑ i, e k i).natAbs by
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]; rfl] at h
    exact h
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (Nat.factorial_ne_zero m)) hne_pi)] at hnat
  rw [Nat.factorization_mul (Nat.mul_ne_zero two_ne_zero (Nat.factorial_ne_zero m)) hne_pi,
      Nat.factorization_mul two_ne_zero (Nat.factorial_ne_zero m)] at hnat
  simp only [Finsupp.coe_add, Pi.add_apply] at hnat
  have hf2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have hffac : (m.factorial).factorization 2 = 2 ^ a - 1 - a := by
    rw [Paper3Atom1.v2_factorial]
    have hmeq : m = 2 ^ a - 1 := by omega
    rw [hmeq, s2_two_pow_sub_one]
  have hfodd : ((∑ k, ∑ i, e k i).natAbs).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hπabs
  rw [hf2, hffac, hfodd] at hnat
  have hplt : a < 2 ^ a := Nat.lt_two_pow_self
  omega


/-- **The odd engine, exact.** For `n = 2^a` (`a ≥ 2`) and `π₁ = ∑ e` odd,
`v₂(per(2e+1)) = 2^a − a`: stated as the two matching divisibilities. -/
theorem engine_exact {m a : ℕ} (ha : 2 ≤ a) (hm : m + 1 = 2 ^ a)
    (e : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hπ : Odd (∑ k, ∑ i, e k i)) :
    (2 : ℤ) ^ (2 ^ a - a) ∣ (Matrix.of (fun k i => 2 * e k i + 1)).permanent
    ∧ ¬ (2 : ℤ) ^ (2 ^ a - a + 1) ∣ (Matrix.of (fun k i => 2 * e k i + 1)).permanent := by
  classical
  refine ⟨?_, engine_upper ha hm e hπ⟩
  -- lower bound `2^(2^a − a) ∣ per`, over `Fin (m+1)` with `m+1 = 2^a`
  rw [OddPerm.permanent_two_mul_add_one]
  apply Finset.dvd_sum
  intro t _
  have htc : t.card ≤ 2 ^ a := by
    have h := Finset.card_le_univ t; rw [Fintype.card_fin] at h; omega
  have hsub : (m + 1) - t.card = 2 ^ a - t.card := by omega
  have h1 : (2 : ℤ) ^ (t.card + (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum))
      ∣ 2 ^ t.card * (Matrix.of (fun k i => if i ∈ t then e k i else 1)).permanent := by
    rw [pow_add]
    refine mul_dvd_mul_left _ ?_
    have hf : (2 : ℤ) ^ (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum)
        ∣ ((2 ^ a - t.card).factorial : ℤ) := by
      exact_mod_cast Paper3Linear.two_pow_sub_digitsum_dvd_factorial (2 ^ a - t.card)
    have hfp := OddPerm.factorial_dvd_permanent_off (m + 1) e t
    rw [hsub] at hfp
    exact hf.trans hfp
  have hs : (Nat.digits 2 (2 ^ a - t.card)).sum ≤ a :=
    digitsum_le_of_le_two_pow (by omega) (Nat.sub_le _ _)
  have hds : (Nat.digits 2 (2 ^ a - t.card)).sum ≤ 2 ^ a - t.card := Nat.digit_sum_le 2 _
  have hexp : 2 ^ a - a ≤ t.card + (2 ^ a - t.card - (Nat.digits 2 (2 ^ a - t.card)).sum) := by omega
  exact dvd_trans (pow_dvd_pow 2 hexp) h1

end OddEngine
