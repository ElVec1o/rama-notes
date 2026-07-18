import Mathlib
open Finset BigOperators

/-!
# The collapsible family vanishes: `Σ_{x odd < 2^k} Ω₃(x) ≡ 0 (mod 2)`

In the adaptive-peak mechanism (Paper 3 §7), the family `n = 2^k − 1` is the unique one whose
achiever set is cut out by a *single* parity condition, and its count parity collapses (hyperbola
swap) to `Σ_{x odd ≤ n} Ω₃(x) mod 2`, where `Ω₃(x) = Σ_{q ≡ 3 (4)} v_q(x)` counts prime-power
divisors with base `≡ 3 (mod 4)`. Machine-checked here:

- `omega3_mul`, `omega3_prime` — `Ω₃` is completely additive with prime values `[q ≡ 3 (4)]`;
- `odd_omega3_iff` — the **pointwise `χ₄` identity**: for odd `x`, `Ω₃(x)` is odd iff `x ≡ 3 (4)`
  (mod 4, primes `≡1` contribute `1`, primes `≡3` contribute `(−1)^{v_q}`);
- `card_three_mod_four` — `#{x < 2^k : x ≡ 3 (4)} = 2^(k−2)`;
- `sum_omega3_odd_even` — the vanishing: for `k ≥ 3`,
  `(Σ_{x < 2^k, x odd} Ω₃(x)) % 2 = 0`.

Consequently the `n = 2^k−1` achiever count is even for every `k ≥ 4`: the collapsible family
**never fires**, and `v₂(N₀(2^k−1))` always lifts strictly above the engine minimum.
-/
namespace Paper3CMinus1

/-- `Ω₃(x)`: the number of prime-power divisors of `x` whose base is `≡ 3 (mod 4)`,
i.e. `Σ_{q ≡ 3 (4)} v_q(x)`. -/
def omega3 (x : ℕ) : ℕ := x.factorization.sum fun q e => if q % 4 = 3 then e else 0

@[simp] lemma omega3_one : omega3 1 = 0 := by simp [omega3]

lemma omega3_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    omega3 (x * y) = omega3 x + omega3 y := by
  unfold omega3
  rw [Nat.factorization_mul hx hy]
  exact Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => by split <;> simp)

lemma omega3_prime {p : ℕ} (hp : p.Prime) :
    omega3 p = if p % 4 = 3 then 1 else 0 := by
  unfold omega3
  rw [hp.factorization]
  exact Finsupp.sum_single_index (by simp)

/-- **The pointwise `χ₄` identity**: for odd positive `x`, `Ω₃(x)` is odd iff `x ≡ 3 (mod 4)`. -/
theorem odd_omega3_iff : ∀ x : ℕ, 0 < x → x % 2 = 1 → (omega3 x % 2 = 1 ↔ x % 4 = 3) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hpos hodd
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)) with h1 | h1
    · -- x = 1
      simp [← h1]
    · -- x > 1: split off the least prime factor
      have hne1 : x ≠ 1 := by omega
      set p := x.minFac with hp
      have hprime : p.Prime := Nat.minFac_prime hne1
      have hdvd : p ∣ x := Nat.minFac_dvd x
      obtain ⟨y, hxy⟩ := hdvd
      have hy0 : y ≠ 0 := by rintro rfl; simp at hxy; omega
      have hp0 : p ≠ 0 := hprime.ne_zero
      -- p and y are odd
      have hpodd : p % 2 = 1 := by
        rcases hprime.eq_two_or_odd with h2 | h2
        · exfalso; rw [hxy, h2] at hodd; omega
        · exact h2
      have hyodd : y % 2 = 1 := by
        rcases Nat.even_or_odd y with he | ho
        · exfalso
          obtain ⟨t, rfl⟩ := he
          have h2 : x = 2 * (p * t) := by rw [hxy]; ring
          omega
        · exact Nat.odd_iff.mp ho
      have hylt : y < x := by
        have hp2 : 2 ≤ p := hprime.two_le
        have : 0 < y := Nat.pos_of_ne_zero hy0
        calc y < 2 * y := by omega
          _ ≤ p * y := by exact Nat.mul_le_mul_right y hp2
          _ = x := hxy.symm
      have hIH := ih y hylt (Nat.pos_of_ne_zero hy0) hyodd
      have hsplit : omega3 x = (if p % 4 = 3 then 1 else 0) + omega3 y := by
        rw [hxy, omega3_mul hp0 hy0, omega3_prime hprime]
      -- x % 4 = (p % 4) * (y % 4) % 4, with p%4, y%4 ∈ {1,3}
      have hx4 : x % 4 = p % 4 * (y % 4) % 4 := by
        rw [hxy, Nat.mul_mod]
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      have hy4 : y % 4 = 1 ∨ y % 4 = 3 := by omega
      rcases hp4 with hp4 | hp4 <;> rcases hy4 with hy4 | hy4 <;>
        · rw [hp4, hy4] at hx4
          rw [hp4] at hsplit
          simp at hsplit
          omega

/-- `#{x < 2^k : x ≡ 3 (mod 4)} = 2^(k−2)` for `k ≥ 2`. -/
lemma card_three_mod_four {k : ℕ} (hk : 2 ≤ k) :
    ((Finset.range (2 ^ k)).filter (fun x => x % 4 = 3)).card = 2 ^ (k - 2) := by
  have himg : (Finset.range (2 ^ k)).filter (fun x => x % 4 = 3)
      = (Finset.range (2 ^ (k - 2))).image (fun j => 4 * j + 3) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hlt, hmod⟩
      refine ⟨x / 4, ?_, by omega⟩
      have h4 : 2 ^ k = 4 * 2 ^ (k - 2) := by
        have h := Nat.sub_add_cancel hk
        nth_rewrite 1 [← h]
        rw [pow_add]; ring
      omega
    · rintro ⟨j, hj, rfl⟩
      have h4 : 2 ^ k = 4 * 2 ^ (k - 2) := by
        have h := Nat.sub_add_cancel hk
        nth_rewrite 1 [← h]
        rw [pow_add]; ring
      omega
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

/-- **The collapsible family vanishes**: for `k ≥ 3`,
`Σ_{x < 2^k, x odd} Ω₃(x) ≡ 0 (mod 2)`. -/
theorem sum_omega3_odd_even {k : ℕ} (hk : 3 ≤ k) :
    (∑ x ∈ (Finset.range (2 ^ k)).filter (fun x => x % 2 = 1), omega3 x) % 2 = 0 := by
  classical
  rw [Finset.sum_nat_mod]
  have hpt : ∀ x ∈ (Finset.range (2 ^ k)).filter (fun x => x % 2 = 1),
      omega3 x % 2 = (if x % 4 = 3 then 1 else 0) := by
    intro x hx
    rw [mem_filter] at hx
    have hpos : 0 < x := by omega
    have hiff := odd_omega3_iff x hpos hx.2
    by_cases h3 : x % 4 = 3
    · simp [h3, hiff.mpr h3]
    · simp only [h3, if_false]
      have : omega3 x % 2 ≠ 1 := fun hc => h3 (hiff.mp hc)
      omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_boole, Nat.cast_id]
  -- the inner filter over odds with x%4=3 equals the plain x%4=3 filter
  have hff : ((Finset.range (2 ^ k)).filter (fun x => x % 2 = 1)).filter (fun x => x % 4 = 3)
      = (Finset.range (2 ^ k)).filter (fun x => x % 4 = 3) := by
    ext x
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  rw [hff, card_three_mod_four (by omega)]
  have : 2 ^ (k - 2) = 2 * 2 ^ (k - 3) := by
    have hke : k - 2 = (k - 3) + 1 := by omega
    rw [hke, pow_succ]; ring
  omega

/-- **The zero-word lemma** (Theorem A's degenerate case): if `v` is odd and has no prime factor
`≡ 3 (mod 4)` (i.e. `Ω₃(v)=0`), then no `w` has `gcd(v,w) ≡ 3 (mod 4)`, so every gcd-χ₄ window count
vanishes---the deficit word of `v` is identically zero. This is exactly the `t₃(v)=0` case of the
word-sum invariant `Σ word_v ≡ wt(v)·t₃(v)`. -/
theorem gcd_chi4_empty_of_no_three {v : ℕ} (hv : v % 2 = 1) (hz : omega3 v = 0) (a b : ℕ) :
    (Finset.Ioc a b).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro w _ ⟨_, hgcd⟩
  have hv0 : v ≠ 0 := by omega
  have hgdvd : Nat.gcd v w ∣ v := Nat.gcd_dvd_left v w
  set g := Nat.gcd v w with hgdef
  have hgpos : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_left w (by omega)
  have hg0 : g ≠ 0 := by omega
  obtain ⟨c, hc⟩ := hgdvd
  have hc0 : c ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hc; exact hv0 hc
  have hsum : omega3 v = omega3 g + omega3 c := by
    rw [hc]; exact omega3_mul hg0 hc0
  have hgz : omega3 g = 0 := by omega
  have hgodd : g % 2 = 1 := by
    have h2 : ¬ (2 ∣ g) := by
      intro h2; have : (2 : ℕ) ∣ v := h2.trans ⟨c, hc⟩; omega
    omega
  have hodd := (odd_omega3_iff g hgpos hgodd).mpr hgcd
  omega

/-- **Converse of the zero-word lemma**: if a prime `q ≡ 3 (mod 4)` divides `v` (`v>0`), then the
period `(0, 2v]` contains a witness `w` with `gcd(v,w) ≡ 3 (mod 4)`---namely `w = q`. Together with
`gcd_chi4_empty_of_no_three` this gives the complete characterization: the deficit word of `v` is
identically zero iff `Ω₃(v)=0` (no prime factor `≡ 3 (mod 4)`). -/
theorem gcd_chi4_nonempty_of_three {v q : ℕ} (hv : 0 < v) (hq : q.Prime) (hq3 : q % 4 = 3)
    (hqv : q ∣ v) :
    ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).Nonempty := by
  refine ⟨q, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ioc]
  have hqle : q ≤ v := Nat.le_of_dvd hv hqv
  refine ⟨⟨hq.pos, by omega⟩, ?_, ?_⟩
  · rcases hq.eq_two_or_odd with h2 | ho
    · rw [h2] at hq3; omega
    · exact ho
  · rw [Nat.gcd_eq_right hqv]; exact hq3

end Paper3CMinus1
