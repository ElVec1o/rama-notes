/-
# Paper 3, Theorem 3 — `3 ∣ a(n)` for `n ≥ 13`, end-to-end in Lean

Combining Lemma A (`permanent_eq_zero_of_col_period`, in `Paper3Permanent`) with
the elementary number theory (Lemma B / the type-A count), this proves that the
permanent of the `gcd` matrix over `ZMod 3` vanishes for `n ≥ 13`. Since the
permanent commutes with the ring map `ℤ → ZMod 3`, this is exactly
`3 ∣ a(n) = perm[gcd(i,j)]` for `n ≥ 13`.

The three columns indexed by `1, 7, 13` (i.e. `Fin n` indices `0, 6, 12`) are
all `≡ (1,…,1) (mod 3)` — because every divisor of `1, 7, 13` is `≡ 1 (mod 3)` —
so the 3-cycle through them is a column period of order 3.
-/
import RamaLean.Paper3Permanent

namespace Paper3

open Matrix Equiv Equiv.Perm

/-- The gcd matrix over `ZMod 3`: entry `(i,j)` is `gcd(i+1, j+1) mod 3`
(the `+1` because `Fin n` is `0`-indexed). Its permanent is `a(n) mod 3`. -/
def gcdMat (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  fun i j => (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ZMod 3)

lemma col_gcd_one (k : ℕ) : (Nat.gcd k 1 : ZMod 3) = 1 := by
  simp [Nat.gcd_one_right]

lemma col_gcd_seven (k : ℕ) : (Nat.gcd k 7 : ZMod 3) = 1 := by
  have h7 : Nat.Prime 7 := by norm_num
  rcases h7.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right k 7) with h | h <;> rw [h] <;> decide

lemma col_gcd_thirteen (k : ℕ) : (Nat.gcd k 13 : ZMod 3) = 1 := by
  have h13 : Nat.Prime 13 := by norm_num
  rcases h13.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right k 13) with h | h <;> rw [h] <;> decide

/-- **Theorem 3 (formalized).** For `n ≥ 13`, the permanent of the `gcd` matrix
over `ZMod 3` is `0`; i.e. `3 ∣ a(n)`. -/
theorem three_dvd_gcd_permanent (n : ℕ) (hn : 13 ≤ n) :
    (gcdMat n).permanent = 0 := by
  classical
  -- the three special columns, integers 1, 7, 13 → indices 0, 6, 12
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨6, by omega⟩
  let c : Fin n := ⟨12, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  -- the 3-cycle σ = (a c b), fixing all other columns
  let σ : Perm (Fin n) := swap a b * swap a c
  have hσ3 : orderOf σ = 3 := (isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf
  -- σ on the three columns
  have hσa : σ a = c := by simp [σ, swap_apply_left, swap_apply_of_ne_of_ne, hac.symm, hbc.symm]
  have hσb : σ b = a := by
    simp [σ, Perm.mul_apply, swap_apply_of_ne_of_ne, hab.symm, hbc, swap_apply_left]
  have hσc : σ c = b := by
    simp [σ, Perm.mul_apply, swap_apply_right, swap_apply_left]
  -- each special column is the all-ones vector mod 3
  have ga : ∀ i, gcdMat n i a = 1 := fun i => by simp [gcdMat, a, col_gcd_one]
  have gb : ∀ i, gcdMat n i b = 1 := fun i => by
    simp only [gcdMat, b]; exact col_gcd_seven _
  have gc : ∀ i, gcdMat n i c = 1 := fun i => by
    simp only [gcdMat, c]; exact col_gcd_thirteen _
  -- σ is a column period, so Lemma A applies
  refine permanent_eq_zero_of_col_period (gcdMat n) σ hσ3 (fun i j => ?_)
  rcases eq_or_ne j a with rfl | hja
  · rw [hσa, gc, ga]
  · rcases eq_or_ne j b with rfl | hjb
    · rw [hσb, ga, gb]
    · rcases eq_or_ne j c with rfl | hjc
      · rw [hσc, gb, gc]
      · -- j ∉ {a,b,c}: σ fixes j
        have : σ j = j := by
          simp [σ, Perm.mul_apply, swap_apply_of_ne_of_ne, hja, hjb, hjc]
        rw [this]

end Paper3
