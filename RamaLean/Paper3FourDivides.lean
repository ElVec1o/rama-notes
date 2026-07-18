import Mathlib
open Matrix Equiv Finset
namespace Paper3Four
variable {n : ℕ}

/-- The permanent−determinant identity over `ℤ`: `perm M − det M = 2·(oddsum)`,
where the oddsum is over sign `= −1` permutations. -/
lemma permanent_sub_det (M : Matrix (Fin n) (Fin n) ℤ) :
    M.permanent - M.det =
      2 * ∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => Perm.sign σ = -1),
            ∏ i, M (σ i) i := by
  have hdet : M.det = ∑ σ : Perm (Fin n), (Perm.sign σ : ℤ) * ∏ i, M (σ i) i := by
    rw [Matrix.det_apply]; simp [Units.smul_def]
  rw [Matrix.permanent, hdet, ← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · simp [h]
  · rw [h]; simp; ring

/-- Smith's key arithmetic identity, in `Fin n` form:
`∑_{e+1 ∣ i+1 and e+1 ∣ j+1} φ(e+1) = gcd(i+1, j+1)`. -/
lemma entry_sum (i j : Fin n) :
    ∑ e : Fin n, (if ((e:ℕ)+1) ∣ ((i:ℕ)+1) ∧ ((e:ℕ)+1) ∣ ((j:ℕ)+1)
        then (Nat.totient ((e:ℕ)+1) : ℤ) else 0)
      = (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) : ℤ) := by
  set g := Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) with hg
  have hgpos : 0 < g := Nat.gcd_pos_iff.mpr (Or.inl (Nat.succ_pos _))
  have hgn : g ≤ n := by
    have h1 : g ≤ (i:ℕ)+1 := Nat.gcd_le_left ((j:ℕ)+1) (Nat.succ_pos _)
    have h2 := i.isLt; omega
  have hcond : ∀ e : Fin n,
      (((e:ℕ)+1) ∣ ((i:ℕ)+1) ∧ ((e:ℕ)+1) ∣ ((j:ℕ)+1)) ↔ ((e:ℕ)+1) ∣ g := by
    intro e; rw [hg, Nat.dvd_gcd_iff]
  simp_rw [hcond]
  rw [← Finset.sum_filter]
  have hsum : (g : ℤ) = ∑ d ∈ g.divisors, (Nat.totient d : ℤ) := by
    rw [← Nat.cast_sum, Nat.sum_totient]
  rw [hsum]
  refine Finset.sum_bij' (fun (e : Fin n) _ => (e:ℕ)+1)
      (fun (d : ℕ) (hd : d ∈ g.divisors) => (⟨d-1, by
        have hdle : d ≤ g := Nat.le_of_dvd hgpos (Nat.dvd_of_mem_divisors hd)
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        omega⟩ : Fin n))
      ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter] at he
    exact Nat.mem_divisors.mpr ⟨he.2, hgpos.ne'⟩
  · intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdvd : d ∣ g := Nat.dvd_of_mem_divisors hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have he : (d - 1) + 1 = d := by omega
    rw [he]; exact hdvd
  · intro e he
    apply Fin.ext; simp
  · intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    simp only; omega
  · intro e he; rfl

/-- The divisibility matrix `L`: `L i d = 1` iff `(d+1) ∣ (i+1)`. Lower-triangular,
unit diagonal. -/
def Lmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i d => if ((d:ℕ)+1) ∣ ((i:ℕ)+1) then 1 else 0

/-- The diagonal totient matrix `D d d = φ(d+1)`. -/
def Dmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal (fun d => (Nat.totient ((d:ℕ)+1) : ℤ))

/-- The gcd matrix `M i j = gcd(i+1, j+1)` over `ℤ`. `a(n) = permanent`. -/
def gcdMat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) : ℤ)

/-- **Smith factorization**: `M = L D Lᵀ`. -/
lemma gcd_factor (n : ℕ) : gcdMat n = Lmat n * Dmat n * (Lmat n)ᵀ := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Dmat, Matrix.diagonal_mul, Matrix.transpose_apply, Lmat, gcdMat]
  rw [← entry_sum i j]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h1 : ((e:ℕ)+1) ∣ ((i:ℕ)+1) <;> by_cases h2 : ((e:ℕ)+1) ∣ ((j:ℕ)+1) <;>
    simp [h1, h2]

/-- `L` is lower-triangular with unit diagonal, so `det L = 1`. -/
lemma Lmat_det (n : ℕ) : (Lmat n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _; simp [Lmat]
  · intro i j hij
    simp only [Lmat]
    rw [if_neg]
    intro hdvd
    have := Nat.le_of_dvd (Nat.succ_pos _) hdvd
    have : (i:ℕ) < (j:ℕ) := hij
    omega

/-- **Smith's determinant**: `det(gcd matrix) = ∏_{k=1}^n φ(k)`. -/
lemma gcd_det (n : ℕ) : (gcdMat n).det = ∏ k : Fin n, (Nat.totient ((k:ℕ)+1) : ℤ) := by
  rw [gcd_factor, Matrix.det_mul, Matrix.det_mul, Lmat_det, Matrix.det_transpose, Lmat_det,
    Dmat, Matrix.det_diagonal]
  simp

/-- `4 ∣ det(gcd matrix)` for `n ≥ 4`, since `φ(3)·φ(4) = 2·2 = 4` divides the product. -/
lemma four_dvd_gcd_det (n : ℕ) (hn : 4 ≤ n) : (4:ℤ) ∣ (gcdMat n).det := by
  rw [gcd_det]
  have h2mem : (⟨2, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have h3mem : (⟨3, by omega⟩ : Fin n) ∈ (Finset.univ.erase (⟨2, by omega⟩ : Fin n)) := by
    rw [Finset.mem_erase]
    exact ⟨by simp [Fin.ext_iff], Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h2mem, ← Finset.mul_prod_erase _ _ h3mem]
  have e2 : (Nat.totient (((⟨2, by omega⟩ : Fin n) : ℕ) + 1) : ℤ) = 2 := by
    show (Nat.totient (2 + 1) : ℤ) = 2; decide
  have e3 : (Nat.totient (((⟨3, by omega⟩ : Fin n) : ℕ) + 1) : ℤ) = 2 := by
    show (Nat.totient (3 + 1) : ℤ) = 2; decide
  rw [e2, e3]
  exact ⟨_, by ring⟩

/-- `gcd m k` is even iff both `m, k` are, so `gcd m k mod 2` depends only on `m mod 2`. -/
lemma gcd_mod2 (m k : ℕ) : (Nat.gcd m k) % 2 = if 2 ∣ m ∧ 2 ∣ k then 0 else 1 := by
  have hiff : 2 ∣ Nat.gcd m k ↔ 2 ∣ m ∧ 2 ∣ k := Nat.dvd_gcd_iff
  by_cases h : 2 ∣ m ∧ 2 ∣ k
  · rw [if_pos h]; have := hiff.mpr h; omega
  · rw [if_neg h]; have := fun hh => h (hiff.mp hh); omega

/-- The mod-2 value of `gcd` in the first argument depends only on its parity. -/
lemma gcd_zmod2_eq (m m' k : ℕ) (h : m % 2 = m' % 2) :
    (Nat.gcd m k : ZMod 2) = (Nat.gcd m' k : ZMod 2) := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, gcd_mod2, gcd_mod2]
  have : (2 ∣ m) ↔ (2 ∣ m') := by rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h]
  simp only [this]

/-- The oddsum `S = ∑_{sign σ = −1} ∏ gcd` is **even** for `n ≥ 4`: the even double
transposition `τ = (0 2)(1 3)` is a fixed-point-free involution on the sign‑`(−1)`
permutations that fixes `∏ gcd mod 2` (it swaps values of equal parity), so mod 2 the
sum pairs up to `0`. -/
lemma oddsum_even (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℤ) ∣ ∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => Perm.sign σ = -1),
              ∏ i, gcdMat n (σ i) i := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  have hn2 : 2 < n := by omega
  have hn3 : 3 < n := by omega
  set p0 : Fin n := ⟨0, hn0⟩ with hp0
  set p1 : Fin n := ⟨1, hn1⟩ with hp1
  set p2 : Fin n := ⟨2, hn2⟩ with hp2
  set p3 : Fin n := ⟨3, hn3⟩ with hp3
  set τ : Perm (Fin n) := Equiv.swap p0 p2 * Equiv.swap p1 p3 with hτ
  have v0 : (p0 : ℕ) = 0 := rfl
  have v1 : (p1 : ℕ) = 1 := rfl
  have v2 : (p2 : ℕ) = 2 := rfl
  have v3 : (p3 : ℕ) = 3 := rfl
  have d02 : p0 ≠ p2 := by rw [Ne, Fin.ext_iff, v0, v2]; omega
  have d13 : p1 ≠ p3 := by rw [Ne, Fin.ext_iff, v1, v3]; omega
  have hsign : Perm.sign τ = 1 := by
    rw [hτ, map_mul, Perm.sign_swap d02, Perm.sign_swap d13]; decide
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap p0 p2) (Equiv.swap p1 p3) := by
    intro x
    by_cases h0 : x = p0
    · right; rw [h0]; apply Equiv.swap_apply_of_ne_of_ne
      · rw [Ne, Fin.ext_iff, v0, v1]; omega
      · rw [Ne, Fin.ext_iff, v0, v3]; omega
    by_cases h2 : x = p2
    · right; rw [h2]; apply Equiv.swap_apply_of_ne_of_ne
      · rw [Ne, Fin.ext_iff, v2, v1]; omega
      · rw [Ne, Fin.ext_iff, v2, v3]; omega
    · left; exact Equiv.swap_apply_of_ne_of_ne h0 h2
  have hcomm : Commute (Equiv.swap p0 p2) (Equiv.swap p1 p3) := hdisj.commute
  have hinv : τ * τ = 1 := by
    rw [hτ]
    calc Equiv.swap p0 p2 * Equiv.swap p1 p3 * (Equiv.swap p0 p2 * Equiv.swap p1 p3)
        = Equiv.swap p0 p2 * (Equiv.swap p1 p3 * Equiv.swap p0 p2) * Equiv.swap p1 p3 := by group
      _ = Equiv.swap p0 p2 * (Equiv.swap p0 p2 * Equiv.swap p1 p3) * Equiv.swap p1 p3 := by
            rw [hcomm.eq]
      _ = (Equiv.swap p0 p2 * Equiv.swap p0 p2) * (Equiv.swap p1 p3 * Equiv.swap p1 p3) := by group
      _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  have hpar : ∀ a : Fin n, ((τ a : Fin n) : ℕ) % 2 = (a : ℕ) % 2 := by
    intro a
    simp only [hτ, Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]
  have hτne : τ ≠ 1 := by
    intro h
    have e1 : τ p0 = p2 := by
      rw [hτ, Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (show p0 ≠ p1 by rw [Ne, Fin.ext_iff, v0, v1]; omega)
          (show p0 ≠ p3 by rw [Ne, Fin.ext_iff, v0, v3]; omega),
        Equiv.swap_apply_left]
    rw [h, Perm.one_apply] at e1
    rw [Fin.ext_iff, v0, v2] at e1; omega
  rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
  apply Finset.sum_involution (fun σ _ => τ * σ)
  · intro σ _
    have hprod : ((∏ i, gcdMat n ((τ * σ) i) i : ℤ) : ZMod 2)
        = ((∏ i, gcdMat n (σ i) i : ℤ) : ZMod 2) := by
      rw [Int.cast_prod, Int.cast_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp only [Perm.mul_apply, gcdMat, Int.cast_natCast]
      exact gcd_zmod2_eq _ _ _ (by have := hpar (σ i); omega)
    rw [hprod]; exact CharTwo.add_self_eq_zero _
  · intro σ _ _ heq
    exact hτne (mul_right_cancel (by rw [one_mul]; exact heq))
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [map_mul, hsign, hσ, one_mul]
  · intro σ _
    rw [← mul_assoc, hinv, one_mul]

/-- **Theorem (`4 ∣ a(n)` for `n ≥ 4`).** The permanent of the gcd matrix
`a(n) = per[gcd(i,j)]` is divisible by `4` for all `n ≥ 4`. Sharpens `2 ∣ a(n)`
(`n ≥ 3`). Proof: `per = det + 2·S` (permanent−determinant identity); Smith's
`det = ∏_{k≤n} φ(k)` is divisible by `4` (from `φ(3)φ(4) = 4`); and the oddsum `S`
is even (a fixed-point-free involution by an even double transposition). -/
theorem four_dvd_permanent (n : ℕ) (hn : 4 ≤ n) : (4 : ℤ) ∣ (gcdMat n).permanent := by
  have hid := permanent_sub_det (gcdMat n)
  have hp : (gcdMat n).permanent = (gcdMat n).det
      + 2 * ∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => Perm.sign σ = -1),
              ∏ i, gcdMat n (σ i) i := by linarith [hid]
  rw [hp]
  refine dvd_add (four_dvd_gcd_det n hn) ?_
  obtain ⟨k, hk⟩ := oddsum_even n hn
  rw [hk]; exact ⟨k, by ring⟩

end Paper3Four

