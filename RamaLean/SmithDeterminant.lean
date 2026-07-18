import Mathlib
/-!
# Smith's determinant of GCD-type matrices

For any `f : ℕ → R` over a commutative ring, the matrix with `(i,j)` entry
`∑_{d ∣ gcd(i+1,j+1)} f d` has determinant `∏_{k=1}^n f k` (`det_gcdDivSum`).
Specialising `f = φ` (Euler totient), since `∑_{d ∣ m} φ d = m`, recovers the
classical theorem of H. J. S. Smith (1875): `det[gcd(i,j)]_{1≤i,j≤n} = ∏_{k≤n} φ(k)`
(`det_gcd_eq_prod_totient`).

The proof is the Smith/`LDLᵀ` factorization: `M = L · diag(f) · Lᵀ` where `L` is the
lower-triangular divisibility matrix (`det L = 1`).
-/
open Matrix Finset
namespace Smith
variable {R : Type*} [CommRing R]

/-- Reindex a `Fin n`-sum restricted to divisors of `m` (with `0 < m ≤ n`) as a sum over
`m.divisors`. -/
lemma sum_fin_dvd_eq (f : ℕ → R) {n m : ℕ} (hm : m ≤ n) (hm0 : 0 < m) :
    ∑ e : Fin n, (if (e:ℕ)+1 ∣ m then f ((e:ℕ)+1) else 0) = ∑ d ∈ m.divisors, f d := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun (e : Fin n) _ => (e:ℕ)+1)
    (fun d hd => (⟨d-1, by
      have := Nat.le_of_dvd hm0 (Nat.dvd_of_mem_divisors hd)
      have := Nat.pos_of_mem_divisors hd; omega⟩ : Fin n)) ?_ ?_ ?_ ?_ ?_
  · intro e he; simp only [mem_filter] at he; exact Nat.mem_divisors.mpr ⟨he.2, hm0.ne'⟩
  · intro d hd
    have h1 := Nat.pos_of_mem_divisors hd
    simp only [mem_filter, mem_univ, true_and]
    have he : d - 1 + 1 = d := by omega
    rw [he]; exact Nat.dvd_of_mem_divisors hd
  · intro e _; apply Fin.ext; simp
  · intro d hd; have := Nat.pos_of_mem_divisors hd; simp only; omega
  · intro e _; rfl

/-- The lower-triangular divisibility matrix: `L i d = 1` iff `(d+1) ∣ (i+1)`. -/
def divMatrix (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i d => if (d:ℕ)+1 ∣ (i:ℕ)+1 then 1 else 0

lemma det_divMatrix (n : ℕ) : (divMatrix R n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one; intro i _; simp [divMatrix]
  · intro i j hij
    simp only [divMatrix]; rw [if_neg]
    intro hd
    have := Nat.le_of_dvd (Nat.succ_pos _) hd
    have : (i:ℕ) < (j:ℕ) := hij; omega

/-- **Smith's determinant (general form).** For `f : ℕ → R`, the matrix with entries
`∑_{d ∣ gcd(i+1,j+1)} f d` has determinant `∏_{k=1}^n f k`. -/
theorem det_gcdDivSum (f : ℕ → R) (n : ℕ) :
    (Matrix.of fun i j : Fin n => ∑ d ∈ (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1)).divisors, f d).det
      = ∏ k : Fin n, f ((k:ℕ)+1) := by
  have hfact : (Matrix.of fun i j : Fin n =>
        ∑ d ∈ (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1)).divisors, f d)
      = divMatrix R n * Matrix.diagonal (fun d : Fin n => f ((d:ℕ)+1)) * (divMatrix R n)ᵀ := by
    ext i j
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, Matrix.transpose_apply, divMatrix, Matrix.of_apply]
    have hm0 : 0 < Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) := Nat.gcd_pos_iff.mpr (Or.inl (Nat.succ_pos _))
    have hm : Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) ≤ n := by
      have h1 : Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) ≤ (i:ℕ)+1 := Nat.gcd_le_left _ (Nat.succ_pos _)
      have := i.isLt; omega
    rw [← sum_fin_dvd_eq f hm hm0]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h1 : (e:ℕ)+1 ∣ (i:ℕ)+1 <;> by_cases h2 : (e:ℕ)+1 ∣ (j:ℕ)+1 <;>
      simp [h1, h2, Nat.dvd_gcd_iff]
  rw [hfact, Matrix.det_mul, Matrix.det_mul, det_divMatrix, Matrix.det_transpose,
    det_divMatrix, Matrix.det_diagonal]
  simp

/-- **Smith's theorem (1875).** `det[gcd(i,j)]_{1 ≤ i,j ≤ n} = ∏_{k=1}^n φ(k)`. -/
theorem det_gcd_eq_prod_totient (n : ℕ) :
    (Matrix.of fun i j : Fin n => (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) : ℤ)).det
      = ∏ k : Fin n, (Nat.totient ((k:ℕ)+1) : ℤ) := by
  have hrw : (Matrix.of fun i j : Fin n => (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1) : ℤ))
      = (Matrix.of fun i j : Fin n =>
          ∑ d ∈ (Nat.gcd ((i:ℕ)+1) ((j:ℕ)+1)).divisors, (Nat.totient d : ℤ)) := by
    ext i j; simp only [Matrix.of_apply]; rw [← Nat.cast_sum, Nat.sum_totient]
  rw [hrw, det_gcdDivSum]

end Smith
