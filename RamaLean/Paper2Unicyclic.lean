import RamaLean.Paper2General

/-!
# The homogenized Chebyshev recurrence behind unicyclic `d`-matching polynomials

For a connected graph `G` of first Betti number `1` with unique non-tree edge `e`, write the twisted
characteristic polynomial as `det(xI - A_G(z)) = A(x) + B(x)(z + z⁻¹)`; concretely
`A = (χ⁺ + χ⁻)/2` and `B = (χ⁺ - χ⁻)/4`, where `χ±` are the characteristic polynomials of `G` with
`e` weighted `±1`.  The `d`-matching polynomial of `G` is then `cV A B d`, where

  `cV A B 0 = 1`,  `cV A B 1 = A`,  `cV A B (d+2) = A * cV A B (d+1) - B^2 * cV A B d`.

This file formalizes the algebra of that recurrence over an arbitrary commutative ring:

* `cV_homogeneous` — `cV (c*A) (c*B) d = c^d * cV A B d`, so `cV` is the homogenization of a
  one-variable sequence;
* `cV_neg_right` — `cV` depends on `B` only through `B^2`;
* `cV_cycle` — the specialization `A = 2Y`, `B = -1` recovers `cU Y d = U_d(Y)`, the second-kind
  Chebyshev sequence.  Since a cycle `C_m` has `A = 2T_m(x/2)` and `B = -1`, this is exactly the
  cycle case `μ_{d,C_m} = U_d(T_m(x/2))` of `Paper2General`;
* `cV_eq_cheb` — over a field, with `B` invertible, `cV A B d = (-B)^d * cU (-A/(2B)) d`.

The graph-theoretic input (that the `d`-matching polynomial of a unicyclic graph is this sequence)
is not formalized here; only the polynomial algebra is.
-/

namespace Paper2Unicyclic

open Paper2

variable {R : Type*} [CommRing R]

/-- The homogenized Chebyshev sequence: `V₀ = 1`, `V₁ = A`, `V_{d+2} = A·V_{d+1} - B²·V_d`. -/
def cV (A B : R) : ℕ → R
  | 0 => 1
  | 1 => A
  | (d + 2) => A * cV A B (d + 1) - B ^ 2 * cV A B d

@[simp] lemma cV_zero (A B : R) : cV A B 0 = 1 := rfl
@[simp] lemma cV_one (A B : R) : cV A B 1 = A := rfl

lemma cV_add_two (A B : R) (d : ℕ) :
    cV A B (d + 2) = A * cV A B (d + 1) - B ^ 2 * cV A B d := rfl

lemma cV_two (A B : R) : cV A B 2 = A ^ 2 - B ^ 2 := by
  rw [cV_add_two, cV_one, cV_zero]; ring

lemma cV_three (A B : R) : cV A B 3 = A ^ 3 - 2 * A * B ^ 2 := by
  rw [cV_add_two, cV_two, cV_one]; ring

/-- `cV` depends on `B` only through `B²`. -/
lemma cV_neg_right (A B : R) : ∀ d, cV A (-B) d = cV A B d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => rfl
    | 1 => rfl
    | (k + 2) =>
      rw [cV_add_two, cV_add_two, ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- **Homogeneity**: `cV (c·A) (c·B) d = c^d · cV A B d`. -/
theorem cV_homogeneous (c A B : R) : ∀ d, cV (c * A) (c * B) d = c ^ d * cV A B d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp
    | 1 => simp
    | (k + 2) =>
      rw [cV_add_two, cV_add_two, ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- **The cycle case**: at `A = 2Y`, `B = -1` the sequence is the second-kind Chebyshev sequence.
For a cycle `C_m` one has `A = 2·T_m(x/2)` and `B = -1`, so this specializes the unicyclic
recurrence to `μ_{d,C_m} = U_d(T_m(x/2))`. -/
theorem cV_cycle (Y : R) : ∀ d, cV (2 * Y) (-1 : R) d = cU Y d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => rfl
    | 1 => rfl
    | (k + 2) =>
      rw [cV_add_two, ih (k + 1) (by omega), ih k (by omega)]
      show 2 * Y * cU Y (k + 1) - (-1 : R) ^ 2 * cU Y k = cU Y (k + 2)
      rw [show cU Y (k + 2) = 2 * Y * cU Y (k + 1) - cU Y k from rfl]
      ring

/-- Over a field, with `B` invertible, `cV` is a scaled Chebyshev value:
`cV A B d = (-B)^d · U_d(-A/(2B))`. -/
theorem cV_eq_cheb {K : Type*} [Field K] (A B : K) (hB : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    ∀ d, cV A B d = (-B) ^ d * cU (-A / (2 * B)) d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp [cU_zero]
    | 1 =>
      show A = (-B) ^ 1 * cU (-A / (2 * B)) 1
      rw [pow_one, show cU (-A / (2 * B)) 1 = 2 * (-A / (2 * B)) from rfl]
      field_simp
    | (k + 2) =>
      rw [cV_add_two, ih (k + 1) (by omega), ih k (by omega)]
      show A * ((-B) ^ (k + 1) * cU (-A / (2 * B)) (k + 1)) - B ^ 2 * ((-B) ^ k * cU (-A / (2 * B)) k)
        = (-B) ^ (k + 2) * cU (-A / (2 * B)) (k + 2)
      rw [show cU (-A / (2 * B)) (k + 2)
            = 2 * (-A / (2 * B)) * cU (-A / (2 * B)) (k + 1) - cU (-A / (2 * B)) k from rfl]
      have h : (2 : K) * B ≠ 0 := mul_ne_zero h2 hB
      field_simp
      ring



/-!
## Root localization

The mathematical content of the unicyclic theorem is not the recurrence but where its roots can be.
`cV A B d = 0` forces `|A / (2B)| ≤ 1`, i.e. the root lies in the Floquet band
`{x : |μ_G(x)| ≤ 2|μ_{G-V(C)}(x)|}`, which is the spectrum of the universal cover.  Everything below
is over a `LinearOrderedField`, and the engine is that `U_d` has no root outside `[-1,1]`.
-/

section Localization

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For `y ≥ 1` the Chebyshev values are increasing and at least one: `cU y (d+1) ≥ cU y d ≥ 1`. -/
lemma cU_ge_one_of_one_le {y : K} (hy : 1 ≤ y) :
    ∀ d, 1 ≤ cU y d ∧ cU y d ≤ cU y (d + 1) := by
  intro d
  induction d with
  | zero =>
    constructor
    · exact le_of_eq (cU_zero y).symm
    · rw [cU_zero, cU_one]; linarith
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hk1 : 1 ≤ cU y (k + 1) := le_trans h1 h2
    refine ⟨hk1, ?_⟩
    have hrec : cU y (k + 2) = 2 * y * cU y (k + 1) - cU y k := rfl
    have : 2 * y * cU y (k + 1) ≥ 2 * cU y (k + 1) := by nlinarith
    linarith [hrec, this, h2]

/-- `U_d` is nonzero outside `[-1,1]`: for `1 ≤ y`, `cU y d ≥ 1 > 0`. -/
lemma cU_pos_of_one_le {y : K} (hy : 1 ≤ y) (d : ℕ) : 0 < cU y d :=
  lt_of_lt_of_le zero_lt_one (cU_ge_one_of_one_le hy d).1

/-- `cU` alternates under negation: `cU (-y) d = (-1)^d * cU y d`. -/
lemma cU_neg (y : K) : ∀ d, cU (-y) d = (-1 : K) ^ d * cU y d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp [cU_zero]
    | 1 => rw [show cU (-y) 1 = 2 * (-y) from rfl, show cU y 1 = 2 * y from rfl]; ring
    | (k + 2) =>
      have e2 : cU (-y) (k + 2) = 2 * (-y) * cU (-y) (k + 1) - cU (-y) k := rfl
      have e1 : cU y (k + 2) = 2 * y * cU y (k + 1) - cU y k := rfl
      rw [e2, ih (k + 1) (by omega), ih k (by omega), e1]
      ring

/-- **`U_d` has no root of absolute value `≥ 1`.** -/
theorem cU_ne_zero_of_one_le_abs {y : K} (hy : 1 ≤ |y|) (d : ℕ) : cU y d ≠ 0 := by
  rcases abs_cases y with ⟨he, _⟩ | ⟨he, _⟩
  · exact ne_of_gt (cU_pos_of_one_le (he ▸ hy) d)
  · have hneg : (1 : K) ≤ -y := by rw [he] at hy; exact hy
    have : cU (-(-y)) d = (-1 : K) ^ d * cU (-y) d := cU_neg (-y) d
    rw [neg_neg] at this
    have hpos : 0 < cU (-y) d := cU_pos_of_one_le hneg d
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt hpos)

/-- **Root localization.** If `cV A B d` vanishes and `B ≠ 0`, then `|A| ≤ 2|B|`.
For a unicyclic graph with `A = μ_G` and `B = -μ_{G-V(C)}` this says every root of the
`d`-matching polynomial lies in the Floquet band `|μ_G| ≤ 2|μ_{G-V(C)}|`, i.e. in the spectrum of
the universal cover -- never in a spectral gap, for any `d`. -/
theorem cV_root_mem_band {A B : K} (hB : B ≠ 0) (h2 : (2 : K) ≠ 0) {d : ℕ}
    (hroot : cV A B d = 0) : |A| ≤ 2 * |B| := by
  by_contra hcon
  push_neg at hcon
  -- |−A/(2B)| ≥ 1, so the Chebyshev factor cannot vanish
  have hy : (1 : K) ≤ |(-A) / (2 * B)| := by
    rw [abs_div, abs_neg, abs_mul, abs_two]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have := cV_eq_cheb A B hB h2 d
  rw [hroot] at this
  have hne : cU ((-A) / (2 * B)) d ≠ 0 := cU_ne_zero_of_one_le_abs hy d
  have hBd : (-B) ^ d ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hB)
  exact (mul_ne_zero hBd hne) this.symm

end Localization

end Paper2Unicyclic
