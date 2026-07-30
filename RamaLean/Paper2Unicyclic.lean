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

end Paper2Unicyclic
