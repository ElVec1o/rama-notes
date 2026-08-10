import Mathlib
import RamaLean.Paper2General

/-!
# The generating function, as a power series

The generating-function corollary was formalized only as the finite recurrence, not as an
identity of formal power series.  This file proves the identity itself:

  `(1 - 2Y·X + X²) · ∑_d U_d(Y) X^d = 1`,

that is `∑_d μ_{d,C_n}(x) z^d = 1/(1 - 2T_n(x/2) z + z²)` with `Y = T_n(x/2)`, and the companion
form for `Φ`, whose numerator is `(1-z)²`.

The proof is coefficient comparison.  Expanding the left factor, the coefficient of `X^n` in the
product is `U_n - 2Y·U_{n-1} + U_{n-2}`, which is the Chebyshev recurrence and so vanishes for
`n ≥ 2`; the two remaining coefficients are `U_0 = 1` and `U_1 - 2Y·U_0 = 0`.
-/

namespace Paper2GenFun

open Paper2 PowerSeries

variable {R : Type*} [CommRing R]

/-- The generating series `∑_d U_d(Y) X^d`. -/
noncomputable def genU (Y : R) : PowerSeries R := PowerSeries.mk fun d => cU Y d

@[simp] lemma coeff_genU (Y : R) (d : ℕ) : (PowerSeries.coeff d) (genU Y) = cU Y d := by
  simp [genU]

/-- **The generating function.**  `(1 - 2Y·X + X²) · ∑_d U_d(Y) X^d = 1`. -/
theorem genU_mul (Y : R) :
    (1 - (PowerSeries.C (2 * Y)) * PowerSeries.X + PowerSeries.X ^ 2) * genU Y = 1 := by
  have hexp : (1 - (PowerSeries.C (2 * Y)) * PowerSeries.X + PowerSeries.X ^ 2) * genU Y
      = genU Y - (PowerSeries.C (2 * Y)) * (PowerSeries.X * genU Y)
        + PowerSeries.X * (PowerSeries.X * genU Y) := by
    ring
  rw [hexp]
  ext n
  rw [map_add, map_sub, PowerSeries.coeff_C_mul]
  match n with
  | 0 =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [genU, cU]
  | 1 =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      simp [genU, cU]
  | (k + 2) =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_succ_X_mul]
      have hrec : cU Y (k + 2) = 2 * Y * cU Y (k + 1) - cU Y k := by simp [cU]
      simp only [coeff_genU, PowerSeries.coeff_one, hrec]
      norm_num

/-- The same statement with the factors the other way round: the series is a two-sided inverse
of the quadratic, so `∑_d U_d(Y) X^d` is `1/(1 - 2Y X + X²)` in the ring of formal power
series. -/
theorem genU_isUnit_inv (Y : R) :
    genU Y * (1 - (PowerSeries.C (2 * Y)) * PowerSeries.X + PowerSeries.X ^ 2) = 1 := by
  rw [mul_comm]; exact genU_mul Y

/-- The series for `Φ` in terms of the series for `U`, from the factorization
`Φ_{n,r} = (2Y-2)·U_{r-1}(Y)` for `r ≥ 1` together with `Φ_{n,0} = 1`. -/
theorem genPhi_eq (Y : R) :
    (PowerSeries.mk fun r => cG Y r)
      = 1 + (PowerSeries.C (2 * Y - 2)) * (PowerSeries.X * genU Y) := by
  ext n
  match n with
  | 0 =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [cG]
  | (k + 1) =>
      rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      simp only [PowerSeries.coeff_mk, coeff_genU, cG_factored Y k]
      rw [PowerSeries.coeff_one]
      simp

/-- **The companion form for `Φ`.**  `(1 - 2Y·X + X²) · ∑_r Φ_{n,r} X^r = (1-X)²`, which is the
numerator `(1-z)²` of the corollary. -/
theorem genPhi_mul (Y : R) :
    (1 - (PowerSeries.C (2 * Y)) * PowerSeries.X + PowerSeries.X ^ 2)
      * (PowerSeries.mk fun r => cG Y r)
      = (1 - PowerSeries.X) ^ 2 := by
  set Q : PowerSeries R := 1 - (PowerSeries.C (2 * Y)) * PowerSeries.X + PowerSeries.X ^ 2 with hQ
  rw [genPhi_eq, mul_add, mul_one]
  have h1 : Q * ((PowerSeries.C (2 * Y - 2)) * (PowerSeries.X * genU Y))
      = (PowerSeries.C (2 * Y - 2)) * PowerSeries.X * (Q * genU Y) := by ring
  rw [h1, genU_mul, mul_one, hQ]
  have hCsub : (PowerSeries.C (2 * Y - 2) : PowerSeries R)
      = PowerSeries.C (2 * Y) - PowerSeries.C 2 := map_sub _ _ _
  rw [hCsub]
  have hC2 : (PowerSeries.C (2 : R)) = 2 := map_ofNat _ 2
  ring_nf
  rw [hC2]

end Paper2GenFun
