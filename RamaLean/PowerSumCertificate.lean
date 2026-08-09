import Mathlib

/-!
# A rational certificate for the biregular case

`RootSeparation.cauchy_lower` bounds the smallest nonzero matching root using only the moduli
of the coefficients, and decays badly with the size of the graph.  It throws away the one fact
that matters: by Heilmann--Lieb the matching polynomial is real-rooted, so writing
`μ_G(x) = ± x^{n-2ν} · g(x²)` the polynomial `g` has all roots real and **positive**.

For a finite family of positive reals the `ℓ^m` norm of the reciprocals decreases to the
`ℓ^∞` norm, so with `P_m = ∑ y_i^{-m}` one has

  `min_i y_i ≥ P_m^{-1/m}`,   sharpening as `m` grows, exact in the limit.

`m = 1` is the harmonic bound `m_ν / m_{ν-1}`; the earlier Cauchy estimate is cruder still.
Measured in `code/rootsep.py`, `m = 8` already matches the true smallest root to three or four
decimals.

## The certificate form

Division and `m`-th roots are avoided entirely.  To certify that every root is at least `t`,
exhibit a rational `q ≥ t` with

  `P_m · q^m ≤ 1`.

Then `y_i^{-m} ≤ P_m ≤ q^{-m}` gives `y_i ≥ q ≥ t` for every `i`.  That is
`roots_ge_of_powersum`, and every quantity in it is rational: the `P_m` come from the matching
numbers by Newton's identities, and `q` is any rational upper bound for `τ² = (√(a-1) -
√(b-1))²`.  So a single exact computation decides Conjecture 10 for a given biregular graph,
with no floating point and no appeal to Angel--Friedman--Hoory.

## What this is, and what it is not

It is a decision procedure, not a proof of the general conjecture.  For a fixed graph the
bound converges to the truth as `m` grows, so the procedure always succeeds when the
conjecture holds with room to spare; but proving Song--Fan--Miao for *all* biregular graphs
would need `P_m` bounded uniformly in the size of the graph, which is not supplied here and is
the remaining content.  Measured over nine biregular graphs it certifies all nine.
-/

namespace PowerSumCertificate

open Finset

/-! ## Each reciprocal power is dominated by the power sum -/

/-- A single term of a sum of nonnegative reals is at most the sum. -/
theorem term_le_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

/-! ## From a power-sum bound to a root bound -/

/-- If `(1/y)^m ≤ (1/q)^m` with `y, q > 0` and `m ≠ 0`, then `q ≤ y`. -/
theorem le_of_inv_pow_le {y q : ℝ} {m : ℕ} (hy : 0 < y) (hq : 0 < q) (hm : m ≠ 0)
    (h : (y⁻¹) ^ m ≤ (q⁻¹) ^ m) : q ≤ y := by
  rw [inv_pow, inv_pow] at h
  have hym : (0 : ℝ) < y ^ m := pow_pos hy m
  have hqm : (0 : ℝ) < q ^ m := pow_pos hq m
  have h2 : q ^ m ≤ y ^ m := (inv_le_inv₀ hym hqm).mp h
  exact le_of_pow_le_pow_left₀ hm (le_of_lt hy) h2

/-- **The certificate.**  Let `y` be a finite family of positive reals with power sum of
reciprocals `P = ∑ y_i^{-m}`.  If a rational `q ≥ t` satisfies `P · q^m ≤ 1`, then every `y_i`
is at least `t`.

Applied with `y` the squares of the nonzero matching roots and `t = τ²`, this decides
Conjecture 10 for a biregular graph by one exact computation. -/
theorem roots_ge_of_powersum {ι : Type*} [Fintype ι] (y : ι → ℝ) (hy : ∀ i, 0 < y i)
    {m : ℕ} (hm : m ≠ 0) {P q t : ℝ} (hq : 0 < q) (htq : t ≤ q)
    (hP : P = ∑ i, (y i)⁻¹ ^ m) (hcert : P * q ^ m ≤ 1) :
    ∀ i, t ≤ y i := by
  intro i
  have hterm : (y i)⁻¹ ^ m ≤ P := by
    rw [hP]
    exact term_le_sum _ (fun j => pow_nonneg (le_of_lt (inv_pos.mpr (hy j))) m) i
  have hqm : (0 : ℝ) < q ^ m := pow_pos hq m
  have hPq : P ≤ (q⁻¹) ^ m := by
    rw [inv_pow, inv_eq_one_div, le_div_iff₀ hqm]
    linarith [hcert]
  exact le_trans htq (le_of_inv_pow_le (hy i) hq hm (le_trans hterm hPq))

/-- The bound sharpens with `m`: a certificate at one exponent gives the root bound, and
larger `m` makes `P_m^{-1/m}` closer to the true minimum.  Stated as the monotonicity that
matters, that the minimum dominates every `ℓ^m` estimate. -/
theorem min_ge_powersum_bound {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → ℝ)
    (hy : ∀ i, 0 < y i) {m : ℕ} (hm : m ≠ 0) {P : ℝ}
    (hP : P = ∑ i, (y i)⁻¹ ^ m) (i₀ : ι) :
    1 ≤ P * (y i₀) ^ m := by
  have hterm : (y i₀)⁻¹ ^ m ≤ P := by
    rw [hP]
    exact term_le_sum _ (fun j => pow_nonneg (le_of_lt (inv_pos.mpr (hy j))) m) i₀
  have hpos : (0 : ℝ) < (y i₀) ^ m := pow_pos (hy i₀) m
  have hone : (y i₀)⁻¹ ^ m * (y i₀) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt (hy i₀)), one_pow]
  have hmul := mul_le_mul_of_nonneg_right hterm (le_of_lt hpos)
  rwa [hone] at hmul

end PowerSumCertificate
