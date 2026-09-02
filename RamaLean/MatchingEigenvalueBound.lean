import Mathlib

/-!
# Every nonzero eigenvalue of a forest is bounded below by a ratio of matching numbers

For a forest `F` the characteristic polynomial and the matching polynomial coincide, so
`μ_F(x) = x^(n - 2ν) * Q(x²)` where `ν` is the matching number and
`Q(y) = Σ_j (-1)^(ν-j) m_(ν-j) y^j` has the squares of the nonzero eigenvalues as its `ν` roots,
all of them positive. Vieta on the bottom two coefficients of `Q` gives

  `Σ_j 1/y_j = e_(ν-1)/e_ν = m_(ν-1)/m_ν`,

and the reciprocal of a sum of positive terms bounds each term from below. Hence every nonzero
eigenvalue `θ` of `F` satisfies

  `θ² ≥ m_ν / m_(ν-1)`.

The content is the elementary inequality; the identification of the sum of reciprocals with
`m_(ν-1)/m_ν` is Vieta and is supplied as a hypothesis, exactly as the criterion of [BGM] is
supplied as a hypothesis elsewhere in this development.

Numerically the bound is within about ten percent of the truth: over trees of order `n = 2m` the
maximum of `m_(ν-1)/m_ν` is `m(m+1)/2`, attained by the path, so the bound reads
`|θ| ≥ √(2/(m(m+1))) ≈ √2/m` against the true minimum `2 sin(π/(2(2m+1))) ≈ π/(2m)`.
-/

open Finset

/-- If positive reals have reciprocal sum `R`, each of them is at least `1/R`. -/
theorem le_of_inv_sum {ι : Type*} (s : Finset ι) (y : ι → ℝ) (R : ℝ)
    (hpos : ∀ i ∈ s, 0 < y i)
    (hR : R = ∑ i ∈ s, (y i)⁻¹)
    {j : ι} (hj : j ∈ s) :
    R⁻¹ ≤ y j := by
  have hyj : 0 < y j := hpos j hj
  have hterm : (y j)⁻¹ ≤ R := by
    rw [hR]
    refine Finset.single_le_sum (f := fun i => (y i)⁻¹) ?_ hj
    intro i hi
    exact le_of_lt (inv_pos.mpr (hpos i hi))
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.mpr hyj) hterm
  have h1 : 1 ≤ R * y j := by
    have := mul_le_mul_of_nonneg_right hterm (le_of_lt hyj)
    rwa [inv_mul_cancel₀ (ne_of_gt hyj)] at this
  have hRi : 0 < R⁻¹ := inv_pos.mpr hRpos
  calc R⁻¹ = R⁻¹ * 1 := by ring
    _ ≤ R⁻¹ * (R * y j) := by nlinarith
    _ = y j := by field_simp

/-- The matching bound. `y` enumerates the squares of the nonzero eigenvalues of a forest, `mnu`
and `mnu1` are `m_ν` and `m_(ν-1)`, and the Vieta identity enters as `hvieta`. Then the square of
every nonzero eigenvalue is at least `m_ν / m_(ν-1)`. -/
theorem eigenvalue_sq_ge_matching_ratio {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (mnu mnu1 : ℝ)
    (hpos : ∀ i ∈ s, 0 < y i)
    (hmnu : 0 < mnu)
    (hvieta : ∑ i ∈ s, (y i)⁻¹ = mnu1 / mnu)
    {j : ι} (hj : j ∈ s) :
    mnu / mnu1 ≤ y j := by
  have h := le_of_inv_sum s y (mnu1 / mnu) hpos hvieta.symm hj
  have hm1 : 0 < mnu1 := by
    have hyj : 0 < y j := hpos j hj
    have : 0 < mnu1 / mnu := lt_of_lt_of_le (inv_pos.mpr hyj) (by
      rw [← hvieta]
      exact Finset.single_le_sum (f := fun i => (y i)⁻¹)
        (fun i hi => le_of_lt (inv_pos.mpr (hpos i hi))) hj)
    exact (div_pos_iff_of_pos_right hmnu).mp this
  rwa [inv_div] at h

/-- Restated as the size bound that feeds `degree_bound_kappa`: if `|θ|` is small then
`m_(ν-1)` is large, so the forest cannot be small. -/
theorem matching_ratio_of_small_eigenvalue {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (mnu mnu1 : ℝ)
    (hpos : ∀ i ∈ s, 0 < y i)
    (hmnu : 0 < mnu)
    (hvieta : ∑ i ∈ s, (y i)⁻¹ = mnu1 / mnu)
    {j : ι} (hj : j ∈ s) :
    mnu ≤ y j * mnu1 := by
  have hb := eigenvalue_sq_ge_matching_ratio s y mnu mnu1 hpos hmnu hvieta hj
  have hm1 : 0 < mnu1 := by
    have hsum : 0 < mnu1 / mnu := by
      rw [← hvieta]
      exact lt_of_lt_of_le (inv_pos.mpr (hpos j hj))
        (Finset.single_le_sum (f := fun i => (y i)⁻¹)
          (fun i hi => le_of_lt (inv_pos.mpr (hpos i hi))) hj)
    exact (div_pos_iff_of_pos_right hmnu).mp hsum
  rw [div_le_iff₀ hm1] at hb
  linarith

/-- The case a tree of even order with a perfect matching: a tree has at most one perfect
matching, so `m_ν = 1` and the ratio collapses to `m_(ν-1)`, which the path maximizes. Given any
upper bound `B` on `m_(ν-1)`, every nonzero eigenvalue satisfies `θ² ≥ 1/B`. -/
theorem eigenvalue_sq_ge_inv_of_unique_perfect_matching {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (mnu1 B : ℝ)
    (hpos : ∀ i ∈ s, 0 < y i)
    (hvieta : ∑ i ∈ s, (y i)⁻¹ = mnu1 / 1)
    (hB : mnu1 ≤ B)
    {j : ι} (hj : j ∈ s) :
    B⁻¹ ≤ y j := by
  have h := eigenvalue_sq_ge_matching_ratio s y 1 mnu1 hpos one_pos hvieta hj
  rw [one_div] at h
  have hm1 : 0 < mnu1 := by
    have hsum : 0 < mnu1 / 1 := by
      rw [← hvieta]
      exact lt_of_lt_of_le (inv_pos.mpr (hpos j hj))
        (Finset.single_le_sum (f := fun i => (y i)⁻¹)
          (fun i hi => le_of_lt (inv_pos.mpr (hpos i hi))) hj)
    simpa using hsum
  have hBpos : 0 < B := lt_of_lt_of_le hm1 hB
  have : B⁻¹ ≤ mnu1⁻¹ := by
    rw [inv_le_inv₀ hBpos hm1]; exact hB
  exact le_trans this h

/-!
## The interlacing step

For a forest with matching number `ν` the nonzero eigenvalues are exactly `2ν` in number, so
`R(F) = m_(ν-1)/m_ν = Σ_j λ_j⁻²` over the `ν` positive ones. If `u` is a vertex missed by some
maximum matching then `ν(F - u) = ν`, so `F - u` also has exactly `ν` positive eigenvalues, and
Cauchy interlacing gives `0 < λ_j(F - u) ≤ λ_j(F)` for every `j`. The sum of reciprocal squares
therefore reverses, which is the content below: deleting an exposed vertex cannot decrease `R`.

Iterating lands on a forest of order `2ν` with a perfect matching, where `m_ν = 1` and the classical
theorem of Gutman bounds `m_(ν-1)` by that of the path. So `R ≤ ν(ν+1)/2` for every forest, and
with `eigenvalue_sq_ge_matching_ratio` every nonzero eigenvalue satisfies `θ² ≥ 2/(ν(ν+1))`.
-/

/-- Interlacing reverses the sum of reciprocal squares: if `a i ≤ b i` with `a i` positive, then
the sum over `b` is at most the sum over `a`. Applied with `a = λ(F - u)` and `b = λ(F)` this says
`R(F) ≤ R(F - u)`. -/
theorem sum_inv_sq_antitone {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a i)
    (hle : ∀ i ∈ s, a i ≤ b i) :
    ∑ i ∈ s, (b i)⁻¹ ^ 2 ≤ ∑ i ∈ s, (a i)⁻¹ ^ 2 := by
  refine Finset.sum_le_sum ?_
  intro i hi
  have ha : 0 < a i := hpos i hi
  have hb : 0 < b i := lt_of_lt_of_le ha (hle i hi)
  have : (b i)⁻¹ ≤ (a i)⁻¹ := by
    rw [inv_le_inv₀ hb ha]; exact hle i hi
  have h0 : (0:ℝ) ≤ (b i)⁻¹ := le_of_lt (inv_pos.mpr hb)
  nlinarith [this, h0]

/-- The closed chain. With `R ≤ ν(ν+1)/2` for a forest of matching number `ν`, every nonzero
eigenvalue satisfies `θ² ≥ 2/(ν(ν+1))`. -/
theorem eigenvalue_sq_ge_two_div {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (mnu mnu1 : ℝ) (nu : ℝ)
    (hpos : ∀ i ∈ s, 0 < y i)
    (hmnu : 0 < mnu)
    (hnu : 0 < nu)
    (hvieta : ∑ i ∈ s, (y i)⁻¹ = mnu1 / mnu)
    (hratio : mnu1 / mnu ≤ nu * (nu + 1) / 2)
    {j : ι} (hj : j ∈ s) :
    2 / (nu * (nu + 1)) ≤ y j := by
  have hd : 0 < nu * (nu + 1) := mul_pos hnu (by linarith)
  have hterm : (y j)⁻¹ ≤ nu * (nu + 1) / 2 := by
    refine le_trans ?_ hratio
    rw [← hvieta]
    exact Finset.single_le_sum (f := fun i => (y i)⁻¹)
      (fun i hi => le_of_lt (inv_pos.mpr (hpos i hi))) hj
  have hyj : 0 < y j := hpos j hj
  have h1 : 1 ≤ (nu * (nu + 1) / 2) * y j := by
    have := mul_le_mul_of_nonneg_right hterm (le_of_lt hyj)
    rwa [inv_mul_cancel₀ (ne_of_gt hyj)] at this
  rw [div_le_iff₀ hd]
  nlinarith [h1, hyj, hd]
