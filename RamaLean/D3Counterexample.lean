import Mathlib

/-!
# Conjecture D3 is false: the arithmetic of the certificate

Conjecture D3 of paper 2a asserts that every finite graph of minimum degree at least three satisfies
`Zeros(μ_G) ⊆ spec(T_G)`. It is false. The counterexample has two hubs, three copies of the star
`K_{1,3}`, and every leaf joined to both hubs: simple, connected, bipartite, `14` vertices,
`27` edges, minimum degree three, and

  `μ_G = x^4 (x^2 - 3) (x^8 - 24x^6 + 171x^4 - 396x^2 + 270)`,

so `√3` is a root, while `√3 ∉ spec(T_G)`.

## What is formalised here, and what is not

The graph-theoretic half is exact but combinatorial and lives in `code/d3_counterexample.py`: the
matching polynomial is computed from the graph by the deletion recursion and `(x^2 - 3)` is divided
out over `ℚ`. Mathlib carries no matching polynomial, which is the same blocker recorded throughout
this development.

What is formalised is the *arithmetic* of the spectral certificate, which is where the content sits
and where a slip would be invisible. On the four directed-edge orbits

  `g₁ = centre → leaf`, `g₂ = leaf → centre`, `g₃ = leaf → hub`, `g₄ = hub → leaf`

the cavity system at `λ` reads

  `λ = 1/g₁ + 2g₃`,  `λ = 1/g₂ + 2g₁`,  `λ = 1/g₃ + 8g₄`,  `λ = 1/g₄ + g₂ + g₃`,

and at `λ = √3` the certifying branch has `g₃ = 0` and `g₄ = ∞`. That is a pole of the coordinate,
not a spectral point: the pair escapes along `g₃g₄ → -1/8`, and only that product enters the decay.
`cavity_one` and `cavity_two` verify the two finite equations at `g₁ = 1/√3`, `g₂ = √3`, `g₃ = 0`.

The decay quotient's characteristic polynomial is `t^4 - t^2/8 - 1/2`, whose coefficients are finite
because the determinant collects only vertex-disjoint cycle collections and the two cycles present
share vertices. `decay_root_lt_one` is the statement that matters: every real root has modulus below
one, which is what the Angel--Friedman--Hoory criterion consumes. The inequality reduces to
`√129 < 15`, that is to `129 < 225`.

The remaining possibility, that `√3` is an *isolated point* of `spec(T_G)`, is not a formality: the
spectrum is closed, and the biregular cover in this same paper carries an isolated `{0}`. It is
excluded by the vertex Green's functions being finite at `√3`, since an atom forces a pole with the
eigenvector weight as residue. `green_hub`, `green_centre` and `green_sum` are those values.

The AFH criterion itself, that decay below one places `λ` outside the spectrum of the universal
cover, is not formalised; it is the analytic input, cited to \cite{AFH}.

## Status

`cavity_one`, `cavity_two`, `decay_char_factor`, `decay_root_lt_one`, `green_hub`, `green_centre`
and `green_sum` are `VERIFIED`. The matching polynomial computation and the AFH criterion carry
formalisation debt, recorded above.
-/

namespace D3Counterexample

open Real

/-! ### The cavity solution at `λ = √3` -/

private lemma sqrt3_pos : (0:ℝ) < sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private lemma sq_sqrt3 : sqrt 3 * sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma inv_sqrt3 : (sqrt 3)⁻¹ = sqrt 3 / 3 := by
  rw [eq_div_iff (by norm_num : (3:ℝ) ≠ 0), inv_mul_eq_div,
    div_eq_iff sqrt3_pos.ne']
  exact sq_sqrt3.symm

/-- **Cavity equation (1)** at the certifying branch: with `g₃ = 0`, the equation
`λ = 1/g₁ + 2g₃` forces `g₁ = 1/√3`. -/
theorem cavity_one : (1 / sqrt 3)⁻¹ + 2 * 0 = sqrt 3 := by
  rw [one_div, inv_inv, mul_zero, add_zero]

/-- **Cavity equation (2)**: with `g₁ = 1/√3` the equation `λ = 1/g₂ + 2g₁` forces `g₂ = √3`,
because `√3 - 2/√3 = 1/√3`. -/
theorem cavity_two : (sqrt 3)⁻¹ + 2 * (1 / sqrt 3) = sqrt 3 := by
  rw [one_div, inv_sqrt3]
  ring

/-- **The product the degenerate pair escapes along.**  Putting `g₃ = ε` and solving `(3)` for `g₄`
gives `g₃g₄ = (λε - 1)/8`, which tends to `-1/8`. This is the algebraic content of the pole: the
individual coordinates diverge, their product does not. -/
theorem cavity_product (lam ε : ℝ) (hε : ε ≠ 0) :
    ε * ((lam - 1 / ε) / 8) = (lam * ε - 1) / 8 := by
  field_simp

/-! ### The decay quotient -/

/-- **The characteristic polynomial factors through `t²`.**  `t^4 - t^2/8 - 1/2` is
`8s² - s - 4 = 0` in `s = t²`, up to the factor `8`. -/
theorem decay_char_factor (t : ℝ) :
    8 * (t ^ 4 - t ^ 2 / 8 - 1 / 2) = 8 * (t ^ 2) ^ 2 - t ^ 2 - 4 := by
  ring

private lemma sqrt129_lt_15 : sqrt 129 < 15 := by
  have : (15:ℝ) = sqrt (225) := by
    rw [show (225:ℝ) = 15 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The positive root of the decay quotient.**  `s = (1 + √129)/16` solves `8s² - s - 4 = 0`, so
the spectral radius of the decay is `√((1 + √129)/16) = √(1 + √129)/4 = 0.8788…`. -/
theorem decay_root_value :
    8 * ((1 + sqrt 129) / 16) ^ 2 - ((1 + sqrt 129) / 16) - 4 = 0 := by
  have h : sqrt 129 * sqrt 129 = 129 := Real.mul_self_sqrt (by norm_num)
  linear_combination h / 32

/-- **That root is below one**, exactly because `129 < 225`. -/
theorem decay_value_lt_one : (1 + sqrt 129) / 16 < 1 := by
  linarith [sqrt129_lt_15]

/-- **The decay is below one.**  Every real root of the decay quotient's characteristic polynomial
has modulus below one. This is what the Angel--Friedman--Hoory criterion consumes, and it is the
whole spectral certificate.

The bound needs no surd at all: with `s = t²`, `(s - 1)² ≥ 0` gives `8s² - 16s + 8 ≥ 0`, and
substituting `8s² = s + 4` leaves `15s ≤ 12`, so `s ≤ 4/5`. The value `(1 + √129)/16` recorded above
is the exact root; this is the inequality it satisfies. -/
theorem decay_root_lt_one (t : ℝ) (h : t ^ 4 - t ^ 2 / 8 - 1 / 2 = 0) : |t| < 1 := by
  have hs : 8 * (t ^ 2) ^ 2 - t ^ 2 - 4 = 0 := by
    rw [← decay_char_factor, h, mul_zero]
  have hlt : t ^ 2 < 1 := by nlinarith [hs, sq_nonneg (t ^ 2 - 1)]
  nlinarith [abs_nonneg t, sq_abs t, hlt]

/-! ### No atom at `√3` -/

/-- **The Green's function at a hub**, `1/(λ - 9g₃)` with `g₃ = 0`, is finite. -/
theorem green_hub : (sqrt 3 - 9 * 0)⁻¹ = sqrt 3 / 3 := by
  rw [mul_zero, sub_zero, inv_sqrt3]

/-- **The Green's function at a centre**, `1/(λ - 3g₂)` with `g₂ = √3`, is finite and negative. -/
theorem green_centre : (sqrt 3 - 3 * sqrt 3)⁻¹ = -(sqrt 3 / 6) := by
  rw [show sqrt 3 - 3 * sqrt 3 = -(2 * sqrt 3) by ring, inv_neg, mul_inv, inv_sqrt3]
  ring

/-- **The sum over the fourteen vertices**: two hubs, three centres, nine leaves, the leaves
contributing `0` because `g₄` is infinite there. Every term is finite, so no vertex Green's function
has a pole at `√3`, so the spectral measure has no atom there. -/
theorem green_sum : 2 * (sqrt 3 / 3) + 3 * (-(sqrt 3 / 6)) + 9 * 0 = sqrt 3 / 6 := by
  ring

end D3Counterexample
