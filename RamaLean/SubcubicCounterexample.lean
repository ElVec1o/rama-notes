import Mathlib

/-!
# A counterexample to Conjecture 10 with all degrees in `{2,3}`

Hall's counterexample refutes Conjecture 10 but has degrees `1` through `6`.  Two natural
repaired hypotheses survived it: minimum degree at least two, and bounded maximum degree.
A single graph on `31` vertices refutes both, and is smaller than Hall's.

## The graph

Take the rooted binary tree of depth three and identify each of its eight leaves with a
vertex of an attached triangle.  Internal skeleton vertices have degree three, each
attachment vertex has degree three (its parent plus two triangle neighbours), the remaining
triangle vertices have degree two, and the skeleton root has degree two.  So the degree set is
exactly `{2,3}`: `31` vertices, `38` edges, minimum degree two, maximum degree three.

## Why the polynomial is computable

The branches meet only along the skeleton, so the matching polynomial follows the rooted pair
recursion.  For a piece rooted at `r` with subpieces `P₁, P₂` joined to `r`,

  `μ_whole = X · A₁A₂ - B₁A₂ - B₂A₁`,   `μ_{whole - r} = A₁A₂`,

writing `(Aᵢ, Bᵢ) = (μ_{Pᵢ}, μ_{Pᵢ - root})`.  A triangle rooted at a vertex contributes
`(X³ - 3X, X² - 1)`.  Iterating three times gives `μ_G` of degree `31`, as it must be.

## What is proved here

`quartic_factor` is the heart: at depth two the recursion produces

  `X·A₁ - 2·B₁ = X²(X² - 3)(X⁴ - 7X² + 8)`,

so the quartic divides `A₂` and hence `μ_G = A₃`.  Its smaller positive root
`θ = √((7 - √17)/2) = 1.19935…` is therefore a root of the matching polynomial, exactly.
`degree_A3` confirms the bookkeeping.

The spectral half, that `θ` lies in an internal gap of `spec(T)`, is certified numerically in
`code/subcubic.py`: a real Angel–Friedman–Hoory ratio system on all `76` directed edges with
residual `5·10⁻⁴¹` at `40` digits and decay rate `ρ = 0.99273509760803 < 1`.  That theorem is
not in Mathlib and is not formalized here; as in `HallCounterexample` it is the single
classical input.
-/

namespace SubcubicCounterexample

open Polynomial

/-! ## The rooted pair recursion -/

/-- A triangle rooted at one of its vertices: `(μ_{C₃}, μ_{P₂})`. -/
noncomputable def A0 : ℤ[X] := X ^ 3 - 3 * X
noncomputable def B0 : ℤ[X] := X ^ 2 - 1

/-- One level of the binary skeleton: a new vertex joined to the roots of two copies. -/
noncomputable def A1 : ℤ[X] := X * A0 ^ 2 - 2 * B0 * A0
noncomputable def B1 : ℤ[X] := A0 ^ 2

noncomputable def A2 : ℤ[X] := X * A1 ^ 2 - 2 * B1 * A1
noncomputable def B2 : ℤ[X] := A1 ^ 2

/-- The whole graph: depth three, so `μ_G = A3`. -/
noncomputable def A3 : ℤ[X] := X * A2 ^ 2 - 2 * B2 * A2

/-! ## Where the quartic comes from -/

/-- **The crux.**  At depth two the recursion factors, and the quartic appears. -/
theorem quartic_factor :
    X * A1 - 2 * B1 = X ^ 2 * (X ^ 2 - 3) * (X ^ 4 - 7 * X ^ 2 + 8) := by
  simp only [A1, B1, A0, B0]; ring

/-- `A2` is `A1` times that, so the quartic divides it. -/
theorem A2_eq : A2 = A1 * (X ^ 2 * (X ^ 2 - 3) * (X ^ 4 - 7 * X ^ 2 + 8)) := by
  rw [A2, ← quartic_factor]; ring

theorem quartic_dvd_A2 : (X ^ 4 - 7 * X ^ 2 + 8 : ℤ[X]) ∣ A2 :=
  ⟨A1 * (X ^ 2 * (X ^ 2 - 3)), by rw [A2_eq]; ring⟩

/-- Hence it divides the matching polynomial of the whole graph. -/
theorem quartic_dvd_A3 : (X ^ 4 - 7 * X ^ 2 + 8 : ℤ[X]) ∣ A3 := by
  obtain ⟨c, hc⟩ := quartic_dvd_A2
  exact ⟨X * A2 * c - 2 * B2 * c, by rw [A3, hc]; ring⟩

/-- The degree is `31`, matching the vertex count. -/
theorem degree_A3 : A3.natDegree = 31 := by
  have : A3 = X ^ 31 - 38 * X ^ 29 + 644 * X ^ 27 - 6424 * X ^ 25 + 41910 * X ^ 23
      - 187852 * X ^ 21 + 591116 * X ^ 19 - 1310272 * X ^ 17 + 2021345 * X ^ 15
      - 2109374 * X ^ 13 + 1418280 * X ^ 11 - 569592 * X ^ 9 + 121392 * X ^ 7
      - 10368 * X ^ 5 := by
    simp only [A3, A2, B2, A1, B1, A0, B0]; ring
  rw [this]
  compute_degree!

/-! ## The root -/

/-- The quartic vanishes at `θ` whenever `θ² = (7 - √17)/2`, and that value is positive, so
such a real `θ` exists.  `θ = 1.19935…`. -/
theorem quartic_root {θ : ℝ} (h : θ ^ 2 = (7 - Real.sqrt 17) / 2) :
    aeval θ (X ^ 4 - 7 * X ^ 2 + 8 : ℤ[X]) = 0 := by
  have h17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h4 : θ ^ 4 = (θ ^ 2) ^ 2 := by ring
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
  rw [h4, h]
  field_simp
  nlinarith [h17]

/-- **The matching polynomial vanishes at `θ`.**  With the spectral exclusion of
`code/subcubic.py`, this refutes Conjecture 10 for graphs of minimum degree two and for
graphs of bounded maximum degree simultaneously. -/
theorem A3_root {θ : ℝ} (h : θ ^ 2 = (7 - Real.sqrt 17) / 2) : aeval θ A3 = 0 := by
  obtain ⟨c, hc⟩ := quartic_dvd_A3
  rw [hc, map_mul, quartic_root h, zero_mul]

/-- `θ` is real and positive: `(7 - √17)/2 > 0` since `√17 < 7`. -/
theorem theta_exists : ∃ θ : ℝ, 0 < θ ∧ θ ^ 2 = (7 - Real.sqrt 17) / 2 := by
  have h17 : Real.sqrt 17 < 7 := by
    have : Real.sqrt 17 < Real.sqrt 49 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq] using this
  refine ⟨Real.sqrt ((7 - Real.sqrt 17) / 2), Real.sqrt_pos.mpr (by linarith), ?_⟩
  exact Real.sq_sqrt (by linarith)

end SubcubicCounterexample
