import Mathlib
import RamaLean.LaguerreBand

/-!
# Tree substitution: the two closure operations

Two operations under which the conjecture is inherited, both valid at every `d`.

## Theorem A, attaching a rooted tree at every vertex

With `α = μ_R`, `β = μ_{R-o}` and `N` the vertex count,

  `μ_{H∘R}(x) = β(x)^N · μ_H(α(x)/β(x))`,

because an uncovered vertex of `H` leaves its whole copy of `R` free (contributing `α`)
while a covered one leaves `R - o` (contributing `β`), so the matching sum is
`∑_M (-1)^{|M|} α^{N-2|M|} β^{2|M|}`.  That *is* `β^N μ_H(α/β)`: `homogenize` below.

The substituted variable is `α/β`, **not** `β/α`.  The same ratio is what the Schur
complement of the universal cover produces, since `x - b* (xI - A_{R-o})^{-1} b` equals
`det(xI - A_R)/det(xI - A_{R-o})`.  `star_ratio` pins the orientation on the standard
example `R = K_{1,t}`, where it must come out as `x - t/x`.

## Theorem B, subdividing a regular graph

For `H` a `D`-regular graph, `μ_{S(H)}(x) = x^{m-n} μ_H(x² - D)`, and the same identity
survives averaging over `r`-covers because suppressing the degree-two fibres of a cover of
`S(H)` gives a cover of `H`, uniformly (a product of independent uniform permutations is
uniform).  The consequence for roots is `subdivision_root`: a nonzero root `λ` has
`λ² - D` inside the Ramanujan interval of `H`, hence `|λ|` inside
`[√(D-1) - 1, √(D-1) + 1]`, which is exactly the band of the `(D,2)`-biregular tree.
That band is `LaguerreBand.band_endpoints` at `P = 2`, `Q = D`.

What is *not* here is the covering combinatorics: that an `r`-cover of `H∘R` is `H'∘R`
for an `r`-cover `H'` of `H`, and the corresponding statement for subdivisions.  Both are
the same kind of fibre bookkeeping as `CoverCounts`, and both remain by hand.
-/

namespace TreeSubstitution

open Finset

/-! ## Theorem A: the substitution is homogenization -/

/-- One term of the matching sum.  `β^N · c (α/β)^{N-2k} = c α^{N-2k} β^{2k}`. -/
theorem homogenize_term {α β : ℝ} (hβ : β ≠ 0) {N k : ℕ} (hk : 2 * k ≤ N) (c : ℝ) :
    β ^ N * (c * (α / β) ^ (N - 2 * k)) = c * α ^ (N - 2 * k) * β ^ (2 * k) := by
  have hsplit : β ^ N = β ^ (N - 2 * k) * β ^ (2 * k) := by
    rw [← pow_add]; congr 1; omega
  have hne : β ^ (N - 2 * k) ≠ 0 := pow_ne_zero _ hβ
  rw [div_pow, hsplit]
  field_simp

/-- **The substitution identity.**  Attaching `R` at every vertex sends the matching sum
of `H` to `β^N` times its value at `α/β`.  This is the polynomial content of Theorem A;
the coefficients `c k` are the matching counts `m_k(H)` with their signs. -/
theorem homogenize {α β : ℝ} (hβ : β ≠ 0) {N : ℕ} (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ k ∈ s, 2 * k ≤ N) :
    β ^ N * ∑ k ∈ s, c k * (α / β) ^ (N - 2 * k)
      = ∑ k ∈ s, c k * α ^ (N - 2 * k) * β ^ (2 * k) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => homogenize_term hβ (hs k hk) (c k)

/-- **The orientation check.**  For the star `R = K_{1,t}` rooted at its centre,
`μ_R = x^{t+1} - t x^{t-1}` and `μ_{R-o} = x^t`, so the substituted variable `α/β` is
`x - t/x`.  The reciprocal `β/α` is not. -/
theorem star_ratio {x : ℝ} (hx : x ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    (x ^ (t + 1) - t * x ^ (t - 1)) / x ^ t = x - t / x := by
  have h1 : x ^ t = x ^ (t - 1) * x := by rw [← pow_succ]; congr 1; omega
  have h2 : x ^ (t + 1) = x ^ (t - 1) * x ^ 2 := by rw [← pow_add]; congr 1; omega
  have hne : x ^ (t - 1) ≠ 0 := pow_ne_zero _ hx
  rw [h1, h2]
  field_simp

/-! ## Theorem B: root transfer through a subdivision -/

/-- **The `(D,2)`-biregular band.**  `(√(D-1) ± 1)² = D ± 2√(D-1)`.  This is
`LaguerreBand.band_endpoints` at `P = 2`, `Q = D`, and it is the band of the universal
cover of a subdivision. -/
theorem subdivision_band {D : ℝ} (hD : 1 ≤ D) :
    (Real.sqrt (D - 1) + 1) ^ 2 = D + 2 * Real.sqrt (D - 1)
      ∧ (Real.sqrt (D - 1) - 1) ^ 2 = D - 2 * Real.sqrt (D - 1) := by
  obtain ⟨hup, hlo⟩ := LaguerreBand.band_endpoints (P := 2) (Q := D) (by norm_num) hD
  have e1 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e1, Real.sqrt_one, one_mul] at hup hlo
  constructor
  · rw [hup]; ring
  · rw [hlo]; ring

/-- **Root transfer.**  If `λ` is a nonzero root of `μ_{r,S(H)}` then `θ = λ² - D` is a
root of `μ_{r,H}`, so Hall–Puder–Sawin puts `|θ| ≤ 2√(D-1)` and therefore `λ²` lands in
the squared band of the `(D,2)`-biregular tree. -/
theorem subdivision_root {D lam theta : ℝ} (hD : 1 ≤ D)
    (hrel : lam ^ 2 - D = theta) (hHL : |theta| ≤ 2 * Real.sqrt (D - 1)) :
    (Real.sqrt (D - 1) - 1) ^ 2 ≤ lam ^ 2
      ∧ lam ^ 2 ≤ (Real.sqrt (D - 1) + 1) ^ 2 := by
  obtain ⟨hup, hlo⟩ := subdivision_band hD
  rw [abs_le] at hHL
  constructor
  · rw [hlo]; linarith [hHL.1]
  · rw [hup]; linarith [hHL.2]

/-- The same conclusion as a bound on `|λ|` itself, which is the form the conjecture is
stated in: `|λ| ∈ [√(D-1) - 1, √(D-1) + 1]`. -/
theorem subdivision_abs {D lam theta : ℝ} (hD : 1 ≤ D)
    (hrel : lam ^ 2 - D = theta) (hHL : |theta| ≤ 2 * Real.sqrt (D - 1)) :
    Real.sqrt (D - 1) - 1 ≤ |lam| ∧ |lam| ≤ Real.sqrt (D - 1) + 1 := by
  obtain ⟨hlo, hup⟩ := subdivision_root hD hrel hHL
  have habs : |lam| ^ 2 = lam ^ 2 := sq_abs lam
  have hnn : (0:ℝ) ≤ |lam| := abs_nonneg lam
  have hsnn : (0:ℝ) ≤ Real.sqrt (D - 1) := Real.sqrt_nonneg _
  constructor
  · nlinarith [hlo, habs]
  · nlinarith [hup, habs]

end TreeSubstitution
