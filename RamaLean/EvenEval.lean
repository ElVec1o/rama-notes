import Mathlib
import RamaLean.Interlacing

/-!
# `μ_G(2√(d-1))` is a positive integer when `|V(G)|` is even

Péter Csikvári asks (personal communication, August 2026) whether `μ_G(2√(d-1))` has a
combinatorial meaning for a `d`-regular graph `G` with an even number of vertices, noting
in passing that it should at least be a positive integer.

**We have nothing on the combinatorial meaning.**  The evaluation point in the rest of this
development is `2√a` with `a` the degree, which sits strictly outside the Heilmann–Lieb
support; his point `2√(d-1)` is the support's edge, a different and harder place.  Nothing
in `MomentTransfer` or `KestenMcKay` bears on it.

The parenthetical is elementary, and this file settles it.

* **Integer.**  `μ_G(x) = ∑_k (-1)^k m_k x^{n-2k}` with `m_k` the matching counts.  When `n`
  is even every exponent `n - 2k` is even, so `μ_G` is a polynomial in `x²` with integer
  coefficients.  At `x = 2√(d-1)` we have `x² = 4(d-1) ∈ ℤ`, so the value is an integer.
  That is `eval_int`.
* **Positive.**  Heilmann–Lieb puts every root of `μ_G` in `[-2√(d-1), 2√(d-1)]`, and the
  bound is not attained on a finite graph, so `2√(d-1)` lies above every root.  A monic
  polynomial is positive above its largest root.  That is `pos_of_all_below`, which is
  `Interlacing.ev_sign` at count zero.

The parity hypothesis is not decorative: for odd `n` every exponent `n - 2k` is odd, the
value is `√(4(d-1))` times an integer, and it is an integer only when `d - 1` is a perfect
square.  `eval_odd_factors` records the obstruction.
-/

namespace EvenEval

open Finset Interlacing

/-! ## Integrality -/

/-- An even power of `x` is a power of `x²`. -/
theorem even_pow (x : ℝ) {m : ℕ} (hm : Even m) : x ^ m = (x ^ 2) ^ (m / 2) := by
  obtain ⟨j, hj⟩ := hm
  have hmj : m = 2 * j := by omega
  rw [hmj, pow_mul]
  congr 1
  omega

/-- **The value is an integer.**  A polynomial supported in even degrees, with integer
coefficients, takes an integer value wherever `x²` is an integer.  For `μ_G` with `|V(G)|`
even the support condition holds, and at `x = 2√(d-1)` we have `x² = 4(d-1)`. -/
theorem eval_int {n K : ℕ} (hn : Even n) (c : ℕ → ℤ) (N : ℤ) {x : ℝ}
    (hx : x ^ 2 = (N : ℝ)) :
    (∑ k ∈ range (K + 1), (c k : ℝ) * x ^ (n - 2 * k))
      = ((∑ k ∈ range (K + 1), c k * N ^ ((n - 2 * k) / 2) : ℤ) : ℝ) := by
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hev : Even (n - 2 * k) := by
    obtain ⟨j, hj⟩ := hn
    exact ⟨j - k, by omega⟩
  rw [even_pow x hev, hx]

/-- At the point Csikvári asks about, `x² = 4(d-1)`. -/
theorem sq_at_edge {d : ℝ} (hd : 1 ≤ d) : (2 * Real.sqrt (d - 1)) ^ 2 = 4 * (d - 1) := by
  have h : Real.sqrt (d - 1) ^ 2 = d - 1 := Real.sq_sqrt (by linarith)
  nlinarith [h]

/-! ## Positivity -/

/-- **A monic polynomial is positive above its largest root.**  This is `ev_sign` at count
zero, and it applies at `2√(d-1)` because Heilmann–Lieb does not attain its bound on a
finite graph. -/
theorem pos_of_all_below (R : Multiset ℝ) {x : ℝ} (h : ∀ t ∈ R, t < x) : 0 < ev R x := by
  classical
  have hx : x ∉ R := fun hm => lt_irrefl x (h x hm)
  have hcount : GapLabel.countAbove R x = 0 := by
    rw [GapLabel.countAbove, Multiset.countP_eq_zero]
    exact fun t ht => not_lt.mpr (h t ht).le
  have := ev_sign R hx
  rwa [hcount, pow_zero, one_mul] at this

/-! ## The answer to the parenthetical -/

/-- **`μ_G(2√(d-1))` is a positive integer when `|V(G)|` is even.**

`R` is the root multiset of `μ_G`, `c` its coefficient sequence in the even-degree
expansion, and the hypotheses are: the roots lie strictly below the evaluation point
(Heilmann–Lieb, strict on a finite graph), the vertex count is even, and the coefficients
are integers.  The conclusion is that the value is a strictly positive integer. -/
theorem eval_pos_int {n K : ℕ} (hn : Even n) (c : ℕ → ℤ) (N : ℤ) (R : Multiset ℝ) {x : ℝ}
    (hx : x ^ 2 = (N : ℝ)) (hroots : ∀ t ∈ R, t < x)
    (hform : ev R x = ∑ k ∈ range (K + 1), (c k : ℝ) * x ^ (n - 2 * k)) :
    0 < (∑ k ∈ range (K + 1), c k * N ^ ((n - 2 * k) / 2) : ℤ) := by
  have hpos : 0 < ev R x := pos_of_all_below R hroots
  rw [hform, eval_int hn c N hx] at hpos
  exact_mod_cast hpos

/-! ## Why the parity hypothesis is needed -/

/-- **The obstruction for odd `n`.**  With `n` odd every exponent `n - 2k` is odd, so the
value is `x` times a polynomial in `x²` with integer coefficients.  At `x = 2√(d-1)` that
is `2√(d-1)` times an integer, which is an integer only when `d - 1` is a perfect square.
So Csikvári's parity hypothesis is exactly what makes the question well posed. -/
theorem eval_odd_factors {n K : ℕ} (hn : Odd n) (c : ℕ → ℤ) (N : ℤ) {x : ℝ}
    (hx : x ^ 2 = (N : ℝ)) (hK : ∀ k ∈ range (K + 1), 2 * k + 1 ≤ n) :
    (∑ k ∈ range (K + 1), (c k : ℝ) * x ^ (n - 2 * k))
      = x * ((∑ k ∈ range (K + 1), c k * N ^ ((n - 1 - 2 * k) / 2) : ℤ) : ℝ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hbound := hK k hk
  have hev : Even (n - 1 - 2 * k) := by
    obtain ⟨j, hj⟩ := hn
    exact ⟨j - k, by omega⟩
  have hsplit : n - 2 * k = (n - 1 - 2 * k) + 1 := by omega
  rw [hsplit, pow_succ, even_pow x hev, hx]
  ring

end EvenEval
