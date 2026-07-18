/-
# Paper 2 — Expected characteristic polynomial of random permutation lifts of cycle graphs

Lean 4 / Mathlib formalization of the verifiable content of
`proof2_cycle_graph_lift.md`.

**Theorem 1** (`paper2`).  For `n ≥ 2`, `r ≥ 1`,
        Φ_{C_n,r}(x) = U_r(Y) − 2·U_{r−1}(Y) + U_{r−2}(Y),     Y = T_n(x/2),
with `T, U` the Chebyshev polynomials of the first/second kind and `U₋₁ = 0`.

**The general derivation (all `n`, `r`) is in `RamaLean/Paper2General.lean`**,
which re-derives the paper's Steps 3–5 (cycle index → Chebyshev closed form) as
genuine theorems over any characteristic-zero domain — see `Paper2.thm1_general`.
This file complements it with concrete, kernel-checked computations over the
paper's tested range (which also cross-check the one classical input cited in
the general file, the exponential formula, on small cases):

* `thm1_verified` — a **kernel-checked** (`native_decide`) verification of the
  closed form against the *direct cycle-index computation* for every
  `n ∈ {2,…,6}`, `r ∈ {1,…,6}` (the exact range `paper2` checked with SymPy,
  reproduced here with a self-contained computable polynomial layer).
* `cor1_numerator` — the **general** trigonometric identity at the heart of
  Corollary 1 (real-rootedness): the numerator of `Φ` in sine form factors,
  exhibiting all roots in `[−2, 2]`.
* `cor2_reduction` — the **general** algebraic reduction underlying Corollary 2,
  together with `cor2_fibLucas` / `cor2_phi3`, the Fibonacci–Lucas evaluation
  `Φ_{C_n,r}(3) = (L(2n) − 2)·F(2nr)/F(2n)` verified over `paper2`'s range.

No `sorry`, no custom mathematical axioms (trust base: the standard
`propext / Classical.choice / Quot.sound` plus the `native_decide` compiler
axiom for the computational lemmas).
-/
import Mathlib

namespace Paper2

/-! ## A self-contained computable polynomial layer (coefficients low → high) -/

/-- A polynomial as its list of rational coefficients, constant term first. -/
abbrev Poly := List ℚ

/-- Coefficientwise addition. -/
def padd : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Scalar multiplication. -/
def psmul (c : ℚ) (p : Poly) : Poly := p.map (c * ·)

/-- Polynomial multiplication (`0 :: p` is multiplication by `x`). -/
def pmul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd (psmul a q) (0 :: pmul p q)

/-- Subtraction. -/
def psub (p q : Poly) : Poly := padd p (psmul (-1) q)

/-- Drop trailing zeros so that equal polynomials have equal representations. -/
def pnorm (p : Poly) : Poly := (p.reverse.dropWhile (· == 0)).reverse

/-- `Tc k = Tₖ(x/2)`, the `k`-th Chebyshev polynomial of the first kind in the
gauge `Y = Tₙ(x/2)`. Recurrence `T_{k+2}(x/2) = x·T_{k+1}(x/2) − T_k(x/2)`. -/
def Tc : ℕ → Poly
  | 0 => [1]
  | 1 => [0, 1/2]
  | (k + 2) => psub (0 :: Tc (k + 1)) (Tc k)

/-- `Uc Y r = U_r(Y)`, the `r`-th Chebyshev polynomial of the second kind
evaluated at the polynomial `Y`. Recurrence `U_{r+1} = 2Y·U_r − U_{r−1}`. -/
def Uc (Y : Poly) : ℕ → Poly
  | 0 => [1]
  | 1 => psmul 2 Y
  | (k + 2) => psub (pmul (psmul 2 Y) (Uc Y (k + 1))) (Uc Y k)

/-- `f(ℓ) = 2·T_{nℓ}(x/2) − 2`, the per-cycle contribution from `proof2` Step 2. -/
def fj (n j : ℕ) : Poly := psub (psmul 2 (Tc (n * j))) [2]

/-- Integer partitions of `r` (each as a non-increasing list of parts), for the
range `1 ≤ r ≤ 6` used in the verification. -/
def partsOf : ℕ → List (List ℕ)
  | 1 => [[1]]
  | 2 => [[2], [1, 1]]
  | 3 => [[3], [2, 1], [1, 1, 1]]
  | 4 => [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]]
  | 5 => [[5], [4, 1], [3, 2], [3, 1, 1], [2, 2, 1], [2, 1, 1, 1], [1, 1, 1, 1, 1]]
  | 6 => [[6], [5, 1], [4, 2], [4, 1, 1], [3, 3], [3, 2, 1], [3, 1, 1, 1],
          [2, 2, 2], [2, 2, 1, 1], [2, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]]
  | _ => []

/-- `z_λ = ∏ j^{m_j} · m_j!`, the order of the centralizer of a permutation of
cycle type `λ` in `Sᵣ`. -/
def zlam (parts : List ℕ) : ℚ :=
  (parts.dedup).foldl
    (fun acc k => acc * (k : ℚ) ^ (parts.count k) * (Nat.factorial (parts.count k) : ℚ)) 1

/-- Direct cycle-index computation of the expected characteristic polynomial:
`Σ_{λ ⊢ r} (1/z_λ) ∏_{j ∈ λ} f(j)`. -/
def directPhi (n r : ℕ) : Poly :=
  (partsOf r).foldl
    (fun acc lam =>
      let prodf := lam.foldl (fun pp k => pmul pp (fj n k)) [1]
      padd acc (psmul (1 / zlam lam) prodf)) []

/-- Closed-form side: `U_r(Y) − 2·U_{r−1}(Y) + U_{r−2}(Y)` with `Y = Tₙ(x/2)`
and `U₋₁ = 0`. -/
def formulaPhi (n r : ℕ) : Poly :=
  let Y := Tc n
  match r with
  | 0 => [1]
  | 1 => psub (Uc Y 1) (psmul 2 (Uc Y 0))                            -- U₁ − 2U₀  (U₋₁ = 0)
  | (k + 2) => psub (padd (Uc Y (k + 2)) (Uc Y k)) (psmul 2 (Uc Y (k + 1)))

/-- **Theorem 1, verified.** For every `n ∈ {2,…,6}` and `r ∈ {1,…,6}`, the
closed form equals the direct cycle-index expected characteristic polynomial.
This reproduces `paper2`'s "30/30 matches" (the full 5×6 grid) inside the Lean
kernel. -/
theorem thm1_verified :
    ∀ n ∈ [2, 3, 4, 5, 6], ∀ r ∈ [1, 2, 3, 4, 5, 6],
      pnorm (directPhi n r) = pnorm (formulaPhi n r) := by
  native_decide

/-! ## Corollary 1 — real-rootedness (the trigonometric core)

With `x = 2cos θ` and `Y = Tₙ(cos θ) = cos(nθ)`, writing `Uₖ(cos φ) =
sin((k+1)φ)/sin φ`, the numerator of `Φ` in the sine form is
`sin((r+1)φ) − 2sin(rφ) + sin((r−1)φ)` with `φ = nθ`.  We prove it factors;
the factorization `2 sin(rφ)(cos φ − 1) = −4 sin(rφ) sin²(φ/2)` shows every root
occurs where `sin(rφ) = 0` or `sin(φ/2) = 0`, i.e. at `x = 2cos θ ∈ [−2, 2]`. -/

/-- The numerator identity (with `a = rφ`): `sin(a+φ) − 2 sin a + sin(a−φ) =
2 sin a (cos φ − 1)`. -/
theorem cor1_numerator (a φ : ℝ) :
    Real.sin (a + φ) - 2 * Real.sin a + Real.sin (a - φ)
      = 2 * Real.sin a * (Real.cos φ - 1) := by
  rw [Real.sin_add, Real.sin_sub]; ring

/-- The fully factored form, exhibiting the roots: `sin(a+φ) − 2 sin a +
sin(a−φ) = −4 sin a · sin²(φ/2)`. -/
theorem cor1_factored (a φ : ℝ) :
    Real.sin (a + φ) - 2 * Real.sin a + Real.sin (a - φ)
      = -4 * Real.sin a * (Real.sin (φ / 2)) ^ 2 := by
  rw [cor1_numerator]
  have h : Real.cos φ = 1 - 2 * (Real.sin (φ / 2)) ^ 2 := by
    have e : Real.cos (2 * (φ / 2)) = 2 * Real.cos (φ / 2) ^ 2 - 1 := Real.cos_two_mul _
    rw [show (2 : ℝ) * (φ / 2) = φ by ring] at e
    nlinarith [e, Real.sin_sq_add_cos_sq (φ / 2)]
  rw [h]; ring

/-! ## Corollary 2 — Fibonacci–Lucas evaluation at `x = 3`

`Φ_{C_n,r}(3) = (L(2n) − 2)·F(2nr)/F(2n)`, where `F`, `L` are the Fibonacci and
Lucas numbers.  At `x = 3`, `Y = Tₙ(3/2) = L(2n)/2`, so `Uₖ(Y)` is the integer
sequence `u` below with `t = 2Y = L(2n)`. -/

/-- Lucas numbers `L(0)=2, L(1)=1, L(k+2)=L(k)+L(k+1)`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (k + 2) => lucas k + lucas (k + 1)

/-- `u r = U_r(Y)` for `Y = t/2`: `u 0 = 1, u 1 = t, u_{r+2} = t·u_{r+1} − u_r`. -/
def useq (t : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => t
  | (k + 2) => t * useq t (k + 1) - useq t k

/-- **General reduction** (any `t`, any `r`): the three-term combination
`u_{r} − 2u_{r−1} + u_{r−2}` collapses to `(t − 2)·u_{r−1}`.  This is the
algebraic step turning `U_r − 2U_{r−1} + U_{r−2}` into `(L(2n) − 2)·U_{r−1}`. -/
theorem cor2_reduction (t : ℤ) (k : ℕ) :
    useq t (k + 2) - 2 * useq t (k + 1) + useq t k = (t - 2) * useq t (k + 1) := by
  show t * useq t (k + 1) - useq t k - 2 * useq t (k + 1) + useq t k = _
  ring

/-- **Fibonacci–Lucas evaluation** `u_k = F(2n(k+1))/F(2n)` (cleared of
division: `F(2n)·u_k = F(2n(k+1))`), verified for `n ∈ {2,…,6}`, `k ∈ {0,…,5}`.
Here `t = L(2n) = lucas (2n)`. -/
theorem cor2_fibLucas :
    ∀ n ∈ [2, 3, 4, 5, 6], ∀ k ∈ [0, 1, 2, 3, 4, 5],
      (Nat.fib (2 * n) : ℤ) * useq (lucas (2 * n)) k = (Nat.fib (2 * n * (k + 1)) : ℤ) := by
  native_decide

/-- `Φ_{C_n,r}(3)` from the closed form, as an integer (`U₋₁ = 0`). -/
def Phi3 (n r : ℕ) : ℤ :=
  let t := lucas (2 * n)
  match r with
  | 0 => 1
  | 1 => useq t 1 - 2 * useq t 0                                  -- = t − 2
  | (k + 2) => useq t (k + 2) - 2 * useq t (k + 1) + useq t k

/-- **Corollary 2, verified.** `F(2n)·Φ_{C_n,r}(3) = (L(2n) − 2)·F(2nr)` for
`n ∈ {2,…,6}`, `r ∈ {1,…,6}` — i.e. `Φ_{C_n,r}(3) = (L(2n) − 2)·F(2nr)/F(2n)`.
Reproduces `paper2`'s "30/30 matches". -/
theorem cor2_phi3 :
    ∀ n ∈ [2, 3, 4, 5, 6], ∀ r ∈ [1, 2, 3, 4, 5, 6],
      (Nat.fib (2 * n) : ℤ) * Phi3 n r = (lucas (2 * n) - 2) * (Nat.fib (2 * n * r) : ℤ) := by
  native_decide

/-- Special case `n = 3`: `Φ_{C_3,r}(3) = 2·F(6r)` (since `L(6) − 2 = 16`,
`F(6) = 8`). -/
theorem cor2_n3 :
    ∀ r ∈ [1, 2, 3, 4, 5, 6], Phi3 3 r = 2 * (Nat.fib (6 * r) : ℤ) := by
  native_decide

end Paper2
