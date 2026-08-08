import Mathlib
import RamaLean.InertiaSplit

/-!
# The shell estimate

G37 is the target that would close the two-vertex case: the wrong-parity class contributes
an integral bounded by a constant times the square of its measure, while the right-parity
class is bounded below.  Measurement across two whole gaps
(`code/margin_scan.py`) puts the ratio `I_wrong / m_wrong²` between `2.4` and `5.2`, with no
blow-up at the gap edges, where the wrong class is largest and the ratio is smallest.

This file proves the upper half's chain, and says plainly which link is missing.

## Why the exponent is two

The wrong-parity region is bounded by the crossing locus `{z : det S(x,z) = 0}`, so every
point of it lies within its own diameter of a point where an eigenvalue vanishes.  Three
steps then give the square.

1. **The determinant is the norm times the smaller eigenvalue, exactly.**  For a `2 × 2`
   Hermitian matrix with eigenvalues `λ₁, λ₂`, `|det| = |λ₁||λ₂|` and the operator norm is
   `max(|λ₁|,|λ₂|)`, so `|det| = ‖S‖ · min(|λ₁|,|λ₂|)`.  That is `abs_mul_eq_max_mul_min`,
   an identity rather than an estimate, and it is what makes the crossing eigenvalue the
   only thing that matters.
2. **The crossing eigenvalue is Lipschitz in the parameter.**  Weyl's inequality gives
   `|λ(z) - λ(w)| ≤ ‖S(z) - S(w)‖`, and `S` depends smoothly on the phases, so
   `|λ_min(z)| ≤ L · dist(z, ∂)` with `∂` the crossing locus.
3. **Integrating over the region.**  `∫_A |det S| ≤ m(A) · sup_A |det S| ≤ m(A) · M · L ·
   reach(A)`, where `reach(A) = sup_{z ∈ A} dist(z, ∂A)` is the **inradius**.  The square
   appears exactly when `reach(A) ≲ m(A)`.

The relevant quantity is the inradius and emphatically **not** the diameter.  A shell that
wraps around the torus has diameter of order one however thin it is, so `diam ≲ m` is simply
false here; what is small is the distance from a point of the shell to its own boundary.

## The link is not missing: it is free

An earlier version of this file conjectured `reach ≲ m`, on the picture that the
wrong-parity region is a thin shell.  **That is false.**  Measurement
(`code/shell_geometry.py`) gives `reach/m` running `2.60, 3.10, 4.63, 5.94, 9.80` as `m`
falls from `0.052` to `0.0053`: the ratio diverges, because the region is a blob and not a
wrapping shell, with `m` of order `reach²`.

The correct bound needs no hypothesis at all.  A region of inradius `r` contains a ball of
radius `r`, so its measure is at least `c_b r^b`, giving

  `reach ≤ (m / c_b)^{1/b}`   unconditionally,

and hence `I_wrong ≤ M · L · c_b^{-1/b} · m^{1 + 1/b}`.  At `b = 2` that is `m^{3/2}`, which
is weaker than the `m²` the numerics suggest but stronger than anything needed: all that
domination requires is a bound tending to zero faster than `I_right` does.  So the upper
half of `G37` is **unconditional**, and the conjecture it was waiting on was both false and
unnecessary.

The lower half, a bound `I_right ≥ c > 0`, is **not** addressed here and is not obviously
available: the natural route, pushing invertibility of `S(x)` down to every phase, is
exactly what `NoQuotient` rules out.
-/

namespace ShellBound

/-! ## The determinant identity -/

/-- **The determinant of a `2 × 2` Hermitian matrix is its norm times its smaller
eigenvalue in absolute value.**  An identity, which is why the crossing eigenvalue controls
everything on the shell. -/
theorem abs_mul_eq_max_mul_min (a b : ℝ) : |a * b| = max |a| |b| * min |a| |b| := by
  rw [abs_mul]
  rcases le_total |a| |b| with h | h
  · rw [max_eq_right h, min_eq_left h, mul_comm]
  · rw [max_eq_left h, min_eq_right h]

/-- The consequence used below: the determinant is at most the norm times the smaller
eigenvalue. -/
theorem abs_det_le {a b M : ℝ} (hM : max |a| |b| ≤ M) : |a * b| ≤ M * min |a| |b| := by
  rw [abs_mul_eq_max_mul_min]
  exact mul_le_mul_of_nonneg_right hM (le_min (abs_nonneg a) (abs_nonneg b))

/-! ## The pointwise bound on the shell -/

/-- **Pointwise on the shell.**  With the norm bounded by `M`, the smaller eigenvalue
Lipschitz with constant `L` in the distance to the crossing locus, and that distance at
most `D`, the determinant is at most `M · L · D`.  `D` is a bound on the distance to the
crossing locus, so the quantity to substitute is the inradius, not the diameter. -/
theorem det_le_on_shell {a b M L D d : ℝ} (hM : max |a| |b| ≤ M) (hM0 : 0 ≤ M)
    (hlip : min |a| |b| ≤ L * d) (hL : 0 ≤ L) (hd : d ≤ D) :
    |a * b| ≤ M * (L * D) := by
  have h1 : |a * b| ≤ M * min |a| |b| := abs_det_le hM
  have h2 : M * min |a| |b| ≤ M * (L * d) := mul_le_mul_of_nonneg_left hlip hM0
  have h3 : M * (L * d) ≤ M * (L * D) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hL) hM0
  linarith

/-! ## Integrating, and where the square comes from -/

/-- **The inradius is bounded by the measure, for free.**  A region of inradius `r` contains
a ball of radius `r`, so `c r^b ≤ m`.  At `b = 2` this reads `c r² ≤ m`, hence
`r ≤ √(m/c)`. -/
theorem reach_le_sqrt {r m c : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hball : c * r ^ 2 ≤ m) :
    r ≤ Real.sqrt (m / c) := by
  have hm : r ^ 2 ≤ m / c := by rw [le_div_iff₀ hc]; linarith
  calc r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hr).symm
    _ ≤ Real.sqrt (m / c) := Real.sqrt_le_sqrt hm

/-- **The upper half, unconditionally.**  Combining the pointwise bound with the free
inradius bound gives `I ≤ M · L · √(m/c) · m`, an exponent of `3/2` in the measure at
`b = 2`.  No shell hypothesis appears: the earlier `G38` was false and is not needed. -/
theorem integral_le_three_halves {I m r c M L : ℝ}
    (hm : 0 ≤ m) (hM : 0 ≤ M) (hL : 0 ≤ L) (hc : 0 < c) (hr : 0 ≤ r)
    (hball : c * r ^ 2 ≤ m) (hint : I ≤ m * (M * (L * r))) :
    I ≤ M * L * Real.sqrt (m / c) * m := by
  have hrb := reach_le_sqrt hc hr hball
  have h1 : M * (L * r) ≤ M * (L * Real.sqrt (m / c)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrb hL) hM
  calc I ≤ m * (M * (L * r)) := hint
    _ ≤ m * (M * (L * Real.sqrt (m / c))) := mul_le_mul_of_nonneg_left h1 hm
    _ = M * L * Real.sqrt (m / c) * m := by ring

/-- **The square, from a shell hypothesis, retained only for comparison.**  This is the
statement the earlier version aimed at.  Its hypothesis is false for the region at hand, and
`integral_le_three_halves` supersedes it. -/
theorem quadratic_of_shell {I m c M L : ℝ}
    (hm : 0 ≤ m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hshell : ∀ D, D ≤ c * m → I ≤ m * (M * (L * D)))
    (hdiam : ∃ D, D ≤ c * m ∧ True) :
    I ≤ M * L * c * m ^ 2 := by
  obtain ⟨D, hD, -⟩ := hdiam
  have h := hshell D hD
  have : m * (M * (L * D)) ≤ m * (M * (L * (c * m))) := by
    have hLD : L * D ≤ L * (c * m) := mul_le_mul_of_nonneg_left hD hL
    have := mul_le_mul_of_nonneg_left hLD hM
    exact mul_le_mul_of_nonneg_left this hm
  calc I ≤ m * (M * (L * D)) := h
    _ ≤ m * (M * (L * (c * m))) := this
    _ = M * L * c * m ^ 2 := by ring

/-! ## What it would give -/

/-- **Closing the two-vertex case, granted both halves.**  With the wrong-parity integral
bounded quadratically and the right-parity integral bounded below by more than that, the
domination criterion of `InertiaSplit` is met.  Both hypotheses are open: the first is
`G38`, the second is not addressed. -/
theorem domination_of_shell {Iw Ir m c M L : ℝ}
    (hupper : Iw ≤ M * L * c * m ^ 2) (hlower : M * L * c * m ^ 2 < Ir) :
    Iw < Ir :=
  lt_of_le_of_lt hupper hlower

end ShellBound
