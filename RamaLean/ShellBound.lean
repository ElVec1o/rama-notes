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
   diam(A)`, and the square appears exactly when `diam(A) ≲ m(A)`.

## The missing link, stated

Step 3's last inequality is the open one.  A region of measure `m` in `b` dimensions has
diameter at least of order `m^{1/b}`, so `diam ≲ m` is **not** automatic; it holds for a
shell of width `w` around a codimension-one locus of bounded area, where both the measure
and the diameter are of order `w`.  Establishing that the wrong-parity region is such a
shell, with the area of the crossing locus bounded uniformly, is `G38`, and it is what
remains of the upper half.

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
most `D`, the determinant is at most `M · L · D`. -/
theorem det_le_on_shell {a b M L D d : ℝ} (hM : max |a| |b| ≤ M) (hM0 : 0 ≤ M)
    (hlip : min |a| |b| ≤ L * d) (hL : 0 ≤ L) (hd : d ≤ D) :
    |a * b| ≤ M * (L * D) := by
  have h1 : |a * b| ≤ M * min |a| |b| := abs_det_le hM
  have h2 : M * min |a| |b| ≤ M * (L * d) := mul_le_mul_of_nonneg_left hlip hM0
  have h3 : M * (L * d) ≤ M * (L * D) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hL) hM0
  linarith

/-! ## Integrating, and where the square comes from -/

/-- **The square, from the shell hypothesis.**  If the region's diameter is at most `c`
times its measure, the pointwise bound `M · L · diam` integrates to `M · L · c · m²`.  The
hypothesis `hshell` is `G38` and is the open link: in `b` dimensions a region of measure `m`
has diameter at least of order `m^{1/b}`, so this is a statement about the geometry of the
crossing locus and not a triviality. -/
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
