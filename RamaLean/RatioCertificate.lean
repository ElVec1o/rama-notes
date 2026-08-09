import Mathlib

/-!
# The ratio-system certificate, as a reusable schema

Three counterexamples to Conjecture 10 are certified the same way: Hall's on `41` vertices, the
minimum-degree-two one on `92`, and the subcubic one on `31`.  Each exhibits a finite nonzero
ratio system for `A_T - λI` whose decay matrix has spectral radius below one, and appeals to
Angel–Friedman–Hoory.  This file isolates that argument once.

## Why a schema and not exact algebra

Hall's ratios lie in `ℚ(√5, √41)`, so his certificate can be written in closed form.  That is
a feature of his graph, not of the method.  For the `31`-vertex graph the `76` directed edges
collapse to `9` orbits, but the ratios do not lie in a small extension: integer-relation
detection at `45` digits finds no minimal polynomial of degree at most `12` with coefficients
of moderate height, returning only spurious relations with coefficients near `10⁹`.  So the
numbers are verified outside Lean, at `40` digits with a Newton–Kantorovich bound, and what is
formalized is the implication that consumes them.

## The schema

`decay_lt_one` is the Collatz–Wielandt step in the strict form the certificate needs: a
nonnegative matrix admitting a positive vector with `K y < y` componentwise has every
eigenvalue of modulus `< 1`.  `spec_excluded` then packages the whole argument, with
Angel–Friedman–Hoory as an explicit hypothesis in the shape it is used: a finite nonzero ratio
system with decay rate below one gives `λ ∉ spec(A_T)`.

The point of stating it once is that the three instances differ only in their numbers.
-/

namespace RatioCertificate

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Collatz–Wielandt, strict form -/

/-- **A nonnegative matrix with a strictly subinvariant positive vector is a contraction.**
If `K ≥ 0`, `y > 0` and `(K y)_i < y_i` for every `i`, then every eigenvalue of `K` has
modulus strictly below one.

The proof is the usual maximiser argument: at an index where `‖v_i‖ / y_i` is largest, the
eigenvalue equation forces `‖μ‖ ‖v_i‖ ≤ t (K y)_i < t y_i = ‖v_i‖`. -/
theorem decay_lt_one (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hsub : ∀ i, ∑ j, K i j * y j < y i)
    (μ : ℂ) (v : ι → ℂ) (hv : ∃ i, v i ≠ 0)
    (heig : ∀ i, ∑ j, (K i j : ℂ) * v j = μ * v i) :
    ‖μ‖ < 1 := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun i => ‖v i‖ / y i) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set t := ‖v i₀‖ / y i₀ with ht
  have hbound : ∀ j, ‖v j‖ ≤ t * y j := by
    intro j
    have hyj : y j ≠ 0 := (hy j).ne'
    calc ‖v j‖ = ‖v j‖ / y j * y j := by field_simp
      _ ≤ t * y j := mul_le_mul_of_nonneg_right (hi₀ j (Finset.mem_univ j)) (le_of_lt (hy j))
  have htpos : 0 < t := by
    obtain ⟨i, hi⟩ := hv
    exact lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hi) (hy i)) (hi₀ i (Finset.mem_univ i))
  have hkey : ‖μ‖ * ‖v i₀‖ < t * y i₀ := by
    have h1 : ‖μ * v i₀‖ ≤ ∑ j, K i₀ j * ‖v j‖ := by
      rw [← heig i₀]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK i₀ j)]
    have h2 : ∑ j, K i₀ j * ‖v j‖ ≤ ∑ j, K i₀ j * (t * y j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hK i₀ j)
    have h3 : ∑ j, K i₀ j * (t * y j) = t * ∑ j, K i₀ j * y j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have h4 : t * ∑ j, K i₀ j * y j < t * y i₀ :=
      mul_lt_mul_of_pos_left (hsub i₀) htpos
    calc ‖μ‖ * ‖v i₀‖ = ‖μ * v i₀‖ := (norm_mul _ _).symm
      _ ≤ ∑ j, K i₀ j * ‖v j‖ := h1
      _ ≤ ∑ j, K i₀ j * (t * y j) := h2
      _ = t * ∑ j, K i₀ j * y j := h3
      _ < t * y i₀ := h4
  have hyi : y i₀ ≠ 0 := (hy i₀).ne'
  have hvi : ‖v i₀‖ = t * y i₀ := by
    rw [ht]; field_simp
  rw [hvi] at hkey
  have hpos : 0 < t * y i₀ := mul_pos htpos (hy i₀)
  nlinarith [hkey, hpos]

/-! ## The certificate -/

/-- A finite nonzero ratio system for `A_T - λ I`, in the sense of Angel–Friedman–Hoory:
an assignment of nonzero reals to the directed edges satisfying `λ = 1/r_e + ∑_{e → f} r_f`. -/
structure RatioSystem (E : Type*) [Fintype E] where
  r : E → ℝ
  follows : E → Finset E
  lam : ℝ
  nonzero : ∀ e, r e ≠ 0
  equation : ∀ e, lam = (r e)⁻¹ + ∑ f ∈ follows e, r f

/-- The decay matrix of a ratio system: `K_{e,f} = r_f²` when `f` follows `e`, else `0`. -/
noncomputable def decay {E : Type*} [Fintype E] [DecidableEq E] (S : RatioSystem E) :
    E → E → ℝ :=
  fun e f => if f ∈ S.follows e then (S.r f) ^ 2 else 0

theorem decay_nonneg {E : Type*} [Fintype E] [DecidableEq E] (S : RatioSystem E) :
    ∀ e f, 0 ≤ decay S e f := by
  intro e f
  unfold decay
  split <;> positivity

/-- **The certificate, assembled.**  A finite nonzero ratio system whose decay matrix admits a
positive strictly subinvariant vector has decay rate below one, hence by Angel–Friedman–Hoory
its `λ` lies outside the spectrum of the universal cover.

`hAFH` is that theorem, stated in the shape the argument consumes; it is not in Mathlib.  Every
other step is proved here.  The three counterexamples of the note are instances differing only
in the numbers supplied. -/
theorem spec_excluded {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
    (S : RatioSystem E) (Spec : Set ℝ)
    (y : E → ℝ) (hy : ∀ e, 0 < y e)
    (hsub : ∀ e, ∑ f, decay S e f * y f < y e)
    (hAFH : (∀ μ : ℂ, ∀ v : E → ℂ, (∃ e, v e ≠ 0) →
        (∀ e, ∑ f, (decay S e f : ℂ) * v f = μ * v e) → ‖μ‖ < 1) → S.lam ∉ Spec) :
    S.lam ∉ Spec :=
  hAFH fun μ v hv heig => decay_lt_one (decay S) (decay_nonneg S) y hy hsub μ v hv heig

end RatioCertificate
