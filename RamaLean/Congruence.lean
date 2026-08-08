import Mathlib

/-!
# The Schur congruence, and what the inertia argument really needs

Audit of the operator-algebra steps this development leans on, after one of them
(`NoQuotient`) was found wrong.  The Haynsworth additivity used for
`κ(x) = N_F(x) + δ(x)` was justified by "Sylvester's law of inertia holds in a von Neumann
algebra with a trace", quoted from memory.  It does hold, but quoting it is not necessary
and not the cheapest route.  The step reduces to an **explicit congruence** together with a
connectedness argument, and the congruence is pure ring algebra.

For a self-adjoint block matrix with invertible corner `d`,

  `[[a, b], [c, d]] = [[1, b e], [0, 1]] · [[a - b e c, 0], [0, d]] · [[1, 0], [e c, 1]]`,

where `e` is the inverse of `d` and `a - b e c` is the Schur complement.  That is
`schur_factor` below, proved over an arbitrary ring.  The outer factors are unipotent, hence
invertible with explicit inverses (`unipotent_inv`), so the block matrix is congruent to the
direct sum of the corner and the Schur complement.

The inertia statement then follows from a homotopy rather than from Sylvester's law:
scaling the off-diagonal part, `t ↦ 1 + t n` with `n² = 0`, is a path of invertibles from
the identity to the congruence, so `t ↦ (1 + t n)ᵀ M (1 + t n)` is a norm-continuous path of
invertible self-adjoint elements.  Along it the negative spectral projection varies
norm-continuously, so its trace is constant.  `nilpotent_path_inv` records that every point
of the path is invertible, which is the part that could fail and does not.

## Audit outcome for the other claims

* **Pimsner–Voiculescu.**  `K₀(C*_r(F_b)) = ℤ·[1]`, and with Powers' faithful unique trace
  this gives projectionlessness: a projection has integer trace in `[0,1]`, hence is `0` or
  `1`.  Correct as used.  The element consumed, `S_v(x)`, is a **finite** sum of group
  elements, so it lies in the group algebra inside `C*_r(F_b)` and not merely in the von
  Neumann algebra, which is what makes projectionlessness applicable at all.
* **`K₀` integrality of `δ` at `k = 2`.**  `K₀(M₂(A)) ≅ K₀(A)` by stability, `[P] = m[1_A]`,
  and the unnormalised trace gives `τ₂(P) = m ∈ {0,1,2}`.  Correct as used.
* **The trace formula `τ(S_v) = μ_G/μ_F`.**  Correct for **simple** graphs.  The no-bypass
  step uses that a lifted attachment point has exactly one neighbouring lift of `v`, which
  holds because `v` and `p` are joined by a single edge.  For a multigraph with parallel
  edges the count changes, and the formula would need re-deriving.  Recorded here because
  the rest of the development does not otherwise say it.
-/

namespace Congruence

open Matrix

/-! ## Unipotent factors -/

/-- A unipotent upper-triangular block matrix is invertible, with explicit inverse. -/
theorem unipotent_inv {R : Type*} [Ring R] (x : R) :
    (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, -x; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lower-triangular counterpart. -/
theorem unipotent_inv' {R : Type*} [Ring R] (x : R) :
    (!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, 0; -x, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## The Schur congruence -/

/-- **The block factorisation.**  With `e` a two-sided inverse of `d`, the block matrix is
the product of a unipotent factor, the direct sum of the Schur complement and the corner,
and another unipotent factor.  This is the whole algebraic content of Haynsworth
additivity, and it holds over any ring. -/
theorem schur_factor {R : Type*} [Ring R] (a b c d e : R) (h1 : d * e = 1) (h2 : e * d = 1) :
    (!![1, b * e; 0, 1] : Matrix (Fin 2) (Fin 2) R)
        * !![a - b * e * c, 0; 0, d] * !![1, 0; e * c, 1]
      = !![a, b; c, d] := by
  have hde : ∀ y : R, d * (e * y) = y := fun y => by rw [← mul_assoc, h1, one_mul]
  have hed : ∀ y : R, e * (d * y) = y := fun y => by rw [← mul_assoc, h2, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, h2, hde]

/-! ## The homotopy that replaces Sylvester's law -/

/-- Scaling a square-zero element keeps `1 + t n` invertible, with inverse `1 - t n`.  This
is why the congruence can be deformed to the identity through invertibles, which is what
makes the trace of the negative spectral projection constant along the way. -/
theorem nilpotent_path_inv {R : Type*} [Ring R] (n : R) (hn : n * n = 0) (t : R)
    (ht : Commute t n) :
    (1 + t * n) * (1 - t * n) = 1 := by
  have h : (t * n) * (t * n) = 0 := by
    calc (t * n) * (t * n) = t * (n * (t * n)) := by rw [mul_assoc]
      _ = t * ((n * t) * n) := by rw [mul_assoc]
      _ = t * ((t * n) * n) := by rw [← ht.eq]
      _ = t * (t * (n * n)) := by rw [mul_assoc]
      _ = 0 := by rw [hn, mul_zero, mul_zero]
  calc (1 + t * n) * (1 - t * n) = 1 - (t * n) * (t * n) := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

/-- The off-diagonal generator of the congruence is square zero, so the path above applies
to it. -/
theorem offdiag_sq_zero {R : Type*} [Ring R] (x : R) :
    (!![0, x; 0, 0] : Matrix (Fin 2) (Fin 2) R) * !![0, x; 0, 0] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

end Congruence
