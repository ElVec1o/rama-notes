import Mathlib

/-!
# The quadrics carry an identity, and an arc gives a tangent

Two pieces of the passage from finite orders to a curve, the item labelled A6. The passage itself
is Avakov's 2-regularity theorem, which needs the implicit function theorem in a form Mathlib is not
going to hand over cheaply; what is checked here is the algebra around it, which is where the
content and the counting are.

## The identity

The second-order obstruction at a commuting tight family is the vector

  `Q_j(D) = ∑ₖ σₖ(j) (D_k²)_jj`,   `σₖ(j) = -1` if `j ∈ eₖ` and `+1` otherwise,

and 2-regularity asks that `E ↦ dQ(D)[E]` be onto. Onto *what* is the question, because the `n`
components of `Q` are never independent. `sum_sgn_diag_sq_eq_zero` says why, and says more than was
expected: the vanishing is not a statement about the sum over blocks but holds for each block on its
own,

  `∑_j σₖ(j) (D_k²)_jj = 0`   for every `k`.

The proof is one symmetry. `(D²)_jj = ∑_l D_{jl}²` because `D` is symmetric, so the sum is
`∑_{j,l} σ(j) D_{jl}²`; swapping the two indices rewrites it as `∑_{j,l} σ(l) D_{jl}²`; and adding
the two forms gives `∑_{j,l} (σ(j)+σ(l)) D_{jl}²`, in which every surviving term has `j` and `l` on
opposite sides of the hyperedge, since `D` is cross-supported, so `σ(j) + σ(l) = 0`. Note what is
used: symmetry and cross-support, nothing about tightness and nothing about the family.

So `Q` lands in the trace-zero diagonals and the surjectivity to ask for is onto the span of the
`Q_j`, which can be smaller still. It is `n-1` at `C_6`, `K_{3,3}` and the Fano family, and `2` at
`C_4`, which carries the extra pair `Q_0 + Q_2 = Q_1 + Q_3 = 0`, one per side of its bipartition.
Measured in `code/arc.py`, where the frozen form of the prediction said `n-1` for every family and
`C_4` falsified it.

## The arc

`mem_tangentCone_of_arc` is the other end: a curve in the set through the point whose difference
quotient converges is exactly what Mathlib's `tangentConeAt` wants, and it is worth having the
translation stated once rather than re-derived. Combined with 2-regularity, whose output is such a
curve, this is the step that upgrades a direction from "no obstruction at any finite order" to "in
the tangent cone".

The converse inclusion, that every tangent-cone direction satisfies `Q = 0`, is the second-order
obstruction and is `TangentObstruction.no_second_order`; it is the half that was already proved.

## Status

`sum_sgn_diag_sq_eq_zero`, `sum_sgn_diag_sq_eq_zero'` and `mem_tangentCone_of_arc` are `VERIFIED`.
Avakov's theorem is cited, not formalised, and appears in `code/arc.py` with the three-line proof
of the degenerate case it is used in.
-/

namespace ArcTangent

open Matrix Finset Filter Topology

section Identity

variable {ι : Type*} [Fintype ι]

/-- **The obstruction vector sums to zero, block by block.**  For a symmetric `D` supported on pairs
with exactly one endpoint in the hyperedge, the signed sum of the diagonal of `D²` vanishes.  Only
symmetry and the support condition are used. -/
theorem sum_sgn_diag_sq_eq_zero (mem : ι → Prop) [DecidablePred mem] (D : Matrix ι ι ℝ)
    (hsym : ∀ i j, D i j = D j i)
    (hcross : ∀ i j, (mem i ↔ mem j) → D i j = 0) :
    ∑ j, (if mem j then (-1 : ℝ) else 1) * (D * D) j j = 0 := by
  set σ : ι → ℝ := fun j => if mem j then (-1 : ℝ) else 1 with hσ
  -- the diagonal of `D²` is a sum of squares, by symmetry
  have hdiag : ∀ j, (D * D) j j = ∑ l, D j l * D j l := by
    intro j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hsym l j]
  have hS : ∑ j, σ j * (D * D) j j = ∑ j, ∑ l, σ j * (D j l * D j l) := by
    simp_rw [hdiag, Finset.mul_sum]
  -- the same double sum with the roles of the two indices exchanged
  have hswap : ∑ j, ∑ l, σ j * (D j l * D j l) = ∑ j, ∑ l, σ l * (D j l * D j l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [hsym l j]
  -- every term of the sum of the two forms vanishes
  have hzero : ∀ j l : ι, (σ j + σ l) * (D j l * D j l) = 0 := by
    intro j l
    by_cases h : mem j ↔ mem l
    · rw [hcross j l h]; ring
    · have hσ0 : σ j + σ l = 0 := by
        simp only [hσ]
        by_cases hj : mem j
        · have hl : ¬ mem l := fun hl => h ⟨fun _ => hl, fun _ => hj⟩
          simp [hj, hl]
        · have hl : mem l := by
            by_contra hl
            exact h ⟨fun x => absurd x hj, fun x => absurd x hl⟩
          simp [hj, hl]
      rw [hσ0]; ring
  have hsum : ∑ j, ∑ l, σ j * (D j l * D j l) + ∑ j, ∑ l, σ l * (D j l * D j l) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := hzero j l
    linarith [this]
  rw [hS]
  rw [hswap] at hsum ⊢
  linarith [hsum]

/-- The consequence for the whole obstruction: summing over the vertices kills it, so the `n`
quadrics satisfy at least the all-ones relation and `Q` lands in the trace-zero diagonals. -/
theorem sum_sgn_diag_sq_eq_zero' {κ : Type*} [Fintype κ] (mem : κ → ι → Prop)
    [∀ k, DecidablePred (mem k)] (D : κ → Matrix ι ι ℝ)
    (hsym : ∀ k i j, D k i j = D k j i)
    (hcross : ∀ k i j, (mem k i ↔ mem k j) → D k i j = 0) :
    ∑ j, ∑ k, (if mem k j then (-1 : ℝ) else 1) * ((D k) * (D k)) j j = 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun k _ => sum_sgn_diag_sq_eq_zero (mem k) (D k) (hsym k) (hcross k)

end Identity

section Arc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **An arc gives a tangent-cone element.**  If a curve stays in `S`, starts at `x₀` and its
difference quotient converges to `D`, then `D` lies in the tangent cone at `x₀`.  This is the
translation of the output of 2-regularity, which produces `x(t) = x₀ + tD + t²w(t)`, into Mathlib's
definition; the parameters are taken as a sequence since that is the form the definition uses. -/
theorem mem_tangentCone_of_arc (S : Set E) (x₀ D : E) (γ : ℕ → ℝ) (arc : ℕ → E)
    (hpos : ∀ n, 0 < γ n) (hto : Tendsto γ atTop (𝓝 0))
    (hmem : ∀ n, x₀ + arc n ∈ S)
    (hquot : Tendsto (fun n => (γ n)⁻¹ • arc n) atTop (𝓝 D)) :
    D ∈ tangentConeAt ℝ S x₀ := by
  -- the arc returns to the base point, since its quotient converges while `γ` does not
  have h0 : Tendsto arc atTop (𝓝 0) := by
    have h := hto.smul hquot
    rw [zero_smul] at h
    exact Filter.Tendsto.congr (fun n => smul_inv_smul₀ (ne_of_gt (hpos n)) (arc n)) h
  exact mem_tangentConeAt_of_seq atTop (fun n => (γ n)⁻¹) arc h0 (.of_forall hmem) hquot

end Arc

end ArcTangent
