import Mathlib

/-!
# The band functions are Lipschitz, with an explicit constant

`ParitySplit` uses a Lipschitz constant for the band functions `λ_k` in the torus phases.  In
the Schur-complement formulation that constant had to be measured, and it scaled like
`1/μ_F(x)`.  Without the Schur complement it is explicit, and this file proves the bound that
makes it so.

## The mechanism

`∂A_G(z)/∂θ_j` is the matrix with `i z_j` in position `(u_j, v_j)` and its conjugate in
position `(v_j, u_j)`, and zero elsewhere.  First-order perturbation theory gives
`∂λ_k/∂θ_j = ⟨v_k, (∂A/∂θ_j) v_k⟩` for a unit eigenvector `v_k`, and that quadratic form is
`2 Re(conj(v_{k,u_j}) · i z_j · v_{k,v_j})`, of absolute value at most
`2|v_{k,u_j}| |v_{k,v_j}| ≤ |v_{k,u_j}|² + |v_{k,v_j}|²`.  Summing over the cotree edges,
each vertex `i` is charged `|v_{k,i}|²` once per incident cotree edge, so

  `∑_j |∂λ_k/∂θ_j| ≤ D`,   `D = max over vertices of the number of incident cotree edges`.

`D ≤ 2` whenever the cotree edges can be chosen vertex-disjoint, and `D ≤ Δ(G)` always.  This
is sharper than the crude `‖A(z) - A(w)‖ ≤ ∑_j |Δθ_j|`, which gives `b` in place of `D`, and
the difference matters: `b` grows with the graph while `D` does not.

## What is proved here

`quad_form_bound` is the per-edge estimate and `sum_deg_bound` the double count, so
`grad_l1_bound` is the displayed inequality.  First-order perturbation theory itself is not
formalized; it enters `grad_l1_bound` as the hypothesis `hderiv`, in exactly the shape it is
used.  The `ℓ¹` bound is the useful one, since it converts a coordinatewise phase change into
a bound on the eigenvalue change with no dimensional loss.
-/

namespace BandLipschitz

open Finset

/-! ## The per-edge estimate -/

/-- `2ab ≤ a² + b²`, the only inequality in the argument. -/
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **The quadratic form of one cotree edge is bounded by the mass at its endpoints.**  With
`w` of modulus at most one, `|2 Re(conj a · w · b)| ≤ ‖a‖² + ‖b‖²`. -/
theorem quad_form_bound (a b w : ℂ) (hw : ‖w‖ ≤ 1) :
    |2 * ((starRingEnd ℂ) a * w * b).re| ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : |((starRingEnd ℂ) a * w * b).re| ≤ ‖(starRingEnd ℂ) a * w * b‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖(starRingEnd ℂ) a * w * b‖ = ‖a‖ * ‖w‖ * ‖b‖ := by
    simp
  have h3 : ‖a‖ * ‖w‖ * ‖b‖ ≤ ‖a‖ * ‖b‖ := by
    have : ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hw (norm_nonneg a)
    calc ‖a‖ * ‖w‖ * ‖b‖ ≤ (‖a‖ * 1) * ‖b‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg b)
      _ = ‖a‖ * ‖b‖ := by ring
  have h4 : |2 * ((starRingEnd ℂ) a * w * b).re| = 2 * |((starRingEnd ℂ) a * w * b).re| := by
    rw [abs_mul]; norm_num
  rw [h4]
  calc 2 * |((starRingEnd ℂ) a * w * b).re| ≤ 2 * (‖a‖ * ‖b‖) := by
        have := h1.trans (le_of_eq h2) |>.trans h3
        linarith
    _ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := two_mul_le_sq_add_sq _ _

/-! ## The double count -/

/-- **Each vertex is charged once per incident cotree edge.**  If the endpoint incidences of
every vertex in `s` total at most `D`, then summing the endpoint masses over `s` costs at most
`D` times the total mass.  This is what replaces the first Betti number by a degree. -/
theorem sum_deg_bound {V : Type*} [Fintype V] [DecidableEq V] (s : Finset (V × V))
    (f : V → ℝ) (hf : ∀ i, 0 ≤ f i) (D : ℕ)
    (hD : ∀ i : V, (s.filter (fun e => e.1 = i)).card
        + (s.filter (fun e => e.2 = i)).card ≤ D) :
    ∑ e ∈ s, (f e.1 + f e.2) ≤ D * ∑ i, f i := by
  classical
  have h1 : ∑ e ∈ s, f e.1 = ∑ i, ((s.filter (fun e => e.1 = i)).card : ℝ) * f i := by
    rw [← Finset.sum_fiberwise s (fun e => e.1) (fun e => f e.1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun e he => by
      rw [(Finset.mem_filter.mp he).2] : ∀ e ∈ s.filter (fun e => e.1 = i), f e.1 = f i)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ e ∈ s, f e.2 = ∑ i, ((s.filter (fun e => e.2 = i)).card : ℝ) * f i := by
    rw [← Finset.sum_fiberwise s (fun e => e.2) (fun e => f e.2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun e he => by
      rw [(Finset.mem_filter.mp he).2] : ∀ e ∈ s.filter (fun e => e.2 = i), f e.2 = f i)]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf i)
  exact_mod_cast hD i

/-! ## The assembly -/

/-- **The `ℓ¹` gradient bound.**  Given the first-order formula for each phase derivative as
the quadratic form of the corresponding cotree edge, the derivatives sum to at most `D`.  So a
phase change of total variation `t` moves any band function by at most `D t`, with `D` a
degree of the cotree and not the first Betti number.  First-order perturbation theory is not
formalized; it enters as `hderiv`, in the shape the argument consumes. -/
theorem grad_l1_bound {V : Type*} [Fintype V] [DecidableEq V] (s : Finset (V × V))
    (v : V → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) (w : V × V → ℂ) (hw : ∀ e, ‖w e‖ ≤ 1)
    (D : ℕ) (hD : ∀ i : V, (s.filter (fun e => e.1 = i)).card
        + (s.filter (fun e => e.2 = i)).card ≤ D)
    (d : V × V → ℝ)
    (hderiv : ∀ e ∈ s, d e = 2 * ((starRingEnd ℂ) (v e.1) * w e * v e.2).re) :
    ∑ e ∈ s, |d e| ≤ D := by
  calc ∑ e ∈ s, |d e| ≤ ∑ e ∈ s, (‖v e.1‖ ^ 2 + ‖v e.2‖ ^ 2) := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [hderiv e he]
        exact quad_form_bound _ _ _ (hw e)
    _ ≤ D * ∑ i, ‖v i‖ ^ 2 :=
        sum_deg_bound s (fun i => ‖v i‖ ^ 2) (fun _ => sq_nonneg _) D hD
    _ = D := by rw [hv, mul_one]

end BandLipschitz
