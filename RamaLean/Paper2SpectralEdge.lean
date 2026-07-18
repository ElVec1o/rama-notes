import Mathlib
open Polynomial.Chebyshev Real
/-!
# The spectral edge of the `Cₙ` `r`-lift d-matching polynomial

The (`r−1`)-matching polynomial of `Cₙ` (= expected new-part char. poly. of a random permutation
`r`-lift, Hall–Puder–Sawin) is `Ψ_r(x) = U_{r−1}(Tₙ(x/2))`. This file machine-checks exactly one
fact (`spectral_edge_is_root`): `2cos(π/(nr))` **is a root** of `Ψ_r`, i.e.
`U_{r−1}(Tₙ(cos(π/(nr)))) = 0`, via `Tₙ(cos θ)=cos(nθ)` and the vanishing of `U_{r−1}` at `cos(π/r)`.

Mathematically this root is in fact the *largest* (the other roots are `2cos(jπ/(nr))`, `j>1`, and
`cos` is decreasing on `[0,π]`), so the Ramanujan spectral gap is `2 − 2cos(π/(nr)) ∼ π²/(nr)²`, a
closed-form finite-`r` gap. Those two statements — largest root, and hence the gap asymptotics — are
**not** formalized here; only root-ness is.
-/

namespace Paper2SpectralEdge

/-- The spectral edge `x = 2cos(π/(nr))` is a root of `Ψ_r(x) = U_{r−1}(Tₙ(x/2))`:
concretely `U_{r−1}(Tₙ(cos(π/(nr)))) = 0`. -/
theorem spectral_edge_is_root (n r : ℕ) (hn : 0 < n) (hr : 2 ≤ r) :
    (U ℝ ((r : ℤ) - 1)).eval ((T ℝ (n : ℤ)).eval (Real.cos (π / (n * r)))) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  -- Step 1: Tₙ(cos(π/(nr))) = cos(π/r)
  have hT : (T ℝ (n : ℤ)).eval (Real.cos (π / (n * r))) = Real.cos (π / r) := by
    rw [T_real_cos]
    congr 1
    push_cast
    field_simp
  rw [hT]
  -- Step 2: U_{r−1}(cos(π/r)) = 0, since U_{r−1}(cos φ)·sin φ = sin(r φ) and sin(π) = 0
  have hsin : Real.sin (π / r) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) < r := by exact_mod_cast hr
    nlinarith [Real.pi_pos]
  have hU := U_real_cos (θ := π / r) ((r : ℤ) - 1)
  have harg : ((((r : ℤ) - 1 : ℤ) : ℝ) + 1) * (π / (r : ℝ)) = π := by
    have h1 : ((((r : ℤ) - 1 : ℤ) : ℝ) + 1) = (r : ℝ) := by push_cast; ring
    rw [h1]; field_simp
  rw [harg, Real.sin_pi] at hU
  exact (mul_eq_zero.mp hU).resolve_right hsin

end Paper2SpectralEdge
