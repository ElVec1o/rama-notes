import Mathlib
import RamaLean.ArcTangent

/-!
# The 2-regularity lemma, with the classical input isolated

The lemma that closes A6 says: if `F` is polynomial with `F 0 = 0` and `F' 0 = 0`, quadratic part
`Q(x) = B(x,x)`, and `D` satisfies `Q D = 0` with `E ↦ B(D,E)` onto, then `D` is tangent to a curve
in `F⁻¹(0)`. The proof is three steps.

1. **Divisibility.** `F(tD + t²w) = t³ G(t,w)` with `G` polynomial, because the coefficients of
   `t⁰`, `t¹` and `t²` are `F 0`, `F' 0 [D]` and `Q D`, all zero.  This is `quadratic_expand` and
   `cubic_expand` below: each homogeneous piece of `F` is expanded at `tD + t²w` and the divisibility
   is read off.  The quadratic piece is the only one where `Q D = 0` is used, and it is used exactly
   once, to kill the `t²` term.
2. **A zero of the leading term.** `G(0,w) = 2B(D,w) + C(D,D,D)` is affine in `w` with onto linear
   part, so it has a zero `w₀`.
3. **Implicit function theorem** in `w` at `(0,w₀)`, giving `w(t)` with `G(t,w(t)) = 0`, hence
   `x(t) = tD + t²w(t)` in `F⁻¹(0)` with `x(t)/t → D`.

Step 1 is `quadratic_expand` and `cubic_expand`, and `leading_zero_of_surjective` assembles their
`t³` coefficients into the statement that the leading term has a zero.  Step 2 is
`exists_zero_of_affine`.  Step 3's *output*, once it is granted, is turned into the tangent-cone
conclusion by `tangent_of_second_order_arc`, which is where the second-order shape `tD + t²w` does
its work: the `t²` term is what makes the difference quotient converge to `D` rather than to
something else.  Only the invocation of the implicit function theorem is classical and unformalised;
it appears as the hypotheses `hmem` and `hw` of the last theorem, which is exactly what it supplies.

The expansions are stated for the homogeneous pieces as multilinear maps rather than for a general
`F`, because that is what the tight projection variety hands over: `Ψ` is a quadratic map, its
diagonal part restricted to the frame manifold is a polynomial of low degree, and the pieces are
available individually.  Nothing is lost and no Taylor-series machinery is needed.

Stating it this way makes the division of labour explicit. What the classical input supplies is a
family of points of the set of the form `x₀ + tD + t²w`, with `t·w` going to zero. What is proved
here is that such a family puts `D` in the tangent cone. Anything that produces such a family, the
implicit function theorem or an explicit construction, feeds this theorem; the cross basis
directions of `code/spanrank.py` are the case where 2-regularity fails and the explicit rotation
supplies the family instead.

## Status

`quadratic_expand`, `cubic_expand`, `leading_zero_of_surjective`, `exists_zero_of_affine` and
`tangent_of_second_order_arc` are `VERIFIED`. What remains cited rather than proved is the implicit
function theorem step alone; Avakov's theorem (Avakov 1985; Arutyunov 2000) is the reference for the
whole, and the elementary proof of its fully degenerate case is written out in `code/arc.py` and in
the note.
-/

namespace TwoRegular

open Filter Topology

/-- **Step 2.**  An affine map with surjective linear part has a zero.  This is what makes the
leading coefficient of the expansion solvable, and it is the only place the rank hypothesis of
2-regularity is used. -/
theorem exists_zero_of_affine {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V] [Module ℝ V] (L : W →ₗ[ℝ] V) (hL : Function.Surjective L) (c : V) :
    ∃ w, L w + c = 0 := by
  obtain ⟨w, hw⟩ := hL (-c)
  exact ⟨w, by rw [hw, neg_add_cancel]⟩

section Expansion

variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

/-- **Step 1, the quadratic piece.**  With `Q x = B x x` symmetric and `Q D = 0`, the value at the
second-order jet is divisible by `t³`, and the `t³` coefficient is `2 B D w`, linear in `w`.  This is
the only place the hypothesis `Q D = 0` is consumed, and it is what removes the `t²` term that would
otherwise obstruct everything. -/
theorem quadratic_expand (B : E →ₗ[ℝ] E →ₗ[ℝ] V) (hsymm : ∀ x y, B x y = B y x)
    (D w : E) (hD : B D D = 0) (t : ℝ) :
    B (t • D + t ^ 2 • w) (t • D + t ^ 2 • w) = t ^ 3 • ((2 : ℝ) • B D w + t • B w w) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hD, smul_zero]
  rw [hsymm w D]
  module

/-- **Step 1, the cubic piece.**  A trilinear term at the same jet is divisible by `t³` with leading
coefficient `C D D D`, which is a constant in `w`.  Together with the previous lemma the `t³`
coefficient of `F` is `2 B D w + C D D D`, affine in `w`. -/
theorem cubic_expand (C : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] V) (D w : E) (t : ℝ) :
    C (t • D + t ^ 2 • w) (t • D + t ^ 2 • w) (t • D + t ^ 2 • w)
      = t ^ 3 • (C D D D
          + t • (C D D w + C D w D + C w D D)
          + t ^ 2 • (C D w w + C w D w + C w w D)
          + t ^ 3 • C w w w) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  module

/-- **Steps 1 and 2 together.**  If `w ↦ 2 B D w` is onto, the `t³` coefficient of the expansion has
a zero, which is the leading term the implicit function theorem is then applied at.  The surjectivity
hypothesis is 2-regularity, and this is the only statement that uses it. -/
theorem leading_zero_of_surjective (B : E →ₗ[ℝ] E →ₗ[ℝ] V) (C : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] V) (D : E)
    (hB : Function.Surjective (fun w => (2 : ℝ) • B D w)) :
    ∃ w : E, (2 : ℝ) • B D w + C D D D = 0 := by
  obtain ⟨w, hw⟩ := hB (-(C D D D))
  refine ⟨w, ?_⟩
  rw [show (2 : ℝ) • B D w = -(C D D D) from hw, neg_add_cancel]

end Expansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Step 3's payoff.**  A family of points of `S` of the second-order form `x₀ + tD + t²w`, with
`t · w` tending to zero, puts `D` in the tangent cone at `x₀`.

The hypothesis on `w` is the weakest one that works: `w` need not converge, only `γ • w` need go to
zero, which is what boundedness of `w` gives and what the implicit function theorem delivers. The
`t²` in front of `w` is doing the work: with `t¹` there the quotient would converge to `D + w 0`
and the tangent would be the wrong vector. -/
theorem tangent_of_second_order_arc (S : Set E) (x₀ D : E) (γ : ℕ → ℝ) (w : ℕ → E)
    (hpos : ∀ n, 0 < γ n) (hto : Tendsto γ atTop (𝓝 0))
    (hw : Tendsto (fun n => γ n • w n) atTop (𝓝 0))
    (hmem : ∀ n, x₀ + (γ n • D + (γ n) ^ 2 • w n) ∈ S) :
    D ∈ tangentConeAt ℝ S x₀ := by
  refine ArcTangent.mem_tangentCone_of_arc S x₀ D γ
    (fun n => γ n • D + (γ n) ^ 2 • w n) hpos hto hmem ?_
  have key : ∀ n, (γ n)⁻¹ • (γ n • D + (γ n) ^ 2 • w n) = D + γ n • w n := by
    intro n
    have hne : γ n ≠ 0 := ne_of_gt (hpos n)
    rw [smul_add, inv_smul_smul₀ hne, smul_smul, sq]
    rw [inv_mul_cancel_left₀ hne]
  refine Filter.Tendsto.congr (fun n => (key n).symm) ?_
  simpa using tendsto_const_nhds.add hw

end TwoRegular
