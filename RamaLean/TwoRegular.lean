import Mathlib
import RamaLean.ArcTangent

/-!
# The 2-regularity lemma, with the classical input isolated

The lemma that closes A6 says: if `F` is polynomial with `F 0 = 0` and `F' 0 = 0`, quadratic part
`Q(x) = B(x,x)`, and `D` satisfies `Q D = 0` with `E ↦ B(D,E)` onto, then `D` is tangent to a curve
in `F⁻¹(0)`. The proof is three steps.

1. **Divisibility.** `F(tD + t²w) = t³ G(t,w)` with `G` polynomial, because the coefficients of
   `t⁰`, `t¹` and `t²` are `F 0`, `F' 0 [D]` and `Q D`, all zero.
2. **A zero of the leading term.** `G(0,w) = 2B(D,w) + C(D,D,D)` is affine in `w` with onto linear
   part, so it has a zero `w₀`.
3. **Implicit function theorem** in `w` at `(0,w₀)`, giving `w(t)` with `G(t,w(t)) = 0`, hence
   `x(t) = tD + t²w(t)` in `F⁻¹(0)` with `x(t)/t → D`.

Step 2 is `exists_zero_of_affine`. Step 3's *output*, once it is granted, is turned into the
tangent-cone conclusion by `tangent_of_second_order_arc`, which is the part worth having machine-
checked because it is where the second-order shape `tD + t²w` does its work: the `t²` term is what
makes the difference quotient converge to `D` rather than to something else. Step 1 and the
invocation of the implicit function theorem are classical and are not formalised; they appear here
as the hypotheses `hmem` and `hw`, which is exactly what the theorem below consumes.

Stating it this way makes the division of labour explicit. What the classical input supplies is a
family of points of the set of the form `x₀ + tD + t²w`, with `t·w` going to zero. What is proved
here is that such a family puts `D` in the tangent cone. Anything that produces such a family, the
implicit function theorem or an explicit construction, feeds this theorem; the cross basis
directions of `code/spanrank.py` are the case where 2-regularity fails and the explicit rotation
supplies the family instead.

## Status

`exists_zero_of_affine` and `tangent_of_second_order_arc` are `VERIFIED`. Avakov's theorem itself is
cited (Avakov 1985; Arutyunov 2000) and is not formalised; the elementary proof of its fully
degenerate case is written out in `code/arc.py` and in the note.
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
