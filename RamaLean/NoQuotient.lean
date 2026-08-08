import Mathlib

/-!
# No reduced quotient onto the abelianisation, and a retraction

An earlier entry in this development asserted `δ = δ_ab` off `spec(G^ab)`, proved by pushing
the negative spectral projection of the Schur complement through a unital `*`-homomorphism
`C*_r(F_b) → C*_r(ℤ^b) = C(T^b)`, on the ground that a quotient with amenable image is
weakly contained in the regular representation.

**That ground is wrong, and the map does not exist.**  For `N ⊴ Γ` the quotient descends to
reduced C*-algebras when `N` is amenable, not when `Γ/N` is.  Here `N = [F_b, F_b]` is free
of infinite rank for `b ≥ 2`, hence not amenable.

The premise is not merely unsupported, it is refutable, and this file records the shape of
the refutation.  A unital ring homomorphism carries units to units, so a single element that
is invertible upstairs and singular downstairs rules out every such map at once.  Applied
here: if `π` existed then `S(x)` invertible would force `S(x,z)` invertible for every `z`,
hence `det(xI - A_G(z)) = μ_F(x)·det S(x,z)` nonzero for every `z`, hence

  `spec(G^ab) ⊆ spec(T) ∪ roots(μ_F)`.

For `K_4` with a two-element feedback set that fails at `x = 3`: the Perron eigenvalue puts
`3 ∈ spec(G^ab)`, while `ρ(T) = 2√2 < 3` and `μ_{K_2}(3) = 8 ≠ 0`.

What survives, and at which label:

* the **conclusion** `δ = δ_ab` off `spec(G^ab)` is now HEURISTIC, not PROVED.  Checked in
  `code/abelian_vs_universal.py` by computing the two sides independently, the abelian band
  count from the magnetic matrix over a phase grid and the gap label from the cavity
  solver.  They agree at every genuine abelian gap on `K_4`, two triangles joined by an
  edge, the theta graph and `K_4` with pendants.
* the **barrier** is unaffected and in fact strengthened.  Those runs show `spec(G^ab)` has
  almost no internal gaps: for all four graphs the only ones are above and below the whole
  spectrum, plus `x = 0` for `K_4` with pendants.  The abelian cover fills in precisely the
  region where the universal cover still has gaps, which is why no argument through the
  torus family reaches it.
-/

namespace NoQuotient

/-- **Units are preserved.**  A unital ring homomorphism carries invertible elements to
invertible elements. -/
theorem isUnit_map {A B : Type*} [Ring A] [Ring B] (f : A →+* B) {a : A} (ha : IsUnit a) :
    IsUnit (f a) :=
  ha.map f

/-- **One element refutes every homomorphism.**  If `a` is invertible and `b` is not, then
no unital ring homomorphism sends `a` to `b`.  This is the shape of the argument that kills
the quotient `C*_r(F_b) → C(T^b)`: the Schur complement is invertible in the free algebra
and singular at some phase. -/
theorem no_hom_of_unit_to_nonunit {A B : Type*} [Ring A] [Ring B]
    {a : A} (ha : IsUnit a) {b : B} (hb : ¬ IsUnit b) :
    ¬ ∃ f : A →+* B, f a = b := by
  rintro ⟨f, hf⟩
  exact hb (hf ▸ isUnit_map f ha)

/-- The same conclusion in the contrapositive form the application uses: granting the
homomorphism, invertibility upstairs forces invertibility downstairs, for every point of
the parameter space at once. -/
theorem unit_everywhere_of_hom {A : Type*} [Ring A] {Z B : Type*} [Ring B]
    (f : A →+* B) (ev : Z → B →+* ℂ) {a : A} (ha : IsUnit a) (z : Z) :
    IsUnit ((ev z) (f a)) :=
  isUnit_map (ev z) (isUnit_map f ha)

/-- **The consequence that fails.**  Granting the homomorphism, a point outside the
universal cover spectrum and off the roots of `μ_F` would have to lie outside the abelian
spectrum too, since the abelianised determinant factors as `μ_F` times the determinant of
the Schur complement.  Stated with the factorisation as a hypothesis, so that the failure is
located precisely: it is the hypothesis `hunit` that cannot be had, not the algebra. -/
theorem abelian_det_ne_zero_of_hom {Z : Type*} (μF : ℝ) (detS : Z → ℝ) (detA : Z → ℝ)
    (hfac : ∀ z, detA z = μF * detS z)
    (hμF : μF ≠ 0) (hunit : ∀ z, detS z ≠ 0) : ∀ z, detA z ≠ 0 := by
  intro z hz
  rw [hfac z] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hμF h
  · exact hunit z h

/-- **The refutation, as an implication with a numerical witness slot.**  If some point has
`detA z₀ = 0` while `μ_F ≠ 0`, then `detS z₀ = 0`, so the Schur complement is singular at
that phase and no homomorphism of the assumed kind exists.  The witness supplied in
`code/abelian_vs_universal.py` is `K_4` at `x = 3`. -/
theorem singular_witness {Z : Type*} (μF : ℝ) (detS : Z → ℝ) (detA : Z → ℝ)
    (hfac : ∀ z, detA z = μF * detS z) (hμF : μF ≠ 0)
    {z₀ : Z} (hz₀ : detA z₀ = 0) : detS z₀ = 0 := by
  have h := hfac z₀
  rw [hz₀] at h
  rcases mul_eq_zero.mp h.symm with hm | hs
  · exact absurd hm hμF
  · exact hs

end NoQuotient
