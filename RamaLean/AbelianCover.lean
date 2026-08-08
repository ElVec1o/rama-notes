import Mathlib

/-!
# Localization of matching roots in the maximal abelian cover

Choose a spanning tree of `G`, put a circle variable on each of the `b = b₁(G)` cotree
edges, and let `A_G(z)` be the resulting magnetic adjacency matrix.  Then

  `μ_G(x) = ∫_{T^b} det(x I - A_G(z)) dz`,

because Haar integration over the torus kills every permutation cycle of length at least
three: a simple cycle of `G` must use a cotree edge, so its monomial is a nontrivial
character.  Only fixed points and transpositions survive, which is exactly the matching
sum.  (Transpositions on a cotree edge contribute `z z⁻¹ = 1`.)

Two facts make this into a localization theorem.

* `det_hermitian_im` — for `|z| = 1` the matrix `A_G(z)` is Hermitian, so `det(xI - A_G(z))`
  is **real** for real `x`.  This is what allows a sign argument at all.
* `exists_zero_of_integral_zero` — a continuous real function on a connected space whose
  average vanishes must vanish somewhere.  Positivity is impossible, and the intermediate
  value theorem finishes.

Together: if `μ_G(t) = 0` then `det(t I - A_G(z)) = 0` for some `z`, i.e. `t` is an
eigenvalue of `A_G(z)`, i.e. `t ∈ spec(G^ab)` by Floquet–Bloch.  The conjecture is thereby
reduced to `Zeros(μ_G) ∩ (spec(G^ab) \ spec(T)) = ∅`.

`root_mem_of_average` is that implication, with the torus identity itself as a hypothesis:
the Godsil–Gutman expansion over cycle types is the one step that remains by hand.
-/

namespace AbelianCover

open MeasureTheory

/-! ## The integrand is real -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a Hermitian matrix is fixed by conjugation. -/
theorem det_hermitian_star {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    star M.det = M.det := by
  rw [← Matrix.det_conjTranspose, hM.eq]

/-- Hence it is real. -/
theorem det_hermitian_im {M : Matrix n n ℂ} (hM : M.IsHermitian) : (M.det).im = 0 := by
  have h := det_hermitian_star hM
  rw [← Complex.conj_eq_iff_im]
  exact h

/-- `x I - M` is Hermitian whenever `M` is and `x` is real, so the characteristic value
`det(x I - M)` that gets integrated is real. -/
theorem det_sub_smul_one_im {M : Matrix n n ℂ} (hM : M.IsHermitian) (x : ℝ) :
    ((x : ℂ) • (1 : Matrix n n ℂ) - M).det.im = 0 := by
  refine det_hermitian_im ?_
  have h1 : ((x : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [Complex.conj_ofReal]
  exact h1.sub hM

/-! ## The zero-average engine -/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

omit [TopologicalSpace X] in
/-- A nonnegative integrable function with vanishing integral vanishes at a point. -/
theorem exists_zero_of_nonneg {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hnn : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) (h0 : ∫ x, f x ∂μ = 0) :
    ∃ x, f x = 0 := by
  have hae : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hnn hfi).mp h0
  obtain ⟨x, hx⟩ := hae.exists
  exact ⟨x, hx⟩

/-- **The engine.**  A continuous real function on a connected space whose average over a
probability measure is zero has a zero.  If it never changed sign the integral could not
vanish; if it does change sign the intermediate value theorem produces the root. -/
theorem exists_zero_of_integral_zero [PreconnectedSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Continuous f) (hfi : Integrable f μ)
    (h0 : ∫ x, f x ∂μ = 0) : ∃ x, f x = 0 := by
  by_cases h1 : ∃ a, f a ≤ 0
  · obtain ⟨a, ha⟩ := h1
    by_cases h2 : ∃ b, 0 ≤ f b
    · obtain ⟨b, hb⟩ := h2
      exact intermediate_value_univ₂ hf continuous_const ha hb
    · -- `f < 0` everywhere, so `-f` is nonnegative with vanishing integral
      push Not at h2
      have hnn : ∀ x, 0 ≤ (-f) x := fun x => by simpa using (h2 x).le
      have hfi' : Integrable (-f) μ := hfi.neg
      have h0' : ∫ x, (-f) x ∂μ = 0 := by simp [integral_neg, h0]
      obtain ⟨x, hx⟩ := exists_zero_of_nonneg hnn hfi' h0'
      exact ⟨x, by simpa using hx⟩
  · -- `f > 0` everywhere
    push Not at h1
    exact exists_zero_of_nonneg (fun x => (h1 x).le) hfi h0

/-! ## The localization -/

/-- **Roots of an average are roots of a member.**  If `mu` is the average over a connected
parameter space of a continuous real family `D`, then every zero of `mu` is a zero of `D t`
at some parameter.

Applied with `X = T^b` the torus, `D t z = det(t I - A_G(z))` (real by
`det_sub_smul_one_im`) and `mu = μ_G`, this says every matching root is an eigenvalue of
some `A_G(z)`, i.e. lies in the spectrum of the maximal abelian cover. -/
theorem root_mem_of_average [PreconnectedSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {D : ℝ → X → ℝ} {mu : ℝ → ℝ}
    (hcont : ∀ t, Continuous (D t)) (hint : ∀ t, Integrable (D t) μ)
    (haverage : ∀ t, mu t = ∫ z, D t z ∂μ)
    {t : ℝ} (ht : mu t = 0) : ∃ z, D t z = 0 :=
  exists_zero_of_integral_zero (hcont t) (hint t) (by rw [← haverage t]; exact ht)

/-- The reduction the localization buys: once every root is known to lie in `spec(G^ab)`,
the conjecture is exactly the statement that no root lies in the part of `spec(G^ab)` that
the universal cover misses. -/
theorem reduction {roots abelianSpec univSpec : Set ℝ}
    (hloc : roots ⊆ abelianSpec) :
    roots ⊆ univSpec ↔ roots ∩ (abelianSpec \ univSpec) = ∅ := by
  constructor
  · intro h
    ext t
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨htr, -, hnu⟩
    exact hnu (h htr)
  · intro h t htr
    by_contra hnu
    have hmem : t ∈ roots ∩ (abelianSpec \ univSpec) := ⟨htr, hloc htr, hnu⟩
    rw [h] at hmem
    exact hmem

end AbelianCover
