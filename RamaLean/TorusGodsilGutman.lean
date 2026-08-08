import Mathlib

/-!
# The torus form of Godsil–Gutman, and what connectedness buys

Godsil and Gutman average the characteristic polynomial over the `2^m` edge signings and
recover the matching polynomial.  Running the same average over the torus of the maximal
abelian cover gives

  `μ_G(x) = ∫_{T^b} det(x I - A_G(z)) dz`,

and this file isolates the two steps that make the torus version worth having.

## Why the average collapses to matchings

A permutation contributes the monomial `z^{[C₁] + ⋯ + [C_r]}`, where `[C]` is the homology
class of a cycle read off in the cotree basis.  Every cycle uses at least one cotree edge, so
`[C] ≠ 0`; vertex-disjoint cycles use disjoint edge sets, so their classes have disjoint
support.  A sum of nonzero vectors with pairwise disjoint supports is nonzero, so every
permutation with a cycle of length at least three is killed by the average.  What survives is
fixed points and transpositions, which is the matching polynomial.  That is
`sum_ne_zero_of_disjoint_support`, and it is the whole combinatorial content.

## What signings cannot do

The torus is **connected** and the set of signings is not.  A real continuous function that
never vanishes on a connected space has one sign, hence a nonzero average.  Since
`det(x I - A_G(z))` is real (the matrix is Hermitian), this gives

  `x ∉ spec(G^ab)  ⟹  μ_G(x) ≠ 0`,   that is   `Zeros(μ_G) ⊆ spec(G^ab)`.

No such argument is available over a finite set of signings, where a nonvanishing function
may take both signs.  This is `nonvanishing_average_ne_zero`.

## What it settles

Weaker than Heilmann–Lieb outside the spectrum, since `spec(G^ab)` contains the Perron value
of `G`.  Stronger inside: it settles Conjecture 10 at every point of a gap of `spec(T)` that
also misses `spec(G^ab)`, for **every** graph and **every** first Betti number, with no
feedback vertex hypothesis and no analytic estimate.  Measured over two growing families in
`code/torus_gg.py`, ten of fourteen gap points are settled this way, with a certified margin
that grows with the number of vertices.  The residue is a gap of `spec(T)` swallowed by a
band of the abelian cover, which is where the feedback vertex machinery is still needed.

`code/torus_gg.py` checks the identity itself to `7 · 10⁻¹⁵` on seven graphs with `b` up to
four, and certifies each verdict by a Lipschitz bound read off the exact Fourier
coefficients, a grid minimum alone being worthless when the zero set is a curve.
-/

namespace TorusGodsilGutman

/-! ## The combinatorial step: disjoint supports cannot cancel -/

/-- **Nonzero vectors with pairwise disjoint supports have nonzero sum.**  Applied to the
homology classes of the cycles of a permutation: each is nonzero because a cycle must use a
cotree edge, and any two are disjointly supported because the cycles are vertex-disjoint.  So
only permutations without long cycles survive the average over the torus. -/
theorem sum_ne_zero_of_disjoint_support {b : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → Fin b → ℤ) (hs : s.Nonempty) (hne : ∀ i ∈ s, v i ≠ 0)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ k, v i k = 0 ∨ v j k = 0) :
    ∑ i ∈ s, v i ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨k, hk⟩ : ∃ k, v i₀ k ≠ 0 := by
    by_contra h
    exact hne i₀ hi₀ (funext fun k => not_not.mp (fun hh => h ⟨k, hh⟩))
  intro hsum
  have hzero : (∑ i ∈ s, v i) k = 0 := by rw [hsum]; rfl
  rw [Finset.sum_apply] at hzero
  have : ∀ i ∈ s, i ≠ i₀ → v i k = 0 := by
    intro i hi hne'
    rcases hdisj i hi i₀ hi₀ hne' k with h | h
    · exact h
    · exact absurd h hk
  rw [Finset.sum_eq_single_of_mem i₀ hi₀ (fun i hi h => this i hi h)] at hzero
  exact hk hzero

/-! ## The topological step: no zeros on a connected space means one sign -/

/-- **A nonvanishing continuous real function on a connected space has constant sign.**  The
positive part is open, and so is the negative part; with no zeros they partition the space,
so each is clopen.  The set of edge signings is finite and discrete, which is exactly why the
Godsil–Gutman average admits no counterpart of this step. -/
theorem sign_const_of_nonvanishing {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hc : Continuous f) (hne : ∀ z, f z ≠ 0) :
    (∀ z, 0 < f z) ∨ (∀ z, f z < 0) := by
  have hopen : IsOpen {z | 0 < f z} := isOpen_lt continuous_const hc
  have hopen' : IsOpen {z | f z < 0} := isOpen_lt hc continuous_const
  have hcompl : {z | 0 < f z}ᶜ = {z | f z < 0} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hne z), fun h => le_of_lt h⟩
  have hclopen : IsClopen {z | 0 < f z} := ⟨by rw [← isOpen_compl_iff, hcompl]; exact hopen',
    hopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · right
    intro z
    have : z ∉ {z | 0 < f z} := by rw [h]; exact Set.notMem_empty z
    simpa [hcompl] using (Set.mem_compl this : z ∈ {z | 0 < f z}ᶜ)
  · left
    intro z
    have : z ∈ {z | 0 < f z} := by rw [h]; trivial
    exact this

/-- On a compact space a positive continuous function is bounded below by a positive
constant, which is what turns constancy of sign into a nonzero average. -/
theorem exists_pos_lower {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {f : X → ℝ} (hc : Continuous f) (hpos : ∀ z, 0 < f z) : ∃ c, 0 < c ∧ ∀ z, c ≤ f z := by
  obtain ⟨z₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  exact ⟨f z₀, hpos z₀, fun z => hmin (Set.mem_univ z)⟩

/-! ## The conclusion -/

open MeasureTheory

/-- **A nonvanishing continuous function on a compact connected space has nonzero average.**
With `f z = det(x I - A_G(z))` on the torus and `μ` normalised Haar measure, the left side is
`μ_G(x)` by the identity above, so `x ∉ spec(G^ab)` forces `μ_G(x) ≠ 0`. -/
theorem nonvanishing_average_ne_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [PreconnectedSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hc : Continuous f) (hne : ∀ z, f z ≠ 0) : ∫ z, f z ∂μ ≠ 0 := by
  have hint : Integrable f μ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rcases sign_const_of_nonvanishing hc hne with hpos | hneg
  · obtain ⟨c, hc0, hcle⟩ := exists_pos_lower hc hpos
    have : c ≤ ∫ z, f z ∂μ := by
      have h1 : ∫ _z : X, c ∂μ ≤ ∫ z, f z ∂μ :=
        integral_mono (integrable_const c) hint hcle
      simpa using h1
    linarith
  · obtain ⟨c, hc0, hcle⟩ := exists_pos_lower hc.neg (fun z => by simpa using (hneg z))
    have : c ≤ ∫ z, -f z ∂μ := by
      have h1 : ∫ _z : X, c ∂μ ≤ ∫ z, -f z ∂μ :=
        integral_mono (integrable_const c) hint.neg hcle
      simpa using h1
    rw [integral_neg] at this
    linarith

/-- **`Zeros(μ_G) ⊆ spec(G^ab)`**, in the form the application uses: if the Floquet
determinant never vanishes on the torus, then the matching polynomial does not vanish at `x`.
The hypothesis `hGG` is the torus Godsil–Gutman identity. -/
theorem mu_ne_zero_of_nonvanishing {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [PreconnectedSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {muG : ℝ}
    (hc : Continuous f) (hne : ∀ z, f z ≠ 0) (hGG : muG = ∫ z, f z ∂μ) : muG ≠ 0 := by
  rw [hGG]
  exact nonvanishing_average_ne_zero μ hc hne

end TorusGodsilGutman
