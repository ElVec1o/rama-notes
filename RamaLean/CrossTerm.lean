import Mathlib

/-!
# The leading cross term is a perfect square

In the vertex recursion for a weighted `2`-plane family, split each bivector along a
unit vector `e` as `ω_k = e ∧ f_k + ω'_k` with `f_k = ι_e ω_k`.  The remainder `X_e`
that separates the recursion from the classical Heilmann–Lieb one expands as
`X_e = ∑_{r≥2} (-1)^{r-1} C_r x^{m-2r}`, and its leading coefficient is

  `C_2 = ∑_{k ≠ l} ⟨f_k ∧ ω'_l, f_l ∧ ω'_k⟩`.

Two facts collapse it.  First, `⟨u ∧ α, w ∧ γ⟩ = ⟨u,w⟩⟨α,γ⟩ - ⟨ι_w α, ι_u γ⟩`, so with
`u_k := ι_{f_k} ω'_k`,

  `C_2 = ∑_{k ≠ l} ⟨f_k,f_l⟩⟨ω'_k,ω'_l⟩ - ∑_{k ≠ l} ⟨u_k, u_l⟩`.

Second, `f_k = ι_e ω_k` lies in the plane of the simple bivector `ω'_k`, so
`f_k ∧ ω'_k = 0`, which is exactly `‖f_k‖²‖ω'_k‖² = ‖u_k‖²`.  And the off-diagonal
`(e, e^⊥)` block of `Adj(A)` is `∑_k u_k`, so tightness `Adj(A) = aI` says `∑_k u_k = 0`.

Under those two hypotheses everything cancels and `C_2` becomes a sum of squares:

  `C_2 = ∑_{i,j} (∑_k (f_k)_i (ω'_k)_j)²  ≥  0`,

which is `‖∑_k f_k ⊗ ω'_k‖²`.  Equality holds exactly when `∑_k f_k ⊗ ω'_k = 0`; for a
coordinate family at a coordinate direction every summand vanishes separately, since
each `ω_k` either contains `e` in its plane (`ω'_k = 0`) or is orthogonal to it
(`f_k = 0`) -- which is why the classical recursion has no cross terms at all.

`crossTerm_eq_sq` below is that statement, with the two geometric inputs carried as
hypotheses `hsimple` and `htight` so the dependence is visible.  Nothing here needs
exterior algebra: the bivectors enter only through their coordinates, so `f`, `ω'` and
`u` are plain indexed families of vectors, and the tensor `∑_k f_k ⊗ ω'_k` appears only
through its coordinates `∑_k (f_k)_i (ω'_k)_j`.
-/

namespace CrossTerm

open Finset BigOperators Matrix

variable {ι n p q : Type*} [Fintype ι] [Fintype n] [Fintype p] [Fintype q] [DecidableEq ι]

/-- Reordering four commuting finite sums. -/
theorem reorder4 (E : ι → ι → n → p → ℝ) :
    (∑ k, ∑ l, ∑ i, ∑ j, E k l i j) = ∑ i, ∑ j, ∑ k, ∑ l, E k l i j := by
  calc (∑ k, ∑ l, ∑ i, ∑ j, E k l i j)
      = ∑ k, ∑ i, ∑ l, ∑ j, E k l i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, E k l i j := Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ∑ l, E k l i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, E k l i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Reordering three commuting finite sums. -/
theorem reorder3 (E : ι → ι → q → ℝ) :
    (∑ k, ∑ l, ∑ i, E k l i) = ∑ i, ∑ k, ∑ l, E k l i := by
  calc (∑ k, ∑ l, ∑ i, E k l i)
      = ∑ k, ∑ i, ∑ l, E k l i := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, E k l i := Finset.sum_comm

/-- **The Gram–Hadamard sum is a sum of squares.**  For any two indexed families of
vectors, `∑_{k,l} ⟨f_k,f_l⟩⟨w_k,w_l⟩` is the squared norm of `∑_k f_k ⊗ w_k`, hence
nonnegative.  This is the Schur product theorem in the only case needed. -/
theorem sum_gram_prod_eq_sum_sq (f : ι → n → ℝ) (w : ι → p → ℝ) :
    (∑ k, ∑ l, (f k ⬝ᵥ f l) * (w k ⬝ᵥ w l))
      = ∑ i, ∑ j, (∑ k, f k i * w k j) ^ 2 := by
  have hL : (∑ k, ∑ l, (f k ⬝ᵥ f l) * (w k ⬝ᵥ w l))
      = ∑ k, ∑ l, ∑ i, ∑ j, (f k i * w k j) * (f l i * w l j) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [dotProduct, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hR : (∑ i, ∑ j, (∑ k, f k i * w k j) ^ 2)
      = ∑ i, ∑ j, ∑ k, ∑ l, (f k i * w k j) * (f l i * w l j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sq, Finset.sum_mul_sum]
  rw [hL, hR, reorder4]

/-- Nonnegativity, the form the application uses. -/
theorem sum_gram_prod_nonneg (f : ι → n → ℝ) (w : ι → p → ℝ) :
    0 ≤ ∑ k, ∑ l, (f k ⬝ᵥ f l) * (w k ⬝ᵥ w l) := by
  rw [sum_gram_prod_eq_sum_sq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- **The leading cross term is a perfect square.**

`hsimple` is `f_k ∧ ω'_k = 0`, in the equivalent metric form `‖f_k‖²‖ω'_k‖² = ‖u_k‖²`;
it holds automatically because `f_k = ι_e ω_k` lies in the plane of `ω'_k`.
`htight` is `∑_k ι_{f_k} ω'_k = 0`, which is the vanishing of the off-diagonal block of
`Adj(A)` and so is exactly the tightness hypothesis `Adj(A) = a I`. -/
theorem crossTerm_eq_sq (f : ι → n → ℝ) (w : ι → p → ℝ) (u : ι → q → ℝ)
    (hsimple : ∀ k, (f k ⬝ᵥ f k) * (w k ⬝ᵥ w k) = u k ⬝ᵥ u k)
    (htight : ∑ k, u k = 0) :
    (∑ k, ∑ l ∈ univ.erase k, ((f k ⬝ᵥ f l) * (w k ⬝ᵥ w l) - u k ⬝ᵥ u l))
      = ∑ i, ∑ j, (∑ k, f k i * w k j) ^ 2 := by
  classical
  -- the `u` double sum collapses: `∑_{k,l} ⟨u_k,u_l⟩ = ‖∑_k u_k‖² = 0`
  have hzero : ∀ i, (∑ k, u k i) = 0 := by
    intro i
    have := congrFun htight i
    simpa [Finset.sum_apply] using this
  have hu : (∑ k, ∑ l, u k ⬝ᵥ u l) = 0 := by
    have h1 : (∑ k, ∑ l, u k ⬝ᵥ u l) = ∑ i, (∑ k, u k i) * (∑ l, u l i) := by
      simp only [dotProduct]
      rw [reorder3]
      exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul_sum _ _ _ _).symm
    rw [h1]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]
  -- split each double sum into diagonal and off-diagonal
  have hsplit : ∀ (F : ι → ι → ℝ),
      (∑ k, ∑ l ∈ univ.erase k, F k l) = (∑ k, ∑ l, F k l) - ∑ k, F k k := by
    intro F
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← Finset.sum_erase_add univ _ (mem_univ k)]; ring
  rw [hsplit]
  simp only [Finset.sum_sub_distrib]
  rw [hu, ← sum_gram_prod_eq_sum_sq]
  have hdiag : (∑ k, ((f k ⬝ᵥ f k) * (w k ⬝ᵥ w k) - u k ⬝ᵥ u k)) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hsimple k]; ring
  have := hdiag
  rw [Finset.sum_sub_distrib] at this
  linarith

/-- The conclusion in the form the recursion consumes it: under the two hypotheses the
leading cross term is nonnegative. -/
theorem crossTerm_nonneg (f : ι → n → ℝ) (w : ι → p → ℝ) (u : ι → q → ℝ)
    (hsimple : ∀ k, (f k ⬝ᵥ f k) * (w k ⬝ᵥ w k) = u k ⬝ᵥ u k)
    (htight : ∑ k, u k = 0) :
    0 ≤ ∑ k, ∑ l ∈ univ.erase k, ((f k ⬝ᵥ f l) * (w k ⬝ᵥ w l) - u k ⬝ᵥ u l) := by
  rw [crossTerm_eq_sq f w u hsimple htight]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Equality holds exactly when the tensor `∑_k f_k ⊗ ω'_k` vanishes. -/
theorem crossTerm_eq_zero_iff (f : ι → n → ℝ) (w : ι → p → ℝ) (u : ι → q → ℝ)
    (hsimple : ∀ k, (f k ⬝ᵥ f k) * (w k ⬝ᵥ w k) = u k ⬝ᵥ u k)
    (htight : ∑ k, u k = 0) :
    (∑ k, ∑ l ∈ univ.erase k, ((f k ⬝ᵥ f l) * (w k ⬝ᵥ w l) - u k ⬝ᵥ u l)) = 0
      ↔ ∀ i j, (∑ k, f k i * w k j) = 0 := by
  rw [crossTerm_eq_sq f w u hsimple htight]
  constructor
  · intro h i j
    have hz : ∀ i' ∈ (univ : Finset n), ∀ j' ∈ (univ : Finset p),
        (∑ k, f k i' * w k j') ^ 2 = 0 := by
      intro i' _ j' _
      by_contra hne
      have hpos : 0 < (∑ k, f k i' * w k j') ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have : 0 < ∑ i', ∑ j', (∑ k, f k i' * w k j') ^ 2 := by
        refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
          ⟨i', mem_univ i', ?_⟩
        exact Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨j', mem_univ j', hpos⟩
      linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp (hz i (mem_univ i) j (mem_univ j))
  · intro h
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [h i j]; ring

end CrossTerm
