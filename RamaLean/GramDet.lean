import Mathlib
import RamaLean.AdjugatePSD

/-!
# The exterior-algebra inputs, in Gram coordinates

The cross-term theorems rest on three facts about multivectors.  Written in Gram
coordinates every one of them becomes a determinant statement, and this file proves
them, so that `CrossTerm`'s hypotheses `hsimple` are discharged rather than assumed.

For decomposable multivectors, `⟨u_1 ∧ ⋯ ∧ u_p, w_1 ∧ ⋯ ∧ w_p⟩ = det (⟨u_i, w_j⟩)`.  So:

* the identity `⟨u ∧ α, w ∧ γ⟩ = ⟨u,w⟩⟨α,γ⟩ - ⟨ι_w α, ι_u γ⟩`, which drives the whole
  computation, is exactly the **bordered determinant formula**

    `det [[a, rᵀ], [c, G]] = a · det G - rᵀ (adj G) c`,                          (†)

  with `a = ⟨u,w⟩`, `r_j = ⟨u, c_j⟩`, `c_i = ⟨a_i, w⟩`, `G_{ij} = ⟨a_i, c_j⟩`;
* `‖f‖²‖α‖² = ‖ι_f α‖² + ‖f ∧ α‖²` for simple `α` is (†) with `u = w = f`, `α = γ`;
* `f_k ∧ ω'_k = 0` is the vanishing of a Gram determinant on a dependent family, since
  `f_k = ι_e ω_k` lies in the plane of `ω'_k`.

Combining the last two gives `‖f_k‖²‖ω'_k‖² = ‖ι_{f_k} ω'_k‖²`, which is precisely the
hypothesis `hsimple` of `CrossTerm.crossTerm_eq_sq`.  That is `hsimple_of_border_zero`
below.

Scope.  (†) is proved for `IsUnit G.det`, which is the case that occurs: `G` is the Gram
matrix of the compressed block, invertible exactly when the block does not degenerate,
and when it does degenerate `ω'_k = 0` and both sides vanish — a case not formalized
here.  The remaining unformalized input to `CrossTerm` is `htight`, that tightness
`Adj(A) = aI` forces `∑_k ι_{f_k} ω'_k = 0`; that is the vanishing of the off-diagonal
block of `Adj(A)`, obtained by polarizing `⟨v, Θ_k v⟩ = ‖ι_v ω_k‖²` across `e` and
`e^⊥`, and it is carried as a hypothesis.
-/

namespace GramDet

open Matrix

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- **The bordered determinant formula.**  For `G` with invertible determinant,
`det [[a, rᵀ], [c, G]] = a · det G - r ⬝ᵥ (adj G *ᵥ c)`.

In Gram coordinates this is the identity
`⟨u ∧ α, w ∧ γ⟩ = ⟨u,w⟩⟨α,γ⟩ - ⟨ι_w α, ι_u γ⟩` that the cross-term computation runs on. -/
theorem det_border {G : Matrix p p ℝ} (hG : IsUnit G.det) (a : ℝ) (r c : p → ℝ) :
    (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => a) (Matrix.replicateRow Unit r)
        (Matrix.replicateCol Unit c) G).det
      = a * G.det - r ⬝ᵥ (G.adjugate *ᵥ c) := by
  classical
  haveI : Invertible G := G.invertibleOfIsUnitDet hG
  rw [Matrix.det_fromBlocks₂₂]
  have h11 : (((Matrix.of fun _ _ : Unit => a) : Matrix Unit Unit ℝ) -
      Matrix.replicateRow Unit r * (⅟G) * Matrix.replicateCol Unit c).det
      = a - r ⬝ᵥ ((⅟G) *ᵥ c) := by
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm]
  rw [h11, mul_sub]
  congr 1
  · ring
  · have hinv : (⅟G : Matrix p p ℝ) = G⁻¹ := by
      simp [Matrix.invOf_eq_nonsing_inv]
    rw [hinv, AdjugatePSD.adjugate_eq_det_smul_inv hG]
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring

/-- **A Gram determinant vanishes on a dependent family.**  If some nonzero combination
of the columns of `M` is zero then `det (Mᵀ M) = 0`.

This is `f_k ∧ ω'_k = 0`: the border `f_k` lies in the plane of `ω'_k`, so the bordered
family is dependent and its Gram determinant vanishes. -/
theorem det_gram_eq_zero_of_dep {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m p ℝ) {x : p → ℝ} (hx : x ≠ 0) (hMx : M *ᵥ x = 0) :
    (Mᵀ * M).det = 0 := by
  have hker : (Mᵀ * M) *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec, hMx, Matrix.mulVec_zero]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩

/-- **The hypothesis `hsimple`, discharged.**  If the bordered Gram determinant vanishes
--- which is `f ∧ ω' = 0` --- then `‖f‖²‖ω'‖² = ‖ι_f ω'‖²`, in the coordinates
`a = ⟨f,f⟩`, `r_i = ⟨f, b_i⟩`, `G = Gram(b)`. -/
theorem hsimple_of_border_zero {G : Matrix p p ℝ} (hG : IsUnit G.det) (a : ℝ) (r : p → ℝ)
    (hzero : (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => a) (Matrix.replicateRow Unit r)
        (Matrix.replicateCol Unit r) G).det = 0) :
    a * G.det = r ⬝ᵥ (G.adjugate *ᵥ r) := by
  have := det_border hG a r r
  rw [hzero] at this
  linarith

/-- The quantity the cross-term computation calls `‖ι_f ω'‖²` is nonnegative, since the
adjugate of a positive definite Gram matrix is positive definite. -/
theorem contraction_sq_nonneg {G : Matrix p p ℝ} (hG : G.PosDef) (r : p → ℝ) :
    0 ≤ r ⬝ᵥ (G.adjugate *ᵥ r) := by
  classical
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hpd := AdjugatePSD.adjugate_posDef hG
    have hquad : 0 < (Finsupp.equivFunOnFinite.symm r).sum fun i ri =>
        (Finsupp.equivFunOnFinite.symm r).sum fun j rj =>
          star ri * G.adjugate i j * rj := by
      refine hpd.2 ?_
      simpa [Finsupp.ext_iff, funext_iff] using hr
    have hq : r ⬝ᵥ (G.adjugate *ᵥ r) = ∑ i, ∑ j, r i * G.adjugate i j * r j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hq]
    simpa [Finsupp.sum_fintype, Finset.mul_sum, mul_assoc] using hquad.le

/-! ### The border vanishes at every level

`hsimple_of_border_zero` needs the bordered Gram determinant to vanish.  That happens
exactly when the border lies in the span of the rest, and here it always does: `f_k` lies
in the plane of `ω'_k`, hence in the span of `ω'_k ∧ ω'_S` for any `S`.  The two lemmas
below turn that into the hypothesis-free form, at **every** level `r`, so that
Theorem `thm:Cr` needs no assumption beyond tightness. -/

/-- The bordered Gram matrix of `[v | M]` is the Gram matrix of the bordered family. -/
theorem border_gram {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m p ℝ) (v : m → ℝ) :
    Matrix.fromBlocks (Matrix.of fun _ _ : Unit => v ⬝ᵥ v)
        (Matrix.replicateRow Unit (Mᵀ *ᵥ v)) (Matrix.replicateCol Unit (Mᵀ *ᵥ v)) (Mᵀ * M)
      = (Matrix.of fun (i : m) (j : Unit ⊕ p) =>
            Sum.elim (fun _ => v i) (fun j' => M i j') j)ᵀ *
        (Matrix.of fun (i : m) (j : Unit ⊕ p) =>
            Sum.elim (fun _ => v i) (fun j' => M i j') j) := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Matrix.fromBlocks, dotProduct, Matrix.mulVec,
      Matrix.vecMul, mul_comm]

/-- **The border always vanishes.**  If `v` is in the column span of `M`, the bordered
Gram determinant is zero — which is `f ∧ ω = 0`. -/
theorem border_det_eq_zero_of_mem_span {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m p ℝ) (y : p → ℝ) :
    (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => (M *ᵥ y) ⬝ᵥ (M *ᵥ y))
        (Matrix.replicateRow Unit (Mᵀ *ᵥ (M *ᵥ y)))
        (Matrix.replicateCol Unit (Mᵀ *ᵥ (M *ᵥ y))) (Mᵀ * M)).det = 0 := by
  classical
  set N : Matrix m (Unit ⊕ p) ℝ := Matrix.of fun (i : m) (j : Unit ⊕ p) =>
    Sum.elim (fun _ => (M *ᵥ y) i) (fun j' => M i j') j with hN
  rw [border_gram M (M *ᵥ y), ← hN]
  refine det_gram_eq_zero_of_dep N (x := Sum.elim (fun _ => (-1 : ℝ)) y) ?_ ?_
  · intro h
    have := congrFun h (Sum.inl ())
    simp at this
  · funext i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hN, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
    simp [Matrix.mulVec, dotProduct]

/-- **`hsimple` at every level, with no hypothesis.**  For `v` in the column span of `M`
and `Mᵀ M` invertible, `‖v‖² det(MᵀM) = rᵀ adj(MᵀM) r` with `r = Mᵀ v` — that is
`‖f‖²‖ω‖² = ‖ι_f ω‖²`. -/
theorem hsimple_of_mem_span {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m p ℝ) (y : p → ℝ) (hG : IsUnit (Mᵀ * M).det) :
    ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) * (Mᵀ * M).det
      = (Mᵀ *ᵥ (M *ᵥ y)) ⬝ᵥ ((Mᵀ * M).adjugate *ᵥ (Mᵀ *ᵥ (M *ᵥ y))) :=
  hsimple_of_border_zero hG _ _ (border_det_eq_zero_of_mem_span M y)

/-! ### Coordinate families are matchings

For a coordinate (graph) family every block is a pair of standard basis vectors, and the
Gram determinant of a set of blocks is `1` when all the indices involved are distinct —
that is, when the set is a matching — and `0` otherwise.  So `‖ω_T‖² = [T is a matching]`,
which is `F_A = μ_G`: the polynomial of a coordinate family is the matching polynomial.
That is the first of the two inputs to the Kesten–McKay identification, and it is proved
here; the second, the Kesten–McKay limit itself, is analytic and is cited. -/

/-- The matrix whose `j`-th column is the standard basis vector `e_{c j}`. -/
def basisCols {m : Type*} [DecidableEq m] (c : p → m) : Matrix m p ℝ :=
  Matrix.of fun i j => if i = c j then 1 else 0

theorem gram_basisCols {m : Type*} [Fintype m] [DecidableEq m] (c : p → m) (j l : p) :
    ((basisCols c)ᵀ * basisCols c) j l = if c j = c l then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisCols, Matrix.of_apply]
  by_cases h : c j = c l
  · simp [h, Finset.sum_ite_eq' Finset.univ (c l) (fun _ => (1:ℝ))]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i = c j <;> by_cases h2 : i = c l <;> simp_all

/-- **A matching contributes `1`.**  If the indices are distinct the Gram matrix is the
identity. -/
theorem gram_det_basis_of_injective {m : Type*} [Fintype m] [DecidableEq m]
    {c : p → m} (hc : Function.Injective c) :
    ((basisCols c)ᵀ * basisCols c).det = 1 := by
  have : (basisCols c)ᵀ * basisCols c = (1 : Matrix p p ℝ) := by
    ext j l
    rw [gram_basisCols, Matrix.one_apply]
    by_cases h : j = l
    · simp [h]
    · rw [if_neg (fun hcc => h (hc hcc)), if_neg h]
  rw [this, Matrix.det_one]

/-- **A non-matching contributes `0`.**  If two indices coincide the family is dependent. -/
theorem gram_det_basis_of_not_injective {m : Type*} [Fintype m] [DecidableEq m]
    {c : p → m} {j l : p} (hjl : j ≠ l) (hc : c j = c l) :
    ((basisCols c)ᵀ * basisCols c).det = 0 := by
  classical
  refine det_gram_eq_zero_of_dep (basisCols c)
    (x := fun t => if t = j then 1 else if t = l then -1 else 0) ?_ ?_
  · intro h
    have := congrFun h j
    simp at this
  · funext i
    simp only [Matrix.mulVec, dotProduct, basisCols, Matrix.of_apply, Pi.zero_apply]
    rw [Finset.sum_eq_add_of_mem j l (Finset.mem_univ j) (Finset.mem_univ l) hjl]
    · rw [if_pos rfl, if_neg (Ne.symm hjl), if_pos rfl, hc]
      ring
    · intro t _ ht
      rw [if_neg ht.1, if_neg ht.2, mul_zero]

end GramDet
