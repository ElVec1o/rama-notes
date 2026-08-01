import Mathlib
import RamaLean.CrossTerm

/-!
# Tightness kills the contraction sum

This is the last input to the cross-term theorems that was carried as a hypothesis.
`CrossTerm.crossTerm_eq_sq` assumes `htight : ∑ k, u k = 0`, where
`u_k = ι_{f_k} ω'_k`; the geometric reason is that `∑_k u_k` is the off-diagonal
`(e, e^⊥)` block of `Adj(A) = ∑_k Θ_k`, so `Adj(A) = a I` forces it to vanish.  Here that
is proved.

Everything is written in coordinates, with a rank-two block presented by its two spanning
vectors, so no exterior algebra is needed:

  `ι_v (b₁ ∧ b₂) = ⟨v,b₁⟩ b₂ - ⟨v,b₂⟩ b₁`,   `Θ_k(u,v) = ⟨ι_u ω_k, ι_v ω_k⟩`.

The proof is three steps.  `iota_antisymm`, that `⟨a, ι_b ω⟩ = -⟨b, ι_a ω⟩`, is a two-term
`ring` identity in these coordinates.  `iota_proj_of_orthogonal` says that compressing the
block to `e^⊥` does not change the pairing against `f_k`, because the discrepancy is a
multiple of `e` and `f_k ⊥ e`.  Together they turn `Θ_k(e,v)` into `-⟨v, u_k⟩` for every
`v ⊥ e`, so tightness gives `⟨v, ∑_k u_k⟩ = 0` there; and each `u_k` already lies in
`e^⊥`, so `∑_k u_k = 0`.

`tight_sum_contraction_eq_zero` is the statement in the form `CrossTerm` consumes.
-/

namespace Tightness

open Matrix Finset

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- `ι_v (b₁ ∧ b₂) = ⟨v,b₁⟩ b₂ - ⟨v,b₂⟩ b₁`. -/
def iota (v b1 b2 : n → ℝ) : n → ℝ := (v ⬝ᵥ b1) • b2 - (v ⬝ᵥ b2) • b1

/-- The component of `b` orthogonal to a unit vector `e`. -/
def proj (e b : n → ℝ) : n → ℝ := b - (e ⬝ᵥ b) • e

@[simp] theorem dot_iota (a v b1 b2 : n → ℝ) :
    a ⬝ᵥ iota v b1 b2 = (v ⬝ᵥ b1) * (a ⬝ᵥ b2) - (v ⬝ᵥ b2) * (a ⬝ᵥ b1) := by
  simp [iota, dotProduct_sub, dotProduct_smul]

@[simp] theorem iota_dot (a v b1 b2 : n → ℝ) :
    iota v b1 b2 ⬝ᵥ a = (v ⬝ᵥ b1) * (a ⬝ᵥ b2) - (v ⬝ᵥ b2) * (a ⬝ᵥ b1) := by
  rw [dotProduct_comm]; exact dot_iota a v b1 b2

/-- **Antisymmetry of the contraction pairing.**  `⟨a, ι_b ω⟩ = -⟨b, ι_a ω⟩`. -/
theorem iota_antisymm (a b b1 b2 : n → ℝ) :
    a ⬝ᵥ iota b b1 b2 = -(b ⬝ᵥ iota a b1 b2) := by
  simp only [dot_iota]
  rw [dotProduct_comm a b1, dotProduct_comm a b2]
  ring

/-- A contraction is orthogonal to the vector contracted with. -/
theorem dot_self_iota (v b1 b2 : n → ℝ) : v ⬝ᵥ iota v b1 b2 = 0 := by
  have := iota_antisymm v v b1 b2
  linarith

/-- The compressed block spans inside `e^⊥`, so any contraction of it does too. -/
theorem dot_e_iota_proj (e v b1 b2 : n → ℝ) (he : e ⬝ᵥ e = 1) :
    e ⬝ᵥ iota v (proj e b1) (proj e b2) = 0 := by
  have hp : ∀ b : n → ℝ, e ⬝ᵥ proj e b = 0 := by
    intro b
    simp [proj, dotProduct_sub, dotProduct_smul, he]
  simp [iota, dotProduct_sub, dotProduct_smul, hp]

/-- **Compression does not change the pairing against `f`.**  If `v` and `f` are both
orthogonal to the unit vector `e`, then contracting the compressed block against `v` and
pairing with `f` gives the same as contracting the original block. -/
theorem iota_proj_of_orthogonal (e v f b1 b2 : n → ℝ) (he : e ⬝ᵥ e = 1)
    (hv : e ⬝ᵥ v = 0) (hf : e ⬝ᵥ f = 0) :
    f ⬝ᵥ iota v (proj e b1) (proj e b2) = f ⬝ᵥ iota v b1 b2 := by
  have hvb : ∀ b : n → ℝ, v ⬝ᵥ proj e b = v ⬝ᵥ b := by
    intro b
    have : v ⬝ᵥ ((e ⬝ᵥ b) • e) = 0 := by
      rw [dotProduct_smul, dotProduct_comm v e, hv, smul_zero]
    simp [proj, dotProduct_sub, this]
  have hfb : ∀ b : n → ℝ, f ⬝ᵥ proj e b = f ⬝ᵥ b := by
    intro b
    have : f ⬝ᵥ ((e ⬝ᵥ b) • e) = 0 := by
      rw [dotProduct_smul, dotProduct_comm f e, hf, smul_zero]
    simp [proj, dotProduct_sub, this]
  simp only [dot_iota, hvb, hfb]

/-- **Tightness kills the contraction sum.**

`htight` is `Adj(A) = a I` in polarized form: the bilinear form
`∑_k ⟨ι_u ω_k, ι_v ω_k⟩` is `a ⟨u,v⟩`.  The conclusion is the hypothesis `htight` of
`CrossTerm.crossTerm_eq_sq`, namely that `∑_k ι_{f_k} ω'_k = 0` with `f_k = ι_e ω_k` and
`ω'_k` the block compressed to `e^⊥`. -/
theorem tight_sum_contraction_eq_zero (e : n → ℝ) (he : e ⬝ᵥ e = 1)
    (b1 b2 : ι → n → ℝ) (a : ℝ)
    (htight : ∀ u v : n → ℝ,
      (∑ k, (iota u (b1 k) (b2 k)) ⬝ᵥ (iota v (b1 k) (b2 k))) = a * (u ⬝ᵥ v)) :
    (∑ k, iota (iota e (b1 k) (b2 k)) (proj e (b1 k)) (proj e (b2 k))) = 0 := by
  classical
  set f : ι → n → ℝ := fun k => iota e (b1 k) (b2 k) with hf
  set u : ι → n → ℝ := fun k => iota (f k) (proj e (b1 k)) (proj e (b2 k)) with hu
  have hfe : ∀ k, e ⬝ᵥ f k = 0 := fun k => dot_self_iota e (b1 k) (b2 k)
  have hue : ∀ k, e ⬝ᵥ u k = 0 := fun k => dot_e_iota_proj e (f k) (b1 k) (b2 k) he
  -- every test vector orthogonal to `e` annihilates the sum
  have key : ∀ v : n → ℝ, e ⬝ᵥ v = 0 → v ⬝ᵥ (∑ k, u k) = 0 := by
    intro v hv
    have hterm : ∀ k, v ⬝ᵥ u k = -((f k) ⬝ᵥ iota v (b1 k) (b2 k)) := by
      intro k
      rw [hu]
      rw [iota_antisymm v (f k) (proj e (b1 k)) (proj e (b2 k))]
      rw [iota_proj_of_orthogonal e v (f k) (b1 k) (b2 k) he hv (hfe k)]
    have hsum : (∑ k, v ⬝ᵥ u k) = -(∑ k, (f k) ⬝ᵥ iota v (b1 k) (b2 k)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => hterm k
    have hT := htight e v
    have hTe : (∑ k, (f k) ⬝ᵥ iota v (b1 k) (b2 k)) = a * (e ⬝ᵥ v) := by
      simpa [hf] using hT
    rw [dotProduct_sum]
    rw [hsum, hTe, hv, mul_zero, neg_zero]
  -- and `e` itself does too, so the sum is orthogonal to everything
  have hall : ∀ w : n → ℝ, w ⬝ᵥ (∑ k, u k) = 0 := by
    intro w
    have hsplit : w = (e ⬝ᵥ w) • e + (w - (e ⬝ᵥ w) • e) := by abel
    have hperp : e ⬝ᵥ (w - (e ⬝ᵥ w) • e) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, he, smul_eq_mul, mul_one,
        dotProduct_comm e w, sub_self]
    have he0 : e ⬝ᵥ (∑ k, u k) = 0 := by
      rw [dotProduct_sum]
      exact Finset.sum_eq_zero fun k _ => hue k
    calc w ⬝ᵥ (∑ k, u k)
        = ((e ⬝ᵥ w) • e + (w - (e ⬝ᵥ w) • e)) ⬝ᵥ (∑ k, u k) := by rw [← hsplit]
      _ = (e ⬝ᵥ w) * (e ⬝ᵥ (∑ k, u k)) + (w - (e ⬝ᵥ w) • e) ⬝ᵥ (∑ k, u k) := by
          rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
      _ = 0 := by rw [he0, mul_zero, key _ hperp, add_zero]
  funext i
  have := hall (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using this

/-- **The compression splits the contraction form.**  For `u, v` orthogonal to the unit
vector `e`, the contraction form of a block splits into its `e`-part and the form of the
compressed block. -/
theorem iota_split (e u v b1 b2 : n → ℝ) (he : e ⬝ᵥ e = 1)
    (hu : e ⬝ᵥ u = 0) (hv : e ⬝ᵥ v = 0) :
    (iota u b1 b2) ⬝ᵥ (iota v b1 b2)
      = (u ⬝ᵥ iota e b1 b2) * (v ⬝ᵥ iota e b1 b2)
        + (iota u (proj e b1) (proj e b2)) ⬝ᵥ (iota v (proj e b1) (proj e b2)) := by
  have hub : ∀ b : n → ℝ, u ⬝ᵥ proj e b = u ⬝ᵥ b := by
    intro b
    have h0 : u ⬝ᵥ ((e ⬝ᵥ b) • e) = 0 := by
      rw [dotProduct_smul, dotProduct_comm u e, hu, smul_zero]
    simp [proj, dotProduct_sub, h0]
  have hvb : ∀ b : n → ℝ, v ⬝ᵥ proj e b = v ⬝ᵥ b := by
    intro b
    have h0 : v ⬝ᵥ ((e ⬝ᵥ b) • e) = 0 := by
      rw [dotProduct_smul, dotProduct_comm v e, hv, smul_zero]
    simp [proj, dotProduct_sub, h0]
  have hbb : ∀ c d : n → ℝ, (proj e c) ⬝ᵥ (proj e d)
      = c ⬝ᵥ d - (e ⬝ᵥ c) * (e ⬝ᵥ d) := by
    intro c d
    simp only [proj, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, he]
    rw [dotProduct_comm e c]
    ring
  simp only [dot_iota, iota_dot, hub, hvb, hbb]
  rw [dotProduct_comm b2 b1]
  ring

/-- **The compressed family is deficient by exactly `F = ∑_k f_k f_kᵀ`.**  If
`Adj(A) = a I` then `Adj(A^(e)) = a I - F` on `e^⊥`, and `tr F = ⟨e, Adj(A) e⟩ = a`.  So
the class is *not* closed under compression in the tight sense: compressing costs exactly
a rank-`≤ q` positive semidefinite matrix of trace `a`, and that deficiency is what a
sharpened induction can spend. -/
theorem adj_compressed (e : n → ℝ) (he : e ⬝ᵥ e = 1) (b1 b2 : ι → n → ℝ) (a : ℝ)
    (htight : ∀ u v : n → ℝ,
      (∑ k, (iota u (b1 k) (b2 k)) ⬝ᵥ (iota v (b1 k) (b2 k))) = a * (u ⬝ᵥ v))
    (u v : n → ℝ) (hu : e ⬝ᵥ u = 0) (hv : e ⬝ᵥ v = 0) :
    (∑ k, (iota u (proj e (b1 k)) (proj e (b2 k)))
            ⬝ᵥ (iota v (proj e (b1 k)) (proj e (b2 k))))
      = a * (u ⬝ᵥ v)
        - ∑ k, (u ⬝ᵥ iota e (b1 k) (b2 k)) * (v ⬝ᵥ iota e (b1 k) (b2 k)) := by
  have hsplit : ∀ k, (iota u (proj e (b1 k)) (proj e (b2 k)))
      ⬝ᵥ (iota v (proj e (b1 k)) (proj e (b2 k)))
      = (iota u (b1 k) (b2 k)) ⬝ᵥ (iota v (b1 k) (b2 k))
        - (u ⬝ᵥ iota e (b1 k) (b2 k)) * (v ⬝ᵥ iota e (b1 k) (b2 k)) := by
    intro k
    have := iota_split e u v (b1 k) (b2 k) he hu hv
    linarith
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_sub_distrib, htight u v]

/-- **The chain, closed.**  Composing `tight_sum_contraction_eq_zero` with
`CrossTerm.crossTerm_nonneg`: for a tight family of rank-two blocks and any unit `e`, the
leading cross term is nonnegative.  The only remaining input is `hsimple`, which
`GramDet.hsimple_of_border_zero` supplies. -/
theorem crossTerm_nonneg_of_tight {p : Type*} [Fintype p] [DecidableEq ι]
    (e : n → ℝ) (he : e ⬝ᵥ e = 1) (b1 b2 : ι → n → ℝ) (a : ℝ) (w : ι → p → ℝ)
    (htight : ∀ u v : n → ℝ,
      (∑ k, (iota u (b1 k) (b2 k)) ⬝ᵥ (iota v (b1 k) (b2 k))) = a * (u ⬝ᵥ v))
    (hsimple : ∀ k,
      ((iota e (b1 k) (b2 k)) ⬝ᵥ (iota e (b1 k) (b2 k))) * (w k ⬝ᵥ w k)
        = (iota (iota e (b1 k) (b2 k)) (proj e (b1 k)) (proj e (b2 k)))
          ⬝ᵥ (iota (iota e (b1 k) (b2 k)) (proj e (b1 k)) (proj e (b2 k)))) :
    0 ≤ ∑ k, ∑ l ∈ Finset.univ.erase k,
        (((iota e (b1 k) (b2 k)) ⬝ᵥ (iota e (b1 l) (b2 l))) * (w k ⬝ᵥ w l)
         - (iota (iota e (b1 k) (b2 k)) (proj e (b1 k)) (proj e (b2 k)))
           ⬝ᵥ (iota (iota e (b1 l) (b2 l)) (proj e (b1 l)) (proj e (b2 l)))) :=
  CrossTerm.crossTerm_nonneg _ w _ hsimple
    (tight_sum_contraction_eq_zero e he b1 b2 a htight)

end Tightness
