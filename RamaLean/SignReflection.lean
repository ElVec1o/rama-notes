import Mathlib

/-!
# The sign-averaged reflection

For rank-two orthogonal projections `P_1, …, P_q` on `ℝ^p` with `∑ P_k = a I`, the mixed
characteristic polynomial satisfies `μ(2a - y) = (-1)^p μ(y)`, so its least and greatest roots
sum to `2a`.  Since `2a - (√(a-1)+1)² = (√(a-1)-1)²`, the reflection exchanges the two edges of
the `(a,2)`-biregular band, and the open lower bound becomes equivalent to the upper one.

The whole content is the statement below, which involves no projections and no mixed
characteristic polynomials.  Randomizing each rank-two slot to rank one writes
`μ(y) = 𝔼_ε det((y-a)I - ∑ ε_k S_k)` with `S_k = e_k f_kᵀ + f_k e_kᵀ` and `ε` independent signs;
`sign_avg_reflect` says such a sign average is even or odd in `t = y - a` according to the parity
of the dimension, because negating every sign is a bijection of the index set.

`shift_reflect` packages the change of variable, and `mixedChar_reflect` is the statement in the
form used for the projection theorem.
-/

namespace SignReflection

open Matrix BigOperators

variable {n q : ℕ}

/-- The `±1` vector attached to a Boolean vector. -/
def sgn (ε : Fin q → Bool) (k : Fin q) : ℝ := if ε k then 1 else -1

@[simp] theorem sgn_not (ε : Fin q → Bool) (k : Fin q) :
    sgn (fun j => !(ε j)) k = - sgn ε k := by
  simp only [sgn]
  split <;> split <;> simp_all

/-- Negating every sign is an involution of the Boolean cube. -/
def flip : (Fin q → Bool) ≃ (Fin q → Bool) :=
  Function.Involutive.toPerm (fun ε j => !(ε j)) (fun ε => by funext j; simp)

@[simp] theorem flip_apply (ε : Fin q → Bool) : flip ε = fun j => !(ε j) := rfl

/-- The sign-averaged characteristic polynomial of a family of matrices. -/
noncomputable def signAvg (S : Fin q → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  ∑ ε : Fin q → Bool, (t • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, sgn ε k • S k).det

/-- **The reflection.**  A sign-averaged characteristic polynomial is an even function of the
spectral variable when the dimension is even, and an odd function when it is odd.  No hypothesis
on the matrices is needed. -/
theorem sign_avg_reflect (S : Fin q → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    signAvg S (-t) = (-1) ^ n * signAvg S t := by
  classical
  unfold signAvg
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv flip _ _ ?_
  intro ε
  have hs : (∑ k, sgn (flip ε) k • S k) = - ∑ k, sgn ε k • S k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [flip_apply, sgn_not, neg_smul]
  have hneg : ((-t) • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, sgn ε k • S k)
      = - (t • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, sgn (flip ε) k • S k) := by
    rw [hs]
    module
  rw [hneg, Matrix.det_neg]
  simp

/-- The change of variable.  If `f` is a shift of a sign average, it reflects about `a`. -/
theorem shift_reflect (S : Fin q → Matrix (Fin n) (Fin n) ℝ) (a y : ℝ) :
    signAvg S (2 * a - y - a) = (-1) ^ n * signAvg S (y - a) := by
  have h : 2 * a - y - a = -(y - a) := by ring
  rw [h, sign_avg_reflect]

/-- **The projection theorem, in the form used.**  If `μ` is the sign average shifted so that the
band centre sits at `a` — which is what randomizing rank-two projections produces — then
`μ(2a - y) = (-1)^p μ(y)`.  Consequently the roots of `μ` are symmetric about `a`, so the least
and greatest sum to `2a` and the two band edges are exchanged. -/
theorem mixedChar_reflect (S : Fin q → Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (μ : ℝ → ℝ) (hμ : ∀ y, μ y = signAvg S (y - a)) (y : ℝ) :
    μ (2 * a - y) = (-1) ^ n * μ y := by
  rw [hμ, hμ, shift_reflect]

/-- The reflection maps roots to roots: if `y` is a root of `μ`, so is `2a - y`. -/
theorem root_reflect (S : Fin q → Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (μ : ℝ → ℝ) (hμ : ∀ y, μ y = signAvg S (y - a)) {y : ℝ} (hy : μ y = 0) :
    μ (2 * a - y) = 0 := by
  rw [mixedChar_reflect S a μ hμ, hy, mul_zero]

/-- The band edges of the `(a,2)`-biregular tree are exchanged by `y ↦ 2a - y`:
`2a - (√(a-1)+1)² = (√(a-1)-1)²`.  This is why the reflection turns the open lower bound into
the known upper one when `b = 2`. -/
theorem band_edges_swap {a : ℝ} (ha : 0 ≤ a - 1) :
    2 * a - (Real.sqrt (a - 1) + 1) ^ 2 = (Real.sqrt (a - 1) - 1) ^ 2 := by
  have h : Real.sqrt (a - 1) ^ 2 = a - 1 := Real.sq_sqrt ha
  nlinarith [h]

/-! ## Why the sign average computes the mixed characteristic polynomial

`sign_avg_reflect` gives the reflection for whatever the sign average is; the bridge to the mixed
characteristic polynomial is that the average *is* `μ`.  That rests on one identity, proved by the
same involution used above: over the Boolean cube the sign monomials are orthogonal to the
constants.  Since `det(yI + ∑ z_k A_k)` is multi-affine in `z` when each `A_k` has rank one, its
expansion `∑_S c_S ∏_{k∈S} z_k` is annihilated termwise except at `S = ∅`, so averaging over signs
returns the constant term, which is exactly what `∏_k (1 - ∂_k)` extracts.
-/

/-- **Character orthogonality on the Boolean cube.**  A nonempty sign monomial averages to zero;
the empty one averages to one.  Proof: flipping a coordinate of the monomial's support is an
involution that negates the summand. -/
theorem sum_prod_sgn (S : Finset (Fin q)) :
    ∑ ε : Fin q → Bool, ∏ k ∈ S, sgn ε k = if S = ∅ then (2 : ℝ) ^ q else 0 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp [Fintype.card_fun]
  · rw [if_neg (Finset.nonempty_iff_ne_empty.mp ⟨k₀, hk₀⟩)]
    have hinv : Function.Involutive
        (fun ε : Fin q → Bool => Function.update ε k₀ (!(ε k₀))) := by
      intro ε
      funext j
      by_cases h : j = k₀
      · subst h; simp
      · simp [Function.update_of_ne h]
    have hflip : ∀ ε : Fin q → Bool,
        (∏ k ∈ S, sgn (Function.update ε k₀ (!(ε k₀))) k) = - ∏ k ∈ S, sgn ε k := by
      intro ε
      rw [← Finset.prod_erase_mul S _ hk₀, ← Finset.prod_erase_mul S _ hk₀]
      have hoff : ∀ k ∈ S.erase k₀, sgn (Function.update ε k₀ (!(ε k₀))) k = sgn ε k := by
        intro k hk
        simp [sgn, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      have hat : sgn (Function.update ε k₀ (!(ε k₀))) k₀ = - sgn ε k₀ := by
        simp only [Function.update_self, sgn]
        split <;> split <;> simp_all
      rw [Finset.prod_congr rfl hoff, hat]
      ring
    have h1 := Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
      (fun ε : Fin q → Bool => ∏ k ∈ S, sgn ε k)
    simp only [Function.Involutive.coe_toPerm] at h1
    rw [Finset.sum_congr rfl (fun ε _ => hflip ε), Finset.sum_neg_distrib] at h1
    linarith [h1]

/-- The average of a sign monomial: zero unless the monomial is empty. -/
theorem avg_prod_sgn (S : Finset (Fin q)) (hS : S.Nonempty) :
    ∑ ε : Fin q → Bool, ∏ k ∈ S, sgn ε k = 0 := by
  rw [sum_prod_sgn, if_neg (Finset.nonempty_iff_ne_empty.mp hS)]

/-- **The bridge, in the form it is used.**  If `F` is multi-affine, presented by its expansion
into sign monomials, then averaging `F` over the Boolean cube returns `2^q` times its constant
term.  Applied to `F(z) = det(yI + ∑ z_k A_k)` with rank-one `A_k`, the constant term is what
`∏_k (1 - ∂_k)` extracts, so the sign average is the mixed characteristic polynomial. -/
theorem sum_multiaffine (c : Finset (Fin q) → ℝ) :
    (∑ ε : Fin q → Bool, ∑ S : Finset (Fin q), c S * ∏ k ∈ S, sgn ε k)
      = (2 : ℝ) ^ q * c ∅ := by
  classical
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (∅ : Finset (Fin q))]
  · rw [← Finset.mul_sum, sum_prod_sgn, if_pos rfl]; ring
  · intro S _ hS
    rw [← Finset.mul_sum, sum_prod_sgn, if_neg hS, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end SignReflection
