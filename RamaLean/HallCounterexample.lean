import Mathlib

/-!
# Hall's counterexample to Conjecture 10

**The counterexample is due to Chris Hall** (personal communication, August 2026); the
construction and the algebraic certificate are his.  This file formalizes the parts of his
verification note that are pure algebra, so that the conclusion rests only on one classical
input and on two combinatorial facts stated explicitly below.

## The graph

Five copies of `K_{2,5}`; in copy `i` the two degree-five vertices are `v_i, w_i`; a pendant
leaf `ℓ_i` is attached to `w_i`; a central vertex `c` is joined to every `v_i`.  Simple,
connected, loopless, bipartite, `41` vertices, `60` edges, first Betti number `20`.

## What is proved here

* **Part A.**  From the two rooted branch polynomials and the vertex-deletion recurrence,
  `μ_G = X²¹ (X⁴ - 11X² + 25)⁴ (X² - 5)(X² - 11)`, so `√5` is a root, and it is a **simple**
  root.  This is Proposition 3.2 of the note, as an identity in `ℤ[X]`.
* **Part B.**  The eight ratio identities of Table 1 hold exactly, in the division-free form
  `r_e (λ - ∑_{e→f} r_f) = 1`.
* **Part C.**  A Collatz–Wielandt bound: a nonnegative matrix admitting a positive strictly
  subinvariant vector has all eigenvalues of modulus `< 1`.  This is the general fact behind
  Proposition 6.1 and is proved here in full.
* **Part D.**  The six components of `x - Kx` are strictly positive for
  `x = (20,121,47,33,28,16)`, using only `s² = 41` and `s > 0`.
* **Part E.**  The assembly: the two halves are logically independent and together refute the
  inclusion.

## What is *not* proved here, and is flagged rather than hidden

1. That the combinatorially defined matching polynomial of the branch equals `X⁵(X² - 6)` and
   `X⁴(X² - 5)` after the stated deletions, and that the vertex-deletion recurrence holds.
   These are classical (`μ_G = X μ_{G-v} - ∑_{u∼v} μ_{G-v-u}`) and enter Part A as the
   defining equations.
2. That the orbit quotient `K` is the correct `6 × 6` reduction of the `120`-state decay
   matrix, and that `ρ(K) = α(r)`.  Verified computationally in `code/hall_certificate.py`,
   which ships: it rebuilds the decay digraph from the graph, finds the strongly connected
   components (one recurrent block of exactly `110` states, ten transient, the transient ones
   being exactly the leaf-incident directed edges), reconstructs `K` from follower counts, and
   checks that the six components of `x - Kx` reproduce the exact expressions of `residual_pos`
   below to `3e-14`, with `ρ(K) = 0.9636233789`.  This was previously done only in `private/`,
   which never ships, and was the one step of the certificate a reader could not check.
3. **Angel–Friedman–Hoory**, Trans. AMS 367 (2015) 4287–4318, Theorem 1.4: a finite nonzero
   ratio system with decay rate `< 1` is equivalent to `A_T - λI` having a bounded inverse.
   Not in Mathlib; enters Part E as an explicit hypothesis in the shape it is consumed.

The numerical value `ρ(K) ≈ 0.9636233789` is nowhere used.
-/

namespace HallCounterexample

open Polynomial

/-! ## Part A: the matching polynomial -/

/-- `μ_{H-v}`, the star `K_{1,6}`. -/
noncomputable def muHv : ℤ[X] := X ^ 5 * (X ^ 2 - 6)

/-- `μ_{H-v-u_j}`, the star `K_{1,5}`. -/
noncomputable def muHvu : ℤ[X] := X ^ 4 * (X ^ 2 - 5)

/-- The branch polynomial, by the deletion recurrence at `v`, whose five neighbours other
than the leaf side are the `u_{i,j}`. -/
noncomputable def muH : ℤ[X] := X * muHv - 5 * muHvu

/-- The whole graph, by the deletion recurrence at the central vertex `c`. -/
noncomputable def muG : ℤ[X] := X * muH ^ 5 - 5 * muHv * muH ^ 4

theorem muH_eq : muH = X ^ 4 * (X ^ 4 - 11 * X ^ 2 + 25) := by
  simp only [muH, muHv, muHvu]; ring

/-- **Proposition 3.2 of the note.** -/
theorem muG_eq :
    muG = X ^ 21 * (X ^ 4 - 11 * X ^ 2 + 25) ^ 4 * (X ^ 2 - 5) * (X ^ 2 - 11) := by
  simp only [muG, muHv, muH_eq]; ring

/-- The cofactor of `X² - 5` in `μ_G`. -/
noncomputable def muGco : ℤ[X] := X ^ 21 * (X ^ 4 - 11 * X ^ 2 + 25) ^ 4 * (X ^ 2 - 11)

theorem muG_factor : muG = (X ^ 2 - 5) * muGco := by
  rw [muG_eq, muGco]; ring

/-- `√5` is a root of `μ_G`. -/
theorem muG_root_sqrt5 : aeval (Real.sqrt 5) muG = 0 := by
  have h5 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hfac : aeval (Real.sqrt 5) ((X : ℤ[X]) ^ 2 - 5) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_ofNat]
    rw [h5]; ring
  rw [muG_factor, map_mul, hfac, zero_mul]

/-- The root is simple: the cofactor does not vanish at `√5`.  Its value is
`√5²¹ · (-5)⁴ · (-6)`, which is negative. -/
theorem muG_root_simple : aeval (Real.sqrt 5) muGco ≠ 0 := by
  have h5 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h4 : (Real.sqrt 5 : ℝ) ^ 4 = 25 := by nlinarith [h5]
  have hp : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hval : aeval (Real.sqrt 5) muGco = Real.sqrt 5 ^ 21 * (-5 : ℝ) ^ 4 * (-6) := by
    simp only [muGco, map_mul, map_pow, map_sub, map_add, map_ofNat, aeval_X]
    rw [h4, h5]; ring
  rw [hval]
  have h21 : (0 : ℝ) < Real.sqrt 5 ^ 21 := pow_pos hp 21
  nlinarith [h21]

/-! ## Part B: the eight ratio identities -/

section Ratios

variable {lam s : ℝ} (hl : lam ^ 2 = 5) (hlp : 0 < lam) (hs : s ^ 2 = 41) (hsp : 0 < s)

/-- The eight ratios of Table 1, as functions of `λ` and `s = √41`. -/
noncomputable def rA (lam s : ℝ) : ℝ := (21 + s) / (10 * lam)
noncomputable def rB (lam s : ℝ) : ℝ := (2 * s - 17) / (5 * lam)
noncomputable def rC (lam s : ℝ) : ℝ := (19 + s) / (40 * lam)
noncomputable def rD (lam s : ℝ) : ℝ := 5 * (13 + s) / (64 * lam)
noncomputable def rE (lam s : ℝ) : ℝ := 5 * (s - 11) / (8 * lam)
noncomputable def rF (lam s : ℝ) : ℝ := (51 + s) / (40 * lam)
noncomputable def rL (lam : ℝ) : ℝ := 1 / lam
noncomputable def rN (lam s : ℝ) : ℝ := (s - 11) / (2 * lam)

include hl hlp hs hsp

/-- Type `A`: `c → v`, followers `5C`. -/
theorem eq_A : rA lam s * (lam - 5 * rC lam s) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rA, rC]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- Type `B`: `v → c`, followers `4A`. -/
theorem eq_B : rB lam s * (lam - 4 * rA lam s) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rA, rB]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- Type `C`: `v → u`, follower `E`. -/
theorem eq_C : rC lam s * (lam - rE lam s) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rC, rE]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- Type `D`: `u → v`, followers `B + 4C`. -/
theorem eq_D : rD lam s * (lam - (rB lam s + 4 * rC lam s)) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rB, rC, rD]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- Type `E`: `u → w`, followers `4F + L`. -/
theorem eq_E : rE lam s * (lam - (4 * rF lam s + rL lam)) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rE, rF, rL]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- Type `F`: `w → u`, follower `D`. -/
theorem eq_F : rF lam s * (lam - rD lam s) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rD, rF]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- Type `L`: `w → ℓ`, no followers. -/
theorem eq_L : rL lam * (lam - 0) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rL, sub_zero]
  field_simp

/-- Type `N`: `ℓ → w`, followers `5F`. -/
theorem eq_N : rN lam s * (lam - 5 * rF lam s) = 1 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  simp only [rF, rN]
  field_simp
  nlinarith [hl, hs, sq_nonneg lam, sq_nonneg s]

/-- All eight ratios are nonzero, as a finite nonzero ratio system requires. -/
theorem ratios_ne_zero :
    rA lam s ≠ 0 ∧ rB lam s ≠ 0 ∧ rC lam s ≠ 0 ∧ rD lam s ≠ 0 ∧
      rE lam s ≠ 0 ∧ rF lam s ≠ 0 ∧ rL lam ≠ 0 ∧ rN lam s ≠ 0 := by
  have hne : lam ≠ 0 := ne_of_gt hlp
  have h6 : 6 < s := by nlinarith [hs, hsp]
  have h7 : s < 7 := by nlinarith [hs, hsp]
  have hden : ∀ k : ℝ, k ≠ 0 → k * lam ≠ 0 := fun k hk => mul_ne_zero hk hne
  refine ⟨div_ne_zero (by linarith) (hden 10 (by norm_num)),
          div_ne_zero (by linarith) (hden 5 (by norm_num)),
          div_ne_zero (by linarith) (hden 40 (by norm_num)),
          div_ne_zero (by linarith) (hden 64 (by norm_num)),
          div_ne_zero (by linarith) (hden 8 (by norm_num)),
          div_ne_zero (by linarith) (hden 40 (by norm_num)),
          one_div_ne_zero hne,
          div_ne_zero (by linarith) (hden 2 (by norm_num))⟩

end Ratios

/-! ## Part C: Collatz–Wielandt -/

/-- **A nonnegative matrix with a positive strictly subinvariant vector is a contraction.**
If `K ≥ 0`, `x > 0` and `K x ≤ θ x` componentwise, then every eigenvalue of `K` has modulus
at most `θ`.  This is the general fact behind Proposition 6.1: taking `θ < 1` gives
`ρ(K) < 1`, which is the hypothesis of the Angel–Friedman–Hoory criterion. -/
theorem eigenvalue_le_of_subinvariant {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (xv : ι → ℝ) (hx : ∀ i, 0 < xv i) (θ : ℝ)
    (hsub : ∀ i, ∑ j, K i j * xv j ≤ θ * xv i)
    (μ : ℂ) (v : ι → ℂ) (hv : ∃ i, v i ≠ 0)
    (heig : ∀ i, ∑ j, (K i j : ℂ) * v j = μ * v i) :
    ‖μ‖ ≤ θ := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun i => ‖v i‖ / xv i) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set t := ‖v i₀‖ / xv i₀ with ht
  have hbound : ∀ j, ‖v j‖ ≤ t * xv j := by
    intro j
    have hxj : xv j ≠ 0 := (hx j).ne'
    calc ‖v j‖ = ‖v j‖ / xv j * xv j := by field_simp
      _ ≤ t * xv j :=
          mul_le_mul_of_nonneg_right (hi₀.2 j (Finset.mem_univ j)) (le_of_lt (hx j))
  have htpos : 0 < t := by
    obtain ⟨i, hi⟩ := hv
    have h1 : 0 < ‖v i‖ := norm_pos_iff.mpr hi
    have h2 : ‖v i‖ / xv i ≤ t := hi₀.2 i (Finset.mem_univ i)
    exact lt_of_lt_of_le (div_pos h1 (hx i)) h2
  have hkey : ‖μ‖ * ‖v i₀‖ ≤ θ * (t * xv i₀) := by
    have h1 : ‖μ * v i₀‖ ≤ ∑ j, K i₀ j * ‖v j‖ := by
      rw [← heig i₀]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK i₀ j)]
    have h2 : ∑ j, K i₀ j * ‖v j‖ ≤ ∑ j, K i₀ j * (t * xv j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hK i₀ j)
    have h3 : ∑ j, K i₀ j * (t * xv j) = t * ∑ j, K i₀ j * xv j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    calc ‖μ‖ * ‖v i₀‖ = ‖μ * v i₀‖ := (norm_mul _ _).symm
      _ ≤ ∑ j, K i₀ j * ‖v j‖ := h1
      _ ≤ ∑ j, K i₀ j * (t * xv j) := h2
      _ = t * ∑ j, K i₀ j * xv j := h3
      _ ≤ t * (θ * xv i₀) := mul_le_mul_of_nonneg_left (hsub i₀) (le_of_lt htpos)
      _ = θ * (t * xv i₀) := by ring
  have hxi : xv i₀ ≠ 0 := (hx i₀).ne'
  have hvi : ‖v i₀‖ = t * xv i₀ := by rw [ht]; field_simp
  rw [hvi] at hkey
  have hpos : 0 < t * xv i₀ := mul_pos htpos (hx i₀)
  exact le_of_mul_le_mul_right (by linarith) hpos

/-! ## Part D: the componentwise certificate -/

section Perron

variable {s : ℝ} (hs : s ^ 2 = 41) (hsp : 0 < s)

include hs hsp

/-- The elementary bounds the note uses. -/
theorem sqrt41_bounds : (32 : ℝ) / 5 < s ∧ s < 13 / 2 := by
  constructor <;> nlinarith [hs, hsp]

/-- **Proposition 6.1, componentwise.**  With `x = (20,121,47,33,28,16)` the six entries of
`x - Kx` in equation (20) of the note are strictly positive.  Listed in the order
`A, B, C, D, E, F`. -/
theorem residual_pos :
    0 < (6553 - 893 * s) / 800 ∧
    0 < (1097 - 168 * s) / 25 ∧
    0 < (385 * s - 2459) / 8 ∧
    0 < (64931 * s - 414951) / 1000 ∧
    0 < (858 - 102 * s) / 125 ∧
    0 < (15443 - 2145 * s) / 2048 := by
  obtain ⟨h1, h2⟩ := sqrt41_bounds hs hsp
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Perron

/-! ## Part E: the assembly -/

/-- **Conjecture 10 is false.**  Stated so that the two halves are visibly independent: one
value is a root of the matching polynomial, and the same value is outside the spectrum of the
universal cover.  The second half is supplied by Angel–Friedman–Hoory from the certificate of
Parts B, C, D and enters here as the hypothesis `hspec`. -/
theorem conj10_false {Spec : Set ℝ} {mu : ℝ → ℝ} {x : ℝ}
    (hroot : mu x = 0) (hspec : x ∉ Spec) :
    ¬ (∀ y, mu y = 0 → y ∈ Spec) :=
  fun h => hspec (h x hroot)

/-- The instance: `x = √5`, `mu = μ_G`. -/
theorem conj10_false_at_sqrt5 {Spec : Set ℝ} (hspec : Real.sqrt 5 ∉ Spec) :
    ¬ (∀ y, aeval y muG = 0 → y ∈ Spec) :=
  conj10_false muG_root_sqrt5 hspec

end HallCounterexample
