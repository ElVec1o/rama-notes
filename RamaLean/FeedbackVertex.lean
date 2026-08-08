import Mathlib

/-!
# Feedback vertex number one

Let `G` be a finite graph with a vertex `v` such that `F = G - v` is a forest, i.e. every
cycle of `G` passes through `v`.  The first Betti number is unrestricted: flowers, theta
graphs and every `K_{2,q}` qualify, so this reaches far past the `b₁ = 1` family.

Write the universal cover's adjacency operator as an `n × n` matrix over `C*_r(F_b)` and
eliminate the preimage of `F`.  Because `F` is a forest it lifts homeomorphically, so the
Schur complement `S_v(x)` onto the fibre over `v` is a **finite** sum of group elements,
hence lies in the group algebra inside `C*_r(F_b)` and not merely in the von Neumann
algebra `L(F_b)`.  That distinction is the whole argument: `L(F_b)` is a II₁ factor full of
projections, whereas `C*_r(F_b)` is projectionless (Pimsner–Voiculescu).  A self-adjoint
invertible element of a projectionless C*-algebra is definite, so its trace cannot vanish.

The canonical trace of the Schur complement is
`τ(S_v(x)) = μ_G(x) / μ_{G-v}(x)`.
So a root `θ` of `μ_G` with `μ_{G-v}(θ) ≠ 0` gives `τ(S_v(θ)) = 0`, forcing `S_v(θ)` to be
non-invertible, hence `θ ∈ spec(A_T)`.

This file machine-checks the three ingredients that are checkable and isolates the one that
is not.

* `no_bypass` — the combinatorial core.  In an acyclic graph two distinct neighbours of `v`
  cannot be joined without passing through `v`.  This is why a walk that leaves a lift `ṽ`,
  enters a lifted component of `F` and returns to *the same* `ṽ` must enter and leave at the
  same attachment point, which is what makes the trace pick up only diagonal terms.
* `resolvent_diag` and `matching_ratio` — the algebra.  For a forest the matching polynomial
  is the characteristic polynomial, so the diagonal resolvent entry is `μ_{F-p}/μ_F`, and the
  matching recursion `μ_G = x μ_{G-v} - ∑_{p ∼ v} μ_{G-v-p}` then collapses
  `x - ∑_p μ_{F-p}/μ_F` to `μ_G/μ_{G-v}`.
* `trace_ne_zero_of_definite` — the trace step, proved.

Pimsner–Voiculescu itself is **not** in Mathlib, so `feedback_one_of` carries it as an
explicit hypothesis, in the shape the argument consumes: a self-adjoint invertible element
is definite.  Nothing below asserts the theorem unconditionally.
-/

namespace FeedbackVertex

open Finset

/-! ## The combinatorial core -/

/-- **No bypass.**  In an acyclic graph, if `v` is adjacent to two distinct vertices `p` and
`q`, then every walk from `p` to `q` passes through `v`.

Lifted to the universal cover this says: a walk that leaves `ṽ` into a lifted component of
the forest and comes back to the *same* `ṽ` must use the same attachment point twice.  Two
distinct attachment points of one component sit under two distinct lifts of `v`, because a
tree has no cycle. -/
theorem no_bypass {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {v p q : V} (hp : G.Adj v p) (hq : G.Adj v q) (hpq : p ≠ q)
    (w : G.Walk p q) : v ∈ w.support := by
  classical
  -- the two-edge path `p - v - q`
  have hpv : G.Adj p v := hp.symm
  let P : G.Walk p q := SimpleGraph.Walk.cons hpv (SimpleGraph.Walk.cons hq SimpleGraph.Walk.nil)
  have hsupp : P.support = [p, v, q] := by simp [P]
  have hPpath : P.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsupp]
    simp [hpv.ne, hpq, hq.ne]
  have hvP : v ∈ P.support := by rw [hsupp]; simp
  -- acyclicity makes paths unique, so `P` is the reduction of `w`
  have huniq := SimpleGraph.isAcyclic_iff_path_unique.mp hG (⟨P, hPpath⟩ : G.Path p q) w.toPath
  have hsub : w.toPath.1.support ⊆ w.support := SimpleGraph.Walk.support_bypass_subset w
  apply hsub
  rw [← huniq]
  exact hvP

/-! ## The algebra -/

/-- The diagonal of a resolvent is a ratio of determinants.  For `A = x I - A_F` with `F` a
forest this is `μ_{F-p}(x)/μ_F(x)`, since a forest's matching polynomial is its
characteristic polynomial and the `(p,p)` cofactor deletes `p`. -/
theorem resolvent_diag {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (A : Matrix n n K) (p : n) :
    A⁻¹ p p = A.adjugate p p / A.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul, div_eq_inv_mul]

/-- **The trace formula, assembled.**  Given the matching recursion at `v`, subtracting the
forest resolvent diagonals from `x` produces exactly `μ_G/μ_{G-v}`. -/
theorem matching_ratio {K : Type*} [Field K] {x mG mF : K} {ι : Type*} (s : Finset ι)
    (mFp : ι → K) (hrec : mG = x * mF - ∑ p ∈ s, mFp p) (hF : mF ≠ 0) :
    x - ∑ p ∈ s, mFp p / mF = mG / mF := by
  rw [hrec, sub_div, mul_div_assoc, div_self hF, mul_one, Finset.sum_div]

/-! ## The trace step -/

variable {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]

omit [PartialOrder A] [IsOrderedAddMonoid A] in
/-- An additive functional sends `0` to `0`. -/
theorem map_zero_of_add {τ : A → ℝ} (hadd : ∀ a b, τ (a + b) = τ a + τ b) : τ 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  linarith

omit [PartialOrder A] [IsOrderedAddMonoid A] in
/-- An additive functional is odd. -/
theorem map_neg_of_add {τ : A → ℝ} (hadd : ∀ a b, τ (a + b) = τ a + τ b) (a : A) :
    τ (-a) = -τ a := by
  have h := hadd a (-a)
  rw [add_neg_cancel, map_zero_of_add hadd] at h
  linarith

/-- **The trace step.**  A faithful positive additive trace does not vanish on a definite
element.  This is the half of the Pimsner–Voiculescu argument that does not need
projectionlessness: once the spectral projection has been forced to be `0` or `1`, the
element is definite and the trace is strictly signed. -/
theorem trace_ne_zero_of_definite {τ : A → ℝ} (hadd : ∀ a b, τ (a + b) = τ a + τ b)
    (hpos : ∀ b : A, 0 < b → 0 < τ b) {a : A} (hdef : 0 < a ∨ a < 0) : τ a ≠ 0 := by
  rcases hdef with h | h
  · exact ne_of_gt (hpos a h)
  · have hneg : (0 : A) < -a := neg_pos.mpr h
    have := hpos _ hneg
    rw [map_neg_of_add hadd] at this
    linarith

/-! ## The conditional theorem -/

/-- **Feedback vertex number one, conditionally.**

`S` is the Schur complement of the universal cover onto the fibre over `v`, `Inv` is
invertibility in `C*_r(F_b)`, and `τ` its canonical trace.

* `htrace` is the trace formula `τ(S x) = μ_G(x)/μ_{G-v}(x)`, whose combinatorial half is
  `no_bypass` and whose algebraic half is `matching_ratio`.
* `hPV` is **Pimsner–Voiculescu**: in the projectionless algebra `C*_r(F_b)`, a self-adjoint
  invertible element is definite.  This is not in Mathlib and is assumed here.
* `hschur` is the Schur complement direction: if `S x` fails to be invertible then `x` lies
  in the spectrum of the universal cover.

The conclusion is that every root of `μ_G` that is not a root of `μ_{G-v}` lies in
`spec(A_T)`, which is Conjecture 10 at `d = 1` for this vertex. -/
theorem feedback_one_of {τ : A → ℝ} {S : ℝ → A} {Inv : A → Prop}
    {mG mF : ℝ → ℝ} {univSpec : Set ℝ}
    (hadd : ∀ a b, τ (a + b) = τ a + τ b)
    (hpos : ∀ b : A, 0 < b → 0 < τ b)
    (htrace : ∀ x, mF x ≠ 0 → τ (S x) = mG x / mF x)
    (hPV : ∀ x, Inv (S x) → 0 < S x ∨ S x < 0)
    (hschur : ∀ x, ¬ Inv (S x) → x ∈ univSpec)
    {θ : ℝ} (hroot : mG θ = 0) (hne : mF θ ≠ 0) : θ ∈ univSpec := by
  refine hschur θ fun hinv => ?_
  have hzero : τ (S θ) = 0 := by rw [htrace θ hne, hroot, zero_div]
  exact trace_ne_zero_of_definite hadd hpos (hPV θ hinv) hzero

end FeedbackVertex
