import Mathlib

/-!
# The span and the rank are component counts: the scalar steps

Two quantities in the 2-regularity criterion for A6 were measured rather than known: the span of the
`n` quadrics `Q_j` and the rank of `dQ(D)` on the kernel. Both are combinatorial. Writing `K(i,j)`
for the blocks separating `i` from `j`, tightness reads `∑_{k ∈ K(i,j)} D_k(i,j) = 0` pair by pair,
and

  `∑_j w_j Q_j(D) = ∑_{i<j} (w_j - w_i) ∑_{k ∈ K(i,j)} σ_k(j) D_k(i,j)²`,
  `∑_j w_j dQ_j(D)[E] = 2 ∑_{i<j} (w_j - w_i) ∑_{k ∈ K(i,j)} σ_k(j) D_k(i,j) E_k(i,j)`.

So in both cases `w` annihilates exactly when, pair by pair, either `w_i = w_j` or a form on the
hyperplane `{∑ t = 0}` vanishes identically: a diagonal quadratic form with the signs as
coefficients in the first, a linear functional with `σ_k(j) D_k(i,j)` as coefficients in the second.
The annihilator is then the space of functions constant on the components of the corresponding
graph, by `CokernelRank.const_of_adj_eq`, and both quantities are `n` minus a component count.

This file carries the scalar steps, which is where the content is; the assembly into the two formulas
is the same argument twice and is in `code/spanrank.py`, verified at seven families.

## The linear case, and the rank formula

`linear_vanishes_iff_const`: a linear functional vanishes on `{∑ t = 0}` exactly when its
coefficients are all equal. So `dQ(D)` sees the pair `(i,j)` exactly when
`(σ_k(j) D_k(i,j))_{k ∈ K(i,j)}` is non-constant, which is the graph `G_D` already used for the
order-four obstruction. The same graph governs the second-order rank.

## The quadratic case, and the span formula

The diagonal form `∑ ε_k t_k²` vanishes on the hyperplane exactly when `ε_a + ε_b = 0` for every
pair, and for signs `ε_k = ±1` that resolves into a criterion with no arithmetic in it:

* `sq_form_ne_zero_of_agree`: two separating blocks on the same side give a non-vanishing form, so
  the pair is an edge;
* `exists_agree_of_three`: three separating blocks always contain two on the same side, by
  pigeonhole, so `|K(i,j)| ≥ 3` is always an edge;
* `sq_form_zero_of_pair`: two separating blocks on opposite sides give a vanishing form, so the pair
  is not an edge;
* `sq_form_zero_of_subsingleton`: fewer than two separating blocks leave no freedom at all.

Together: the pair is an edge of `G_Q` iff `|K(i,j)| ≥ 3`, or `|K(i,j)| = 2` with both separating
blocks on the same side. `G_Q` depends on the hypergraph alone.

## What this settles, and in which direction

`G_D` is always a subgraph of `G_Q`, and 2-regularity at `D` says the two have the same components.
For a generic kernel direction they are equal. They are not equal at every *cone* direction: a cross
basis direction is supported on one pair with two separating blocks of opposite sign, and
`sq_form_zero_of_pair` is exactly why it satisfies `Q = 0`, while `linear_vanishes_iff_const` makes
its `dQ` rank at most one. So A6 does not follow from 2-regularity at every cone direction, and the
answer to that question is no. Those directions carry an explicit curve instead, the rotation of the
cross configuration, so nothing is lost; what is lost is the hope of one uniform route.

## Status

`linear_vanishes_iff_const`, `sq_form_ne_zero_of_agree`, `sq_form_zero_of_pair`,
`sq_form_zero_of_subsingleton`, `signs_cancel_of_sq_form_zero`, `sum_probe_mul`,
`sum_probe_sq` and `exists_agree_of_three` are `VERIFIED`.
-/

namespace SpanRank

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The test vector: `+1` at `a`, `-1` at `b`, zero elsewhere. It lies on the hyperplane, and every
statement below is proved by evaluating on it. -/
def probe (a b : ι) : ι → ℝ := fun k => (if k = a then (1 : ℝ) else 0) - (if k = b then 1 else 0)

/-- Pairing the probe against any function reads off a difference. -/
theorem sum_probe_mul (f : ι → ℝ) (a b : ι) : ∑ k, f k * probe a b k = f a - f b := by
  simp only [probe, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' univ a f, Finset.sum_ite_eq' univ b f]
  simp

theorem probe_sum (a b : ι) : ∑ k, probe a b k = 0 := by
  have := sum_probe_mul (fun _ => (1 : ℝ)) a b
  simpa using this

/-- Against the squares it reads off a sum instead, the two signs adding rather than cancelling.
This one line is the whole difference between the two criteria below. -/
theorem sum_probe_sq (ε : ι → ℝ) (a b : ι) (hab : a ≠ b) :
    ∑ k, ε k * (probe a b k) ^ 2 = ε a + ε b := by
  have h : ∀ k, ε k * (probe a b k) ^ 2
      = (if k = a then ε k else 0) + (if k = b then ε k else 0) := by
    intro k
    by_cases hka : k = a
    · subst hka; simp [probe, hab]
    · by_cases hkb : k = b
      · subst hkb; simp [probe, hka]
      · simp [probe, hka, hkb]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ a ε, Finset.sum_ite_eq' univ b ε]
  simp

/-- **The linear criterion.**  A linear functional vanishes on the sum-zero hyperplane exactly when
all its coefficients agree.  This is what makes the rank of `dQ(D)` a component count. -/
theorem linear_vanishes_iff_const (c : ι → ℝ) :
    (∀ t : ι → ℝ, ∑ k, t k = 0 → ∑ k, c k * t k = 0) ↔ ∀ a b : ι, c a = c b := by
  constructor
  · intro h a b
    have := h (probe a b) (probe_sum a b)
    rw [sum_probe_mul c a b] at this
    linarith
  · intro h t ht
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨a₀⟩⟩
    · simp
    · calc ∑ k, c k * t k = ∑ k, c a₀ * t k :=
            Finset.sum_congr rfl fun k _ => by rw [h k a₀]
        _ = c a₀ * ∑ k, t k := by rw [Finset.mul_sum]
        _ = 0 := by rw [ht, mul_zero]

/-- **The quadratic criterion, non-vanishing half.**  Two coefficients that agree and are nonzero
give a form that does not vanish on the hyperplane: the pair is an edge of `G_Q`. -/
theorem sq_form_ne_zero_of_agree (ε : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (hagree : ε a = ε b) (hne : ε a ≠ 0) :
    ∃ t : ι → ℝ, (∑ k, t k = 0) ∧ ∑ k, ε k * (t k) ^ 2 ≠ 0 := by
  refine ⟨probe a b, probe_sum a b, ?_⟩
  rw [sum_probe_sq ε a b hab, ← hagree]
  intro hcon
  exact hne (by linarith)

/-- The converse test: if the form vanishes on the hyperplane then every pair of coefficients
cancels.  With signs `±1` that forces the two separating blocks onto opposite sides. -/
theorem signs_cancel_of_sq_form_zero (ε : ι → ℝ)
    (h : ∀ t : ι → ℝ, ∑ k, t k = 0 → ∑ k, ε k * (t k) ^ 2 = 0) (a b : ι) (hab : a ≠ b) :
    ε a + ε b = 0 := by
  have := h (probe a b) (probe_sum a b)
  rwa [sum_probe_sq ε a b hab] at this

/-- **The quadratic criterion, vanishing half.**  On a two-element index set with opposite signs the
form vanishes identically on the hyperplane.  This is exactly the cross configuration, and it is why
a cross basis direction satisfies `Q = 0`. -/
theorem sq_form_zero_of_pair (ε : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (hall : ∀ k : ι, k = a ∨ k = b) (hopp : ε a + ε b = 0)
    (t : ι → ℝ) (ht : ∑ k, t k = 0) : ∑ k, ε k * (t k) ^ 2 = 0 := by
  have huniv : (univ : Finset ι) = {a, b} := by
    ext x; simpa using hall x
  rw [huniv, Finset.sum_pair hab] at ht ⊢
  have hb : t b = -t a := by linarith
  have hεb : ε b = -ε a := by linarith
  rw [hb, hεb]; ring

omit [DecidableEq ι] in
/-- Fewer than two separating blocks leave no freedom: the hyperplane is trivial. -/
theorem sq_form_zero_of_subsingleton [Subsingleton ι] (ε : ι → ℝ)
    (t : ι → ℝ) (ht : ∑ k, t k = 0) : ∑ k, ε k * (t k) ^ 2 = 0 := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨a⟩⟩
  · simp
  · have huniv : (univ : Finset ι) = {a} := by
      ext x; simp [Subsingleton.elim x a]
    rw [huniv, Finset.sum_singleton] at ht ⊢
    rw [ht]; ring

omit [Fintype ι] [DecidableEq ι] in
/-- **Pigeonhole.**  Among three separating blocks two lie on the same side, so `|K(i,j)| ≥ 3` is
always an edge of `G_Q` whatever the signs are.  Stated for values in `{1, -1}`, which is what the
signs `σ_k(j)` are. -/
theorem exists_agree_of_three (ε : ι → ℝ) (hsign : ∀ k, ε k = 1 ∨ ε k = -1)
    (a b c : ι) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ x y : ι, x ≠ y ∧ ε x = ε y := by
  rcases hsign a with ha | ha <;> rcases hsign b with hb | hb <;> rcases hsign c with hc | hc
  · exact ⟨a, b, hab, by rw [ha, hb]⟩
  · exact ⟨a, b, hab, by rw [ha, hb]⟩
  · exact ⟨a, c, hac, by rw [ha, hc]⟩
  · exact ⟨b, c, hbc, by rw [hb, hc]⟩
  · exact ⟨b, c, hbc, by rw [hb, hc]⟩
  · exact ⟨a, c, hac, by rw [ha, hc]⟩
  · exact ⟨a, b, hab, by rw [ha, hb]⟩
  · exact ⟨a, b, hab, by rw [ha, hb]⟩

end SpanRank
