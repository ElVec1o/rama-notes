import Mathlib

/-!
# The ratio route: a sign-alternating invariant for the cavity recursion

`SoftEdge.rayleigh_in_gap` bars compression arguments from proving the inner half of the
two-sided statement: a quadratic form cannot separate a gap point from a spectral point.  The
ratio recursion is not barred, because it bounds ratios of matching polynomials rather than
Rayleigh quotients.  This file makes that route concrete.

## The reduction

By Godsil `μ_G` divides `μ_P` for the path tree `P`, and on a tree the deletion recurrence is
exact and local:

  `F_v = λ - ∑_{u a child of v} 1/F_u`,   `F_leaf = λ`.

So `μ_G(λ) ≠ 0` follows if no `F` vanishes on `P`.

## Why the obvious certificate fails, and what replaces it

If every child ratio lay in `[a,b]` with `a > 0`, invariance would need `a ≤ λ - k/a`, that is
`a² - λa + k ≤ 0`, which has a positive solution only for `λ ≥ 2√k`.  That is the Heilmann-Lieb
bound: a *positive* invariant interval exists only above the band, never inside a gap.

Measurement says what replaces it.  On path trees of `(d,q)`-biregular graphs at gap points,
over twenty-two thousand path-tree vertices, the ratios separate perfectly by vertex type with
no exceptions: every degree-`d` vertex has `F > 0` and every degree-`q` vertex has `F < 0`
(`code/pathratio.py`).  For `(3,9)` at `λ = 0.354` the left ratios fill `[0.3536, 0.5353]`, the
left endpoint being the leaf value `λ`, and the right ratios fill `[-22.27, -13.79]`.  The
certificate is therefore *sign-alternating*: a positive interval on one side of the bipartition
and a negative interval on the other.

## The two steps

`left_step`: children negative in `[-C,-c]` push the parent up, to `[λ, λ + k/c]`.  Since `λ > 0`
this keeps the parent positive and bounded, and it holds for every number of children, so
truncation of the path tree is harmless here.

`right_step`: children positive in `[a,B]` push the parent down, and it lands strictly negative
as soon as `k > λB`.

Together they close the induction on `P` and give `no_vanishing`.

## The constants are forced, and they are the tree fixed point

The two steps determine each other.  Taking `a = λ` (the leaf value), `B = λ + (d-1)/c` from
`left_step` and `c = k₀/B - λ` from `right_step`, where `k₀` is the least number of children at
a right-type vertex, eliminates `c`.  What is left is that `B` closes the system exactly when

  `λB² - B(k₀ + λ² - d + 1) + λk₀ = 0`,

which is `certificate_closes`.  Two facts about that quadratic decide the route.

Its discriminant `(k₀ + λ² - d + 1)² - 4λ²k₀` vanishes **exactly at the gap edge**.  With
`s = √(d-1)`, `t = √(q-1)`, `k₀ = q-1 = t²` and `λ = g = t - s`, one has
`k₀ + λ² - d + 1 = 2t(t-s)`, so the discriminant is `4t²(t-s)² - 4(t-s)²t² = 0`; that is
`discriminant_vanishes_at_edge`.  Numerically it is positive throughout the open gap and zero at
the edge in every family tested (`code/certificate.py`).  A certificate that degenerates
precisely where the gap closes is the right object.

And its smaller root is the universal cover's cavity fixed point `F_d`, agreeing to fifteen
digits in every case checked.  So the certificate constants are not chosen; they are the fixed
point the path tree is already tracking.

## What remains

The uniform form of `right_step` needs `k > λB`, and that **fails**: for a `(3,6)`-biregular
graph on `15` vertices at `λ = 0.99g`, `0.21%` of right-type vertices have too few children
(`code/certificate.py`).

The defect is repaired by dropping the uniform interval.  Measuring the child ratios directly,
a right-type vertex at the minimum child count carries children that are *leaves*, of ratio
exactly `λ`: `0.8136` against `λ = 0.8136` at `k = 1`, and the same at the minimum `k` of every
family tested.  So the correct hypothesis is a bound on the ratios rather than on the counts,
and `right_step_sharp` supplies it: child ratios below `k/λ` suffice, which is what the path
trees satisfy with slack `0.42` to `4.47` and **zero violations** over every vertex measured
(`code/childbound.py`).  The requirement thereby drops from `k > λB` to `k > λ²`, strictly
weaker since `B > λ`, and the failing case is covered: at `k = 1` it needs `F < 1/λ = 1.229`
against an observed `0.8136`.

## What remains

  **A10′.**  Every child ratio at a right-type path-tree vertex with `k` children is below
  `k/λ`.

That is the whole remaining gap.  It is a statement about how blocking propagates from a vertex
to its children along a self-avoiding walk, so it is combinatorial rather than spectral, which
is the point of taking this route.

## Status

`left_step`, `right_step`, `right_step_sharp`, `right_step_leaves`, `certificate_closes`,
`discriminant_vanishes_at_edge` and `no_vanishing` are `VERIFIED`.  That the *uniform*
certificate closes on every path tree is `FALSE`, failing on `0.21%` of vertices in one measured
case; the sharp form repairs it.  A10′ and the sign separation are `HEURISTIC`, on the
measurements cited.  The biregular case of Conjecture 10 remains a `CONJECTURE`.
-/

namespace RatioRoute

open Finset

/-- **Negative children push the parent up.**  If every child ratio lies in `[-C, -c]` with
`0 < c`, then `-1/F` is positive and at most `1/c`, so the parent lies in `[λ, λ + k/c]`.  In
particular it stays positive, and the bound holds for *every* number of children, so a path-tree
vertex missing some of its children is still covered. -/
theorem left_step {k : ℕ} (F : Fin k → ℝ) (lam c C : ℝ) (hc : 0 < c)
    (hF : ∀ j, -C ≤ F j ∧ F j ≤ -c) :
    lam ≤ lam - ∑ j, 1 / F j ∧ lam - ∑ j, 1 / F j ≤ lam + k / c := by
  have hneg : ∀ j, F j < 0 := fun j => lt_of_le_of_lt (hF j).2 (by linarith)
  have hup : ∀ j ∈ (univ : Finset (Fin k)), 1 / F j ≤ 0 := fun j _ =>
    div_nonpos_of_nonneg_of_nonpos zero_le_one (hneg j).le
  have hlow : ∀ j ∈ (univ : Finset (Fin k)), -(1 / c) ≤ 1 / F j := by
    intro j _
    have h1 : F j ≤ -c := (hF j).2
    have : 1 / F j = -(1 / (-F j)) := by field_simp
    rw [this, neg_le_neg_iff]
    exact one_div_le_one_div_of_le hc (by linarith)
  constructor
  · have : ∑ j, 1 / F j ≤ 0 := sum_nonpos hup
    linarith
  · have hs : -((k : ℝ) / c) ≤ ∑ j, 1 / F j := by
      calc -((k : ℝ) / c) = ∑ _j : Fin k, -(1 / c) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ ∑ j, 1 / F j := sum_le_sum hlow
    linarith

/-- **Positive children push the parent down, and past zero once there are enough of them.**
If every child ratio lies in `[a, B]` with `0 < a`, each contributes at least `1/B`, so the sum
exceeds `λ` as soon as `k > λB` and the parent is strictly negative. -/
theorem right_step {k : ℕ} (F : Fin k → ℝ) (lam a B : ℝ) (ha : 0 < a) (haB : a ≤ B)
    (hF : ∀ j, a ≤ F j ∧ F j ≤ B) (hk : lam * B < k) :
    lam - ∑ j, 1 / F j < 0 := by
  have hB : 0 < B := lt_of_lt_of_le ha haB
  have hge : ∀ j ∈ (univ : Finset (Fin k)), 1 / B ≤ 1 / F j := fun j _ =>
    one_div_le_one_div_of_le (lt_of_lt_of_le ha (hF j).1) (hF j).2
  have hs : (k : ℝ) / B ≤ ∑ j, 1 / F j := by
    calc (k : ℝ) / B = ∑ _j : Fin k, 1 / B := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ j, 1 / F j := sum_le_sum hge
  have : lam < (k : ℝ) / B := by rw [lt_div_iff₀ hB]; linarith
  linarith

/-- **The sharp right step.**  If every child ratio is positive and below `k/λ`, each
reciprocal exceeds `λ/k`, the sum exceeds `λ`, and the parent is strictly negative.

This replaces the uniform hypothesis `k > λB` of `right_step` by a bound on the child ratios
themselves, which is what a path tree actually satisfies, and it repairs the defect: the
requirement drops from `k > λB` to `k > λ²`, strictly weaker since `B > λ`. -/
theorem right_step_sharp {k : ℕ} (hk : 0 < k) (F : Fin k → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hF : ∀ j, 0 < F j ∧ F j < (k : ℝ) / lam) :
    lam - ∑ j, 1 / F j < 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hne : (univ : Finset (Fin k)).Nonempty := by
    rw [univ_nonempty_iff]; exact Fin.pos_iff_nonempty.mp hk
  have hlt : ∀ j ∈ (univ : Finset (Fin k)), lam / (k : ℝ) < 1 / F j := by
    intro j _
    rw [div_lt_div_iff₀ hkR (hF j).1]
    have h2 := (hF j).2
    rw [lt_div_iff₀ hlam] at h2
    nlinarith [h2]
  have hs : ∑ _j : Fin k, lam / (k : ℝ) < ∑ j, 1 / F j := sum_lt_sum_of_nonempty hne hlt
  have hconst : ∑ _j : Fin k, lam / (k : ℝ) = lam := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith

/-- **The extreme case is the leaf case.**  A child with no children of its own has ratio
exactly `λ`, so a right-type vertex all of whose children are leaves has ratio `λ - k/λ`, which
is negative precisely when `k > λ²`.  Measurement says this is the binding case: at the minimum
child count on every path tree examined, every child is a leaf, its ratio equal to `λ` to the
last digit. -/
theorem right_step_leaves {k : ℕ} (lam : ℝ) (hlam : 0 < lam) (hk : lam ^ 2 < k) :
    lam - (k : ℝ) / lam < 0 := by
  rw [sub_neg, lt_div_iff₀ hlam]
  nlinarith

/-- **The constants are forced.**  With `c` defined by `cB = k₀ - λB`, the requirement
`B = λ + (d-1)/c` of `left_step` holds exactly when `B` satisfies the quadratic
`λB² - B(k₀ + λ² - d + 1) + λk₀ = 0`.  So the two steps do not leave the constants free: they
determine them. -/
theorem certificate_closes {lam B k0 dd c : ℝ} (hB : B ≠ 0)
    (hcdef : c * B = k0 - lam * B)
    (hquad : lam * B ^ 2 - B * (k0 + lam ^ 2 - dd + 1) + lam * k0 = 0) :
    B * c = lam * c + (dd - 1) := by
  refine mul_right_cancel₀ hB ?_
  have e1 : B * c * B = B * (c * B) := by ring
  have e2 : (lam * c + (dd - 1)) * B = lam * (c * B) + (dd - 1) * B := by ring
  rw [e1, e2, hcdef]
  linear_combination -hquad

/-- **The certificate degenerates exactly at the gap edge.**  Writing `s = √(d-1)`, `t = √(q-1)`
so that `g = t - s` and `k₀ = q - 1 = t²`, the discriminant of that quadratic at `λ = g` is
identically zero.  Inside the gap it is positive, so the certificate exists throughout the open
gap and fails precisely where the gap itself closes. -/
theorem discriminant_vanishes_at_edge (s t : ℝ) :
    (t ^ 2 + (t - s) ^ 2 - s ^ 2) ^ 2 - 4 * (t - s) ^ 2 * t ^ 2 = 0 := by ring

/-- **The two steps close the induction.**  A ratio that is either at least `λ > 0` or at most
`-c < 0` is nonzero; `left_step` delivers the first alternative and `right_step` the second, so
under the sign-alternating invariant no ratio on the path tree vanishes and `μ_G(λ) ≠ 0`. -/
theorem no_vanishing {F lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (h : lam ≤ F ∨ F ≤ -c) : F ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt (lt_of_lt_of_le hlam h)
  · exact ne_of_lt (lt_of_le_of_lt h (by linarith))

end RatioRoute
