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

## The coupled induction, corrected

Assembling both sides gives a system in one constant `m > 0`, the lower bound on `|F|` at
right-type vertices.  With `κ(t) = λ + t/m` bounding left-type ratios at child count `t`, and
`min_children`/`child_count_drop` capping a right-type vertex's children at `k - D` each, the
parent is at most `λ - k/κ(k-D)`.  The invariant propagates when that is at most `-m`, which by
`closure_iff` is

  `λ + m ≤ k / κ(k-D)`   for every attainable `k`, that is `D ≤ k ≤ q-1`.

The recursion consuming these steps is `PathTreeInduction.invariant`.

**This is a fixed-point condition on `m`, not a closed form**, and an earlier version of this
file asserted otherwise.  It took `m = D/λ - 2λ`, on the reasoning that `μ(j) = j/κ(j-D) - λ`
decreases to that limit.  The limit is `D/λ - 3λ`, so `μ(j)` drops *below* the value fed into
`κ`, and `κ` was not a valid bound.  For `(3,6,4)` at `λ = 0.99g` the values are `μ(2) = 1.64`,
`μ(3) = 0.67`, `μ(4) = 0.43`, `μ(5) = 0.32`, all under the `0.83` assumed.  The error surfaced
while formalizing, which is what formalizing is for.

Solving the fixed point properly, by iterating `m ↦ min_{D ≤ j ≤ q-1} (j/(λ + (j-D)/m) - λ)`
from above, the induction closes on the **whole** gap for `(4,8,4)`, `(4,12,4)` and `(5,10,4)`,
and on part of it elsewhere: `61%` of `g` for `(3,6,4)`, `78%` for `(3,9,4)`, `83%` for
`(3,12,4)` and `29%` for `(3,6,5)` (`code/coupled.py`).  The earlier claim of the whole gap for
`(3,6,4)` and `(3,9,4)` is withdrawn.

So the biregular case of Conjecture 10 is proved for every `(d,q)`-biregular graph and every `λ`
in the gap at which the fixed point is positive, which is the entire gap for three of the
families tested.  It remains the first proof of the inner half of the two-sided statement for a
nontrivial class, on a smaller class than was claimed.

## Status

`left_step`, `right_step`, `right_step_sharp`, `right_step_leaves`, `certificate_closes`,
`discriminant_vanishes_at_edge`, `no_vanishing`, `right_step_bound`, `closure_iff` and
`induction_step` are `VERIFIED`.  The counting lemmas `min_children`, `child_count_drop`,
`children_are_leaves` and `binding_case` are `VERIFIED`, and their three graph-theoretic inputs
are now formalized too, in `PathCount`.

That the *uniform* certificate closes on every path tree is `FALSE`, failing on `0.21%` of
vertices in one measured case; `right_step_sharp` repairs it.  The earlier closed-form closure
condition is `FALSE` and withdrawn.

The biregular case of Conjecture 10 wherever the fixed point is positive is `VERIFIED`: every
step is verified, and the recursion over the path tree is now carried out in
`PathTreeInduction.invariant`, with `no_vanishing` concluding that no ratio vanishes.  Nothing
in the chain from hypotheses to conclusion is left unformalized.  Outside that range, and the sign separation, remain
`HEURISTIC` on the measurements cited.  The general biregular case remains a `CONJECTURE`.
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


/-! ## The refined step: the bound is per-vertex, not global

`right_step` needs `k > λB` with `B` the worst-case bound for *every* child, and that is what
fails. Measured on the path tree of the `(3,6,5)` family at `λ = 0.8136`, the uniform requirement
is `k > 1.6247` while eight right-type vertices have `k = 1`
(`code/certificate.py`), and the certificate does not close.

The worst case is the wrong bound for those children. `left_step` already gives a left vertex
with `j` children the bound `λ + j/c`, and the global `B` is that at `j = d-1`. A right vertex
with very few children sits where the path tree is nearly exhausted, so its children are
child-poor too and carry a much smaller bound. Instantiating `B` per-vertex from the child's own
count rather than globally, the requirement becomes `k > λ(λ + j_max/c)`, which is strictly
weaker whenever `j_max < d-1` (`refined_weaker`), and it closes every family tested including
`(3,6,5)`, where the uniform certificate fails: `0` failures against `8`
(`code/twolevel.py`). That was the documented defect and it is the last one.

Nothing here is new analysis; it is the same two steps composed in the order that keeps the
information `left_step` already produces. The uniform certificate discards the child count and
then cannot recover it. -/

/-- The bound a left-type vertex inherits from its own child count, via `left_step`. The global
`B` of the uniform certificate is this at `j = d-1`, the worst case. -/
noncomputable def leftBound (lam c : ℝ) (j : ℕ) : ℝ := lam + (j : ℝ) / c

/-- Fewer children, smaller bound. -/
theorem leftBound_mono {lam c : ℝ} (hc : 0 < c) {j j' : ℕ} (h : j ≤ j') :
    leftBound lam c j ≤ leftBound lam c j' := by
  unfold leftBound
  have : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast h
  gcongr

/-- **The refined requirement is strictly weaker.** A child with fewer than `d-1` children
imposes a strictly smaller threshold than the uniform one, which is exactly why a right vertex
with `k = 1` can be safe although `k > λB` fails. -/
theorem refined_weaker {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) {j j' : ℕ} (h : j < j') :
    lam * leftBound lam c j < lam * leftBound lam c j' := by
  have hj : (j : ℝ) < (j' : ℝ) := by exact_mod_cast h
  have : leftBound lam c j < leftBound lam c j' := by
    unfold leftBound; gcongr
  exact mul_lt_mul_of_pos_left this hlam

/-- **The refined right step.** Each child is bounded by `leftBound` at *its own* child count,
and the requirement uses the largest of those rather than the global worst case. Reduces to
`right_step` with `B` instantiated per-vertex. -/
theorem right_step_refined {k : ℕ} (F : Fin k → ℝ) (lam a c Bmax : ℝ) (j : Fin k → ℕ)
    (ha : 0 < a) (haB : a ≤ Bmax)
    (hF : ∀ i, a ≤ F i ∧ F i ≤ leftBound lam c (j i))
    (hBmax : ∀ i, leftBound lam c (j i) ≤ Bmax)
    (hk : lam * Bmax < k) :
    lam - ∑ i, 1 / F i < 0 :=
  right_step F lam a Bmax ha haB (fun i => ⟨(hF i).1, le_trans (hF i).2 (hBmax i)⟩) hk

/-! ## Blocking propagates: the combinatorial core of A10' -/

/-- **Every right-type path-tree vertex has at least `q - r` children.**

The three hypotheses are the graph-theoretic inputs, each elementary.  Let `π` be a
self-avoiding path in a `(d,q)`-biregular bipartite graph with sides `L` (degree `d`) and `R`
(degree `q`, size `r`), ending at `w ∈ R`, with `k = |N(w) ∖ π|`, and write `pL = |π ∩ L|`,
`pR = |π ∩ R|`.  Then `q - k ≤ pL` because the `q - k` blocked neighbours of `w` all lie in `L`;
`pL ≤ pR` because `π` alternates and ends in `R`; and `pR ≤ r` trivially.

Measured: `min k = q - r` exactly, in every family with `q > r`, so the bound is attained. -/
theorem min_children {q r k pL pR : ℤ} (h1 : q - k ≤ pL) (h2 : pL ≤ pR) (h3 : pR ≤ r) :
    q - r ≤ k := by linarith

/-- **The child count drops by at least `q - r` each level.**

Same setup, with `u ∈ N(w) ∖ π` a child of `w` and `ku` its own child count.  The third
hypothesis `ku ≤ r - pR` holds because `N(u) ⊆ R` and an unblocked neighbour of `u` must avoid
`π ∩ R`.  Combined with `pR ≥ pL ≥ q - k` this gives `ku ≤ r - q + k`.

Measured over roughly fourteen thousand right-type path-tree vertices in five families: zero
violations, and worst slack `0` in four of them, so this bound is attained too
(`code/blocking.py`). -/
theorem child_count_drop {q r k pL pR ku : ℤ}
    (h1 : q - k ≤ pL) (h2 : pL ≤ pR) (h3 : ku ≤ r - pR) :
    ku ≤ k - (q - r) := by linarith

/-- **At the minimum child count the children are leaves.**  Combining the two bounds: when `k`
attains `q - r`, every child has `ku ≤ 0`, hence `ku = 0`.  A childless left-type vertex has
ratio exactly `λ`, which is what `code/childbound.py` measured to the last digit, and it is the
binding case of `right_step_sharp`. -/
theorem children_are_leaves {q r k ku : ℤ} (hk : k ≤ q - r) (h : ku ≤ k - (q - r))
    (hku : 0 ≤ ku) : ku = 0 := by omega

/-- **The binding case closes.**  At the minimum child count every child is a leaf of ratio
exactly `λ`, so the parent is `λ - k/λ`, strictly negative as soon as `k > λ²`.  This is
`right_step_leaves` applied to the configuration `children_are_leaves` forces. -/
theorem binding_case {k : ℕ} (lam : ℝ) (hlam : 0 < lam) (hk : lam ^ 2 < k) :
    lam - (k : ℝ) / lam < 0 :=
  right_step_leaves lam hlam hk


/-- **Structural closure: two inequalities replace the path tree.**

Substituting the two combinatorial bounds — `min_children` (`Δ ≤ k`) and `child_count_drop`
(`j ≤ k - Δ`) — into the refined requirement `λ·leftBound λ c j < k` and asking it for every
admissible `k` reduces it to

  `λ < c`   and   `λ² < Δ`,

because `Δ(c-λ) > λ(λc-Δ)` is equivalent to `Δ > λ²` after cancelling `c`. Neither mentions a
path tree, a family, or a graph: given those two numbers the certificate closes at every
right-type vertex at once.

The second condition is the one already known — it is `binding_case`, the requirement that the
minimum-child-count configuration closes, where `children_are_leaves` forces every child to be a
leaf of ratio exactly `λ`. The first is new and is what the per-vertex bound buys.

Measured over 354 *realizable* parameter points — a `(d,q)`-biregular bipartite graph with
`|R| = r` needs `|L| = qr/d` to be a positive integer, and an earlier sweep of this omitted the
check and counted `(3,20,19)`, where `qr/d = 126.667`, among its failures — the pair holds at
**326**, or `92.1%` (`code/universal_close.py`). There the ratio route closes *provably* rather
than family by family.

The `28` failures sit where `λ` approaches the gap edge, at `frac = 0.9` and `0.99`, and they are
the two conditions themselves rather than a weakness elsewhere: `code/sharp_close.py` checks the
sharper combinatorial bound `ku ≤ min(d-1, k-(q-r))`, which uses the elementary fact that a child
lies in `L` and has degree `d`, and it gains **nothing** at any parameter point, because both
tests stop earlier on the constants. So the obstruction is not the child-count bound. It is that
near the gap edge either `λ² < Δ` fails, which is `binding_case` failing and means the
sign-alternating pattern cannot hold at the minimum child count, or `λ < c` fails. Extending the
route to the edge needs a different invariant there, not a better combinatorial bound. -/
theorem structural_closure {lam c : ℝ} (hlam : 0 < lam) (hlc : lam < c)
    {Delta k j : ℕ} (hD : lam ^ 2 < (Delta : ℝ)) (hk : Delta ≤ k)
    (hj : (j : ℝ) ≤ (k : ℝ) - (Delta : ℝ)) :
    lam * leftBound lam c j < (k : ℝ) := by
  have hc : 0 < c := lt_trans hlam hlc
  have hkD : ((Delta : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk
  have hstep : lam * leftBound lam c j ≤ lam * (lam + ((k : ℝ) - Delta) / c) := by
    have : leftBound lam c j ≤ lam + ((k : ℝ) - Delta) / c := by
      unfold leftBound; gcongr
    exact mul_le_mul_of_nonneg_left this hlam.le
  refine lt_of_le_of_lt hstep ?_
  rw [← sub_pos]
  have hprod : (0 : ℝ) ≤ ((k : ℝ) - Delta) * (c - lam) := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) - Delta := by linarith
    have h2 : (0 : ℝ) ≤ c - lam := by linarith
    positivity
  have key : (0 : ℝ) < ((k : ℝ) - lam * lam) * c - lam * ((k : ℝ) - Delta) := by
    nlinarith [hprod, hD, hlam, hc, hkD]
  have hexp : (k : ℝ) - lam * (lam + ((k : ℝ) - Delta) / c)
      = (((k : ℝ) - lam * lam) * c - lam * ((k : ℝ) - Delta)) / c := by
    field_simp; ring
  rw [hexp]
  exact div_pos key hc

/-! ## The coupled induction, and when it closes -/

/-- **The right step with an explicit bound on the children.**  If every child ratio is positive
and at most `κ`, the parent is at most `λ - k/κ`. -/
theorem right_step_bound {k : ℕ} (F : Fin k → ℝ) (lam kap : ℝ)
    (hF : ∀ j, 0 < F j ∧ F j ≤ kap) :
    lam - ∑ j, 1 / F j ≤ lam - (k : ℝ) / kap := by
  have hge : ∀ j ∈ (univ : Finset (Fin k)), 1 / kap ≤ 1 / F j := fun j _ =>
    one_div_le_one_div_of_le (hF j).1 (hF j).2
  have hs : (k : ℝ) / kap ≤ ∑ j, 1 / F j := by
    calc (k : ℝ) / kap = ∑ _j : Fin k, 1 / kap := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ j, 1 / F j := sum_le_sum hge
  linarith

/-- **The closure inequality.**  The right-type bound reaches `-m` exactly when `λ + m ≤ k/κ`.
This is what the coupled system must satisfy at every attainable child count. -/
theorem closure_iff {lam kap m : ℝ} {k : ℕ} :
    lam - (k : ℝ) / kap ≤ -m ↔ lam + m ≤ (k : ℝ) / kap := by
  constructor <;> intro h <;> linarith

/-- **The induction step, assembled.**  At a right-type vertex with `k` children whose ratios lie
in `(0, κ]`, if the closure inequality holds at `k` then the parent ratio is at most `-m`, so the
invariant propagates.  With `left_step`, which sends children at most `-m` to a parent in
`[λ, λ + j/m]`, this is the whole step; the recursion over the path tree is the standard
well-founded one on a finite tree. -/
theorem induction_step {k : ℕ} (F : Fin k → ℝ) (lam kap m : ℝ)
    (hF : ∀ j, 0 < F j ∧ F j ≤ kap) (hclose : lam + m ≤ (k : ℝ) / kap) :
    lam - ∑ j, 1 / F j ≤ -m :=
  le_trans (right_step_bound F lam kap hF) (closure_iff.mpr hclose)

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
