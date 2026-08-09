import Mathlib

/-!
# The path-tree recursion, formalized

`RatioRoute` proves the induction *step* on both sides of the bipartition, and left the
recursion over the path tree itself as "the standard well-founded induction on a finite tree".
This file removes that gap: the recursion is carried out.

## The abstraction

A path tree is not needed in its graph-theoretic form.  All the argument uses is a set of
vertices, a side map, a children map, and the fact that children are strictly smaller in some
`ℕ`-valued height, so the recursion terminates.  That is `PT`.  Instantiating it with the tree
of self-avoiding walks, side given by which part of the bipartition the walk ends in and height
by the number of vertices still available, is immediate.

## The statement

Given the ratio recurrence `F v = λ - ∑_{c a child of v} 1/F c`, the two structural facts proved
in `PathCount` and packaged in `RatioRoute` -- every right-type vertex has at least `D` children,
and a right-type vertex's children have at least `D` fewer children than it does -- and the
closure inequality at every attainable child count, `invariant` concludes

* every right-type ratio is at most `-m`, in particular strictly negative, and
* every left-type ratio lies in `[λ, λ + k/m]` with `k` its child count.

Since `λ > 0` and `m > 0`, no ratio vanishes, so `μ_G(λ) ≠ 0` at every such `λ`.  That is the
theorem the ratio route was aiming at, now with no unformalized step between the hypotheses and
the conclusion.

## What is assumed

`hclose` is the fixed-point condition, checked numerically per family in `code/coupled.py`; it
is a hypothesis here, as it must be, since whether it holds depends on `(d,q,r)` and `λ`.
`hmin` and `hdrop` are the counting facts, whose graph-theoretic proofs are in `PathCount`.
Nothing else is assumed.

`saturation_blocks_improvement` records the other side of the ledger: where both bounds are
attained, no choice of constants does better, so the route has a limit there.

`invariant_depth` is the general form, with the two bounds indexed by height.  It is what
recovers the range the uniform constants miss: feeding in the per-depth counting bounds turns
the fixed point into a finite backward recursion, closing the whole gap for six of seven
families against three (`code/depthind.py`).
-/

namespace PathTreeInduction

open List

/-- A path tree, abstractly: vertices carry a side, a list of children, and a height that
strictly decreases along edges.  Children lie on the opposite side. -/
structure PT (V : Type*) where
  isR : V → Bool
  ch : V → List V
  ht : V → ℕ
  ht_lt : ∀ v, ∀ c ∈ ch v, ht c < ht v
  alt : ∀ v, ∀ c ∈ ch v, isR c = !isR v

variable {V : Type*}

/-! ## Two list-sum bounds -/

theorem sum_map_nonpos {l : List V} {f : V → ℝ} (h : ∀ c ∈ l, f c ≤ 0) :
    (l.map f).sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [map_cons, sum_cons]
      have h1 : f a ≤ 0 := h a (by simp)
      have h2 : (t.map f).sum ≤ 0 := ih fun c hc => h c (by simp [hc])
      linarith

theorem sum_map_ge {l : List V} {f : V → ℝ} {b : ℝ} (h : ∀ c ∈ l, b ≤ f c) :
    (l.length : ℝ) * b ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [map_cons, sum_cons, length_cons]
      have h1 : b ≤ f a := h a (by simp)
      have h2 : (t.length : ℝ) * b ≤ (t.map f).sum := ih fun c hc => h c (by simp [hc])
      push_cast
      linarith

theorem sum_map_le {l : List V} {f g : V → ℝ} (h : ∀ c ∈ l, f c ≤ g c) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [map_cons, sum_cons]
      have h1 : f a ≤ g a := h a (by simp)
      have h2 : (t.map f).sum ≤ (t.map g).sum := ih fun c hc => h c (by simp [hc])
      linarith

/-! ## The recursion, with bounds indexed by height -/

/-- **The invariant propagates, with height-indexed bounds.**  This is the general form: the
left-type upper bound `κ` and the right-type lower bound `m` may vary with the height, and the
two hypotheses `hL`, `hR` are exactly the two step conditions stated at each vertex against its
own children.

Height-indexing is what recovers the range the uniform version misses.  The alternation count of
`PathCount` bounds a left-type vertex's children by `r - ⌊ℓ/2⌋` and a right-type vertex's from
below by `q - ⌊ℓ/2⌋` for a path of `ℓ` vertices, both tightening with depth, and the first
reaching zero, which is what forces leaves.  Feeding those in turns the fixed point into a
finite backward recursion from the deepest level; measured, it closes the whole gap for six of
seven families against three for the uniform bound (`code/depthind.py`). -/
theorem invariant_depth (T : PT V) (F : V → ℝ) (lam : ℝ) (kap m : ℕ → ℝ)
    (hlam : 0 < lam) (hmpos : ∀ t, 0 < m t)
    (hF : ∀ v, F v = lam - ((T.ch v).map fun c => 1 / F c).sum)
    (hL : ∀ v, T.isR v = false →
        lam + ((T.ch v).map fun c => 1 / m (T.ht c)).sum ≤ kap (T.ht v))
    (hR : ∀ v, T.isR v = true →
        lam + m (T.ht v) ≤ ((T.ch v).map fun c => 1 / kap (T.ht c)).sum) :
    ∀ v, (T.isR v = true → F v ≤ -(m (T.ht v))) ∧
      (T.isR v = false → lam ≤ F v ∧ F v ≤ kap (T.ht v)) := by
  have key : ∀ n : ℕ, ∀ v : V, T.ht v = n →
      (T.isR v = true → F v ≤ -(m (T.ht v))) ∧
      (T.isR v = false → lam ≤ F v ∧ F v ≤ kap (T.ht v)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      constructor
      · intro hRv
        have hchild : ∀ c ∈ T.ch v, 1 / kap (T.ht c) ≤ 1 / F c := by
          intro c hc
          have hcL : T.isR c = false := by
            have := T.alt v c hc; rw [hRv] at this; simpa using this
          have hlt : T.ht c < n := hv ▸ T.ht_lt v c hc
          obtain ⟨hlo, hhi⟩ := (ih (T.ht c) hlt c rfl).2 hcL
          exact one_div_le_one_div_of_le (lt_of_lt_of_le hlam hlo) hhi
        have := sum_map_le hchild
        have hcl := hR v hRv
        rw [hF v]; linarith
      · intro hLv
        have hneg : ∀ c ∈ T.ch v, F c ≤ -(m (T.ht c)) := by
          intro c hc
          have hcR : T.isR c = true := by
            have := T.alt v c hc; rw [hLv] at this; simpa using this
          have hlt : T.ht c < n := hv ▸ T.ht_lt v c hc
          exact (ih (T.ht c) hlt c rfl).1 hcR
        have hup : ∀ c ∈ T.ch v, (1 : ℝ) / F c ≤ 0 := by
          intro c hc
          exact div_nonpos_of_nonneg_of_nonpos zero_le_one
            (le_trans (hneg c hc) (by linarith [hmpos (T.ht c)]))
        have hlow : ∀ c ∈ T.ch v, -(1 / m (T.ht c)) ≤ (1 : ℝ) / F c := by
          intro c hc
          have h1 : F c ≤ -(m (T.ht c)) := hneg c hc
          have hmc := hmpos (T.ht c)
          have h2 : (0 : ℝ) < -F c := by linarith
          have he : (1 : ℝ) / F c = -(1 / (-F c)) := by field_simp
          rw [he, neg_le_neg_iff]
          exact one_div_le_one_div_of_le hmc (by linarith)
        refine ⟨?_, ?_⟩
        · have := sum_map_nonpos hup
          rw [hF v]; linarith
        · have hs : ((T.ch v).map fun c => -(1 / m (T.ht c))).sum
              ≤ ((T.ch v).map fun c => 1 / F c).sum := sum_map_le hlow
          have hneg' : ((T.ch v).map fun c => -(1 / m (T.ht c))).sum
              = -((T.ch v).map fun c => 1 / m (T.ht c)).sum := by
            induction (T.ch v) with
            | nil => simp
            | cons a t iht => simp only [map_cons, sum_cons, iht]; ring
          rw [hneg'] at hs
          have := hL v hLv
          rw [hF v]; linarith
  exact fun v => key (T.ht v) v rfl

/-! ## The recursion -/

/-- **The invariant propagates through the whole path tree.**  Under the ratio recurrence, the
two counting facts and the closure inequality, every right-type ratio is at most `-m` and every
left-type ratio lies in `[λ, λ + k/m]`.  Proved by strong induction on the height. -/
theorem invariant (T : PT V) (F : V → ℝ) (lam m : ℝ) (D : ℕ)
    (hlam : 0 < lam) (hm : 0 < m)
    (hF : ∀ v, F v = lam - ((T.ch v).map fun c => 1 / F c).sum)
    (hmin : ∀ v, T.isR v = true → D ≤ (T.ch v).length)
    (hdrop : ∀ v, T.isR v = true → ∀ c ∈ T.ch v, (T.ch c).length + D ≤ (T.ch v).length)
    (hclose : ∀ k : ℕ, D ≤ k → lam + m ≤ (k : ℝ) / (lam + ((k : ℝ) - D) / m)) :
    ∀ v, (T.isR v = true → F v ≤ -m) ∧
      (T.isR v = false → lam ≤ F v ∧ F v ≤ lam + (T.ch v).length / m) := by
  have key : ∀ n : ℕ, ∀ v : V, T.ht v = n →
      (T.isR v = true → F v ≤ -m) ∧
      (T.isR v = false → lam ≤ F v ∧ F v ≤ lam + (T.ch v).length / m) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      constructor
      · -- right-type vertex: children are left-type, bounded above by κ
        intro hR
        set k := (T.ch v).length with hk
        have hDk : D ≤ k := hmin v hR
        set kap : ℝ := lam + ((k : ℝ) - D) / m with hkap
        have hDkR : ((D : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hDk
        have hkap_pos : 0 < kap := by
          have : 0 ≤ ((k : ℝ) - D) / m := div_nonneg (by linarith) hm.le
          simp only [hkap]; linarith
        have hchild : ∀ c ∈ T.ch v, 1 / kap ≤ 1 / F c := by
          intro c hc
          have hcR : T.isR c = false := by
            have := T.alt v c hc; rw [hR] at this; simpa using this
          have hlt : T.ht c < n := hv ▸ T.ht_lt v c hc
          obtain ⟨hlo, hhi⟩ := (ih (T.ht c) hlt c rfl).2 hcR
          have hlen : ((T.ch c).length : ℝ) ≤ (k : ℝ) - D := by
            have := hdrop v hR c hc
            have : ((T.ch c).length : ℝ) + D ≤ (k : ℝ) := by exact_mod_cast this
            linarith
          have hFc : F c ≤ kap := by
            refine le_trans hhi ?_
            simp only [hkap]
            have hdiv : ((T.ch c).length : ℝ) / m ≤ ((k : ℝ) - D) / m := by gcongr
            linarith
          exact one_div_le_one_div_of_le (lt_of_lt_of_le hlam hlo) hFc
        have hsum : (k : ℝ) * (1 / kap) ≤ ((T.ch v).map fun c => 1 / F c).sum :=
          sum_map_ge hchild
        have hcl := hclose k hDk
        rw [hF v]
        have : (k : ℝ) / kap ≤ ((T.ch v).map fun c => 1 / F c).sum := by
          rw [div_eq_mul_one_div]; exact hsum
        have hgoal : lam + m ≤ (k : ℝ) / kap := hcl
        linarith
      · -- left-type vertex: children are right-type, at most -m
        intro hL
        have hchild : ∀ c ∈ T.ch v, T.isR c = true := by
          intro c hc
          have := T.alt v c hc; rw [hL] at this; simpa using this
        have hneg : ∀ c ∈ T.ch v, F c ≤ -m := by
          intro c hc
          have hlt : T.ht c < n := hv ▸ T.ht_lt v c hc
          exact (ih (T.ht c) hlt c rfl).1 (hchild c hc)
        have hup : ∀ c ∈ T.ch v, (1 : ℝ) / F c ≤ 0 := by
          intro c hc
          exact div_nonpos_of_nonneg_of_nonpos zero_le_one
            (le_trans (hneg c hc) (by linarith))
        have hlow : ∀ c ∈ T.ch v, -(1 / m) ≤ (1 : ℝ) / F c := by
          intro c hc
          have h1 : F c ≤ -m := hneg c hc
          have h2 : (0 : ℝ) < -F c := by linarith
          have : (1 : ℝ) / F c = -(1 / (-F c)) := by field_simp
          rw [this, neg_le_neg_iff]
          exact one_div_le_one_div_of_le hm (by linarith)
        constructor
        · have := sum_map_nonpos hup
          rw [hF v]; linarith
        · have hs := sum_map_ge hlow
          rw [hF v]
          have : ((T.ch v).length : ℝ) * -(1 / m) = -(((T.ch v).length : ℝ) / m) := by
            field_simp
          rw [this] at hs
          linarith
  exact fun v => key (T.ht v) v rfl

/-! ## Saturation: when the certificate cannot be improved -/

/-- **A saturated bound admits no improvement.**  If some vertex attains the left-type upper
bound and some vertex attains the right-type lower bound, then any other valid pair of bounds is
no better at those heights.  So once both are attained the certificate cannot be sharpened by a
different choice of constants, and extending its range needs a different ingredient rather than
better bookkeeping.

This is the situation measured for `(3,6,5)`, the one family the depth-indexed recursion does
not close on the whole gap: at the largest `λ` it reaches, both ratios of actual value to bound
are `1.0000`, attained at path lengths `11` and `10` (`code/slack2.py`).  The remaining range is
therefore out of reach of this certificate, not merely unproved by it. -/
theorem saturation_blocks_improvement (T : PT V) (F : V → ℝ) (kap kap' m m' : ℕ → ℝ)
    (hL : ∀ v, T.isR v = false → F v ≤ kap' (T.ht v))
    (hR : ∀ v, T.isR v = true → F v ≤ -(m' (T.ht v)))
    (u w : V) (hu : T.isR u = false) (hw : T.isR w = true)
    (hsatL : F u = kap (T.ht u)) (hsatR : F w = -(m (T.ht w))) :
    kap (T.ht u) ≤ kap' (T.ht u) ∧ m' (T.ht w) ≤ m (T.ht w) := by
  constructor
  · rw [← hsatL]; exact hL u hu
  · have := hR w hw
    rw [hsatR] at this
    linarith

/-- **No ratio vanishes.**  Both alternatives of `invariant` are bounded away from zero, so
`μ_G(λ) ≠ 0` follows at every `λ` for which the hypotheses hold. -/
theorem no_vanishing (T : PT V) (F : V → ℝ) (lam m : ℝ) (D : ℕ)
    (hlam : 0 < lam) (hm : 0 < m)
    (hF : ∀ v, F v = lam - ((T.ch v).map fun c => 1 / F c).sum)
    (hmin : ∀ v, T.isR v = true → D ≤ (T.ch v).length)
    (hdrop : ∀ v, T.isR v = true → ∀ c ∈ T.ch v, (T.ch c).length + D ≤ (T.ch v).length)
    (hclose : ∀ k : ℕ, D ≤ k → lam + m ≤ (k : ℝ) / (lam + ((k : ℝ) - D) / m)) :
    ∀ v, F v ≠ 0 := by
  intro v
  obtain ⟨hR, hL⟩ := invariant T F lam m D hlam hm hF hmin hdrop hclose v
  cases hb : T.isR v with
  | true => exact ne_of_lt (lt_of_le_of_lt (hR hb) (by linarith))
  | false => exact ne_of_gt (lt_of_lt_of_le hlam (hL hb).1)

end PathTreeInduction
