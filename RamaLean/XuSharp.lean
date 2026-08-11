import Mathlib

/-!
# Xu's constant is attained, at every rank

Xu conjectures `maxroot μ ≤ (√(a-1) + √(b-1))²` for a tight family of rank-`b` projections. The
measurements left open whether that constant is the truth at `b ≥ 3` or merely an upper bound
there: an adversarial search reached `0.939` of it at `(a,b) = (3,2)` but only `0.739` at
`(4,3)` and `0.726` at `(5,4)`, which is equally consistent with the constant being sharp and
the search being in the wrong place. This file records the three steps that settle it, in the
abstract form each of them actually has.

## The argument

Write `ρ = √(a-1) + √(b-1)`, the spectral radius of the `(a,b)`-biregular tree.

1. **The bridge.** For an `a`-regular `b`-uniform hypergraph `H` the coordinate projections onto
   the hyperedges are a tight rank-`b` family, and their mixed characteristic polynomial satisfies
   `μ(t²) = t^{n-q} μ_{I(H)}(t)` with `I(H)` the incidence bipartite graph, which is
   `(a,b)`-biregular. `bridge_roots` is that step: a factorisation of this shape identifies the
   positive roots of `μ` with the squares of the positive roots of `μ_I`, whatever the cofactor,
   provided only that it does not vanish. Verified numerically against the MSS definition on four
   hypergraphs (`code/xu_sharp.py`, control A) and shown to fail off the coordinate locus, which
   is where the content of the conjecture lives.

2. **The ceiling.** Godsil's bound puts every root of `μ_{I(H)}` in `[-ρ, ρ]`, so by step 1 every
   root of `μ` is at most `ρ²`. Xu's inequality is therefore a theorem for coordinate families at
   every `b`, not a conjecture.

3. **The floor.** The greatest root of a matching polynomial is monotone under subgraphs, and a
   graph of girth `> 2r` contains the ball `B_r` of the biregular tree, whose largest eigenvalue
   increases to `ρ`. Since `(a,b)`-biregular graphs of arbitrary girth exist, the class contains
   members with ratio arbitrarily close to one.

Steps 2 and 3 are exactly the hypotheses of `sharp_of_approach`, whose conclusion is that the
supremum over the class equals `ρ²`: the constant is attained in the limit and cannot be lowered,
at every `b`. `approach_of_tendsto` is the form step 3 is delivered in, a sequence rather than an
`ε`.

## Status

`bridge_roots`, `sharp_of_approach`, `approach_of_tendsto`, `sharp_of_ladder` and
`sharp_transfers_to_squares` are `VERIFIED`. Godsil's bound and subgraph monotonicity are
classical and are hypotheses here, not claims; `λ_max(B_r) ↑ ρ` is `HEURISTIC`, measured to
`r = 12` at five pairs `(a,b)` in `code/xu_sharp.py`.

## What this does not say

Nothing about the non-coordinate case, which is the whole of Xu's conjecture beyond this. The
value of settling the coordinate case is that it fixes the constant: any proof of the general
statement must produce exactly `(√(a-1) + √(b-1))²` and no better, and any attempted improvement
of the constant is refuted before it starts.
-/

namespace XuSharp

open Filter Topology

/-- **The bridge.**  A factorisation `μ(t²) = c(t)·μ_I(t)` with `c` nonvanishing on the positives
identifies the positive roots of `μ` with the squares of the positive roots of `μ_I`.  For
coordinate families `c(t) = t^{n-q}` and `μ_I` is the matching polynomial of the incidence
bipartite graph, so this is the step that turns a mixed characteristic polynomial into an ordinary
matching polynomial on an `(a,b)`-biregular graph. -/
theorem bridge_roots (μ μI c : ℝ → ℝ) (h : ∀ t : ℝ, μ (t ^ 2) = c t * μI t)
    (hc : ∀ t : ℝ, 0 < t → c t ≠ 0) {y : ℝ} (hy : 0 < y) :
    μ y = 0 ↔ μI (Real.sqrt y) = 0 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hb : μ y = c (Real.sqrt y) * μI (Real.sqrt y) := by
    have := h (Real.sqrt y)
    rwa [Real.sq_sqrt hy.le] at this
  constructor
  · intro h0
    rw [h0] at hb
    exact (mul_eq_zero.mp hb.symm).resolve_left (hc _ hs)
  · intro h0
    rw [hb, h0, mul_zero]

/-- **Sharpness.**  A ceiling that every member respects, together with members exceeding every
value below it, pins the supremum exactly.  This is the shape of the conclusion: step 2 supplies
the ceiling and step 3 the approach. -/
theorem sharp_of_approach {S : Set ℝ} (hne : S.Nonempty) (ρ : ℝ)
    (hub : ∀ y ∈ S, y ≤ ρ) (happ : ∀ w < ρ, ∃ y ∈ S, w < y) :
    sSup S = ρ :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt hne hub happ

/-- The approach hypothesis in the form the construction delivers it: a sequence inside the class
converging to the ceiling.  The balls `B_r` give exactly this, one member per radius. -/
theorem approach_of_tendsto {S : Set ℝ} {f : ℕ → ℝ} (hmem : ∀ n, f n ∈ S) (ρ : ℝ)
    (hlim : Tendsto f atTop (𝓝 ρ)) : ∀ w < ρ, ∃ y ∈ S, w < y := by
  intro w hw
  by_contra hcon
  push Not at hcon
  have : ρ ≤ w := le_of_tendsto hlim (Eventually.of_forall fun n => hcon (f n) (hmem n))
  linarith

/-- **The two steps assembled.**  A ceiling plus a converging ladder inside the class gives the
supremum.  Applied with `S` the set of ratios `maxroot μ / ρ²` over coordinate families, `ρ = 1`
and `f r` the ball ratio at radius `r`, this says the ratio has supremum one: Xu's constant is
attained and cannot be lowered. -/
theorem sharp_of_ladder {S : Set ℝ} {f : ℕ → ℝ} (ρ : ℝ)
    (hmem : ∀ n, f n ∈ S) (hub : ∀ y ∈ S, y ≤ ρ) (hlim : Tendsto f atTop (𝓝 ρ)) :
    sSup S = ρ :=
  sharp_of_approach ⟨f 0, hmem 0⟩ ρ hub (approach_of_tendsto hmem ρ hlim)

/-- Sharpness survives the change of variable `y = t²` of the bridge: a ladder approaching `ρ` in
the matching variable is a ladder approaching `ρ²` in the `μ` variable, since squaring is
continuous.  This is why step 3 may be run on the biregular tree, where the object is an
adjacency eigenvalue, rather than on the mixed characteristic polynomial itself. -/
theorem sharp_transfers_to_squares {f : ℕ → ℝ} (ρ : ℝ) (hlim : Tendsto f atTop (𝓝 ρ)) :
    Tendsto (fun n => f n ^ 2) atTop (𝓝 (ρ ^ 2)) :=
  hlim.pow 2

/-- The conclusion in the form it is used against the conjecture: if the ceiling is attained in the
limit then no smaller constant works, so any strengthening of Xu's inequality is false.  Stated
contrapositively, which is how one applies it. -/
theorem no_smaller_constant {S : Set ℝ} {f : ℕ → ℝ} (ρ : ℝ)
    (hmem : ∀ n, f n ∈ S) (hlim : Tendsto f atTop (𝓝 ρ)) {ρ' : ℝ} (hlt : ρ' < ρ) :
    ¬ (∀ y ∈ S, y ≤ ρ') := by
  intro hbad
  obtain ⟨y, hyS, hy⟩ := approach_of_tendsto hmem ρ hlim ρ' hlt
  exact absurd (hbad y hyS) (not_le.mpr hy)

end XuSharp
