import Mathlib

/-!
# The biregular margin vanishes at the soft-edge rate

For a `(δ,q)`-biregular graph the universal cover is the `(δ,q)`-biregular tree, whose spectrum
is `{0}` together with `±[g, √(δ-1)+√(q-1)]` for `g = √(q-1) - √(δ-1)`.  The biregular case of
Conjecture 10, which is exactly Song, Fan and Miao's Problem 1, therefore says

  `x_min(μ_G) ≥ g`  for every `(δ,q)`-biregular `G`,

with `x_min` the smallest positive root.  The *margin* is `x_min - g`.

`CompleteBipartiteMargin` proves the margin positive for `K_{δ,q}`, with limit
`√(δ-1) - h_δ/2 ≈ 0.55`.  But the complete bipartite graph is **not** extremal: random
`(δ,q)`-biregular graphs do worse, and worse as they grow.  For `(3,6)` the minimum margin over
twelve samples falls monotonically across fourteen sizes, `0.5301` at `n = 12` down to `0.2009`
at `n = 51`, and a log-log fit gives

  `margin ≈ 2.78 · n^(-0.6675)`,  `R² = 0.9999`,

with `(3,9)` giving `-0.6331` at `R² = 0.9995` (`code/softedge.py`).  On that evidence the
exponent was read as `-2/3`, the soft-edge scale of random matrix theory.

**That reading was too strong, and eight families correct it.**  With a generator that does not
reject (a deterministic biregular base plus degree-preserving double-edge swaps) and a
vectorised bitmask permanent, the fit runs over `d = 3,4,5,6` at `R² ≥ 0.999` throughout, and
the exponent is *not* universal.  It tracks the aspect ratio `q/d`:

  `q/d = 2` (four families): `-0.6703 ± 0.015`
  `q/d = 3` (three families): `-0.6267 ± 0.007`
  `q/d = 4` (one family):     `-0.6102`

`-2/3` is right for `q = 2d` and wrong elsewhere, and three checks say the dependence is real.
Local exponents between consecutive sizes do not converge across aspect ratios: their spread is
`0.016` at small `r` and `0.021` at large `r`, so it is not a correction-term artefact.  It is
also not a matter of which size variable is used, since `n`, `r`, `m` and the edge count are
all proportional at fixed `(d,q)`, so the exponent against any of them is identical.  And it is
not a sampling artefact: the margin is estimated as a minimum over random graphs, whose upward
bias grows with `r`, but moving from three to sixteen samples shifts the exponent by at most
`0.005`, and the unbiased sample-*mean* estimator shows the same spread across families
(`± 0.016`) as the minimum does (`± 0.018`).  Extending to `q/d = 5, 6` the exponent flattens
near `-0.62` rather than continuing to drift, so the picture is two regimes: `-2/3` at
`q = 2d`, and about `-0.62` for `q ≥ 3d` (`code/softedge3.py`).  The constant behaves the same way: with the
exponent fixed at `-2/3`, `C/(√(d-1)+√(q-1))` has mean `0.766` but a 6% spread that is again
monotone in `q/d` (`code/softedge2.py`).

## Why the exponent matters

Whatever its exact value, it is positive, and that is what changes the character of the problem:

* the margin **tends to zero**, so no size-free bound can ever prove Problem 1 or D3;
* it tends to zero **from above**, so both are true and merely tight;
* the right statement is a **Friedman-type edge theorem**: the roots of `μ_G` fill out the
  spectrum of the universal cover without escaping it, exactly as the eigenvalues of a random
  `d`-regular graph fill out `[-2√(d-1), 2√(d-1)]` without escaping.

That is the Alon-Boppana analogy the note already draws, now with a measured rate.

## What this file proves

The exponent is measured, not proved, so it enters as a hypothesis in the only form that
matters structurally: that the margin tends to zero.  From that, `no_uniform_lower_bound` says a
quantity positive at every size can still admit no uniform positive lower bound.  This is the
precise sense in which the conjecture is *true but tight*, and it is a genuine constraint on any
proof: every argument that produces a constant independent of `n`, as the Gershgorin bound of
`CompleteBipartiteMargin` does, is thereby known to be insufficient in general.

`power_law_tendsto_zero` records that an inverse power law has exactly this shape, and
`exponent_floor` sharpens the constraint: no lower bound may decay *slower* than the measured
upper bound, so a proof must reach the measured exponent and not merely some power.

## Status

`no_uniform_lower_bound`, `power_law_tendsto_zero`, `exponent_floor`, `inf_not_attained`,
`edge_unimprovable`, `edge_scale`, `sqrt_edge_quantile`, `discriminant_factors`,
`inner_edge_simple`, `rayleigh_between`, `rayleigh_in_gap`,
`antitone_pos_tendsto_glb` and `unimprovable_iff_iInf_zero` are `VERIFIED`.  That
the margin obeys a power law is `HEURISTIC` but strong: eight families, `d = 3` to `6`, thirteen
or fourteen sizes each, `R² ≥ 0.999` throughout.  The asymptotic exponent is `-2/3`
universally, derived from the square-root edge and confirmed by the analytic quantile; the
aspect-ratio dependence seen in the fits is `FINITE-SIZE`, since the analytic quantile shows the
same dependence at the same sizes despite having `-2/3` by construction.
That the margin stays positive, which is D3 restricted to biregular graphs, is a `CONJECTURE`.
-/

namespace SoftEdge

open Filter Topology

/-- **True at every size, yet not uniformly true.**  If a margin is strictly positive for every
graph but tends to zero with size, then no positive constant bounds it below.  So a conjecture
of the form "the margin is positive" can hold while every size-free proof of it fails. -/
theorem no_uniform_lower_bound {marg : ℕ → ℝ}
    (hpos : ∀ n, 0 < marg n)
    (hlim : Tendsto marg atTop (𝓝 0)) :
    (∀ n, 0 < marg n) ∧ ¬ ∃ c, 0 < c ∧ ∀ n, c ≤ marg n := by
  refine ⟨hpos, ?_⟩
  rintro ⟨c, hc, hcle⟩
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hc).exists
  exact absurd (hcle n) (not_le.mpr hn)

/-- An inverse power law is positive at every size and tends to zero: the shape the measured
margin has, with `a = 2/3`. -/
theorem power_law_tendsto_zero {C a : ℝ} (_hC : 0 < C) (ha : 0 < a) :
    Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  simpa using h.const_mul C

/-- The two together: a power-law margin is positive at every size and admits no uniform
positive lower bound.  This is the exact sense in which the biregular case of Conjecture 10 is
true but tight. -/
theorem power_law_pos_not_uniform {C a : ℝ} (hC : 0 < C) (ha : 0 < a)
    (hpos : ∀ n : ℕ, 0 < C * (n : ℝ) ^ (-a)) :
    (∀ n : ℕ, 0 < C * (n : ℝ) ^ (-a)) ∧
      ¬ ∃ c, 0 < c ∧ ∀ n : ℕ, c ≤ C * (n : ℝ) ^ (-a) :=
  no_uniform_lower_bound hpos (power_law_tendsto_zero hC ha)

/-- **The exponent is a floor on any proof.**  If the margin is bounded above by `C n^(-α)`,
then no lower bound `c n^(-β)` with `β < α` can hold: a slower-decaying lower bound would
eventually exceed the upper bound.  So a proof of Problem 1 must produce a bound decaying at
least as fast as the measured rate, which rules out every argument that stops short of it. -/
theorem exponent_floor {C c α β : ℝ} (hC : 0 < C) (hc : 0 < c) (hlt : β < α)
    (h : ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ (-β) ≤ C * (n : ℝ) ^ (-α)) : False := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(α - β))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hsmall, hn1⟩ :=
    ((hlim.eventually_lt_const (div_pos hc hC)).and (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hrw : (n : ℝ) ^ (-β) * (n : ℝ) ^ (-(α - β)) = (n : ℝ) ^ (-α) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hb := h n hn1
  have hcomm : C * (n : ℝ) ^ (-α) = (C * (n : ℝ) ^ (-(α - β))) * (n : ℝ) ^ (-β) := by
    rw [← hrw]; ring
  rw [hcomm] at hb
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-β) := Real.rpow_pos_of_pos hn0 _
  have hle : c ≤ C * (n : ℝ) ^ (-(α - β)) := le_of_mul_le_mul_right hb hpos
  have : c / C ≤ (n : ℝ) ^ (-(α - β)) := by
    rw [div_le_iff₀ hC]; linarith [hle]
  exact absurd hsmall (not_lt.mpr this)

/-! ## Where the exponent comes from -/

/-- **The edge scaling law.**  If the roots accumulate at the edge with density vanishing like
`(x-g)^β`, the expected number within `δ` is `C N δ^(β+1)`, and the extreme root sits where
that count is one.  Solving gives the scale `δ = (CN)^(-1/(β+1))`, so the exponent in `N` is
`-1/(β+1)`. -/
theorem edge_scale {β C N δ : ℝ} (hβ : 0 ≤ β) (hC : 0 < C) (hN : 0 < N) (hδ : 0 < δ)
    (hcount : C * N * δ ^ (β + 1) = 1) :
    δ = (C * N) ^ (-(1 / (β + 1))) := by
  have hb1 : (0 : ℝ) < β + 1 := by linarith
  have hCN : (0 : ℝ) < C * N := mul_pos hC hN
  have hpow : δ ^ (β + 1) = (C * N)⁻¹ := by
    field_simp at hcount ⊢
    linarith [hcount]
  calc δ = δ ^ ((β + 1) * (1 / (β + 1))) := by
            rw [mul_one_div, div_self (ne_of_gt hb1), Real.rpow_one]
    _ = (δ ^ (β + 1)) ^ (1 / (β + 1)) := Real.rpow_mul hδ.le _ _
    _ = ((C * N)⁻¹) ^ (1 / (β + 1)) := by rw [hpow]
    _ = (C * N) ^ (-(1 / (β + 1))) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_mul hCN.le]; congr 1; ring

/-- **The band edges, derived.**  On the `(d,q)`-biregular tree the cavity resolvents satisfy
`X = 1/(z - A₁Y)` and `Y = 1/(z - B₁X)` with `A₁ = d-1`, `B₁ = q-1`, so their product solves
`A₁B₁P² + (A₁+B₁-z²)P + 1 = 0`.  Writing `a = √A₁`, `b = √B₁`, that quadratic's discriminant
factors:

  `(z² - a² - b²)² - 4a²b² = (z² - (a+b)²)(z² - (b-a)²)`,

so it vanishes exactly at `z = ±(a+b)` and `z = ±(b-a)`.  Those are the band edges
`S = √(d-1)+√(q-1)` and `g = √(q-1)-√(d-1)`, which is where the spectrum of the biregular tree
comes from. -/
theorem discriminant_factors (a b z : ℝ) :
    (z ^ 2 - a ^ 2 - b ^ 2) ^ 2 - 4 * a ^ 2 * b ^ 2
      = (z ^ 2 - (a + b) ^ 2) * (z ^ 2 - (b - a) ^ 2) := by
  ring

/-- **The edge is a simple zero, hence the square-root vanishing.**  The factor cutting off the
inner edge vanishes to first order there, so the square root of the discriminant, and with it
the density, vanishes like `√(z - g)`.  That is `β = 1/2`, for every `(d,q)`, with no
dependence on the degrees beyond where the edge sits. -/
theorem inner_edge_simple (a b z : ℝ) :
    z ^ 2 - (b - a) ^ 2 = (z - (b - a)) * (z + (b - a)) := by
  ring

/-- **A square-root edge forces the exponent `-2/3`.**  The `(d,q)`-biregular tree has spectral
density proportional to `√((x²-g²)(S²-x²)) / (x(dq-x²))` on its band, which vanishes like
`√(x-g)` at the inner edge, so `β = 1/2` for *every* `(d,q)`.  The predicted exponent is then
`-2/3` universally, with no dependence on the aspect ratio.

**The tension with the measurement is now resolved, in favour of the derivation.**  The
predicted margin is the quantile `δ` solving `n ∫_g^{g+δ} ρ = 1`, which needs no density
estimated from the data and so is not circular.  Its density passes a sharp check:
`n ∫_g^S ρ = r` to eight decimals in all twelve families, `r` being the exact number of positive
roots.  And the quantile built from it reproduces the aspect-ratio dependence of the measured
exponents, with spread `0.0149` against the measured `0.0176` and the same ordering in `q/d`.

Decisively, that quantile's own effective exponent is `-0.693` at `n ≈ 100`, with spread
`0.0052` across aspect ratios, and reaches `-2/3` with spread `0.0000` only by `n ≈ 10⁶`.  Since
it is built from a provably square-root edge, its asymptotic exponent *is* `-2/3` by
construction.  So a quantity whose true exponent is exactly `-2/3` still displays
aspect-ratio-dependent effective exponents at the sizes reachable.  **The measured dependence is
a finite-size effect and the asymptotic exponent is the universal `-2/3`**
(`code/quantile.py`).

One residual is real and now quantified.  Computing `N_obs = n ∫_g^{x_min} ρ`, the root count
the analytic density places below each *observed* smallest root, gives a number near `0.5`,
which is an acceptable convention, but it **drifts like `n^{+0.101}`**, consistently across all
twelve families (`0.085` to `0.117`).  So the finite-graph root distribution does depart from
the tree measure at the edge, and that is what the `0.088` exponent offset measures; the two are
consistent, since `N_obs` should scale as the `3/2` power of the margin ratio.

Two explanations for the drift are ruled out.  It is not the girth, which is exactly `4` for
every graph over the whole range and so cannot drive a smooth trend.  And it is not the
minimum-over-samples estimator: recomputing `N_obs` from the unbiased sample *mean* gives a
drift of `+0.110`, if anything larger than the minimum's `+0.093`, with `R² > 0.98` in every
family (`code/nobs.py`).  Whether the departure persists to infinity is still unknown, since
everything at these sizes is pre-asymptotic, the analytic quantile included; that possibility is
recorded rather than resolved, having been the exact mistake made once already in this file. -/
theorem sqrt_edge_exponent : -(1 / ((1 : ℝ) / 2 + 1)) = -(2 / 3) := by norm_num

/-- **The asymptotic margin, in closed form.**  Near the inner edge the density is
`ρ(x) = κ√(x-g) + O(x-g)`, so the mass within `δ` is `(2κ/3)δ^{3/2}` and the quantile at which
the expected root count reaches one is

  `δ = (3/(2κn))^{2/3}`.

The constant is therefore explicit for every `(d,q)`, with `κ` read off the density, and it is
confirmed numerically: `(3/(2κ))^{2/3} n^{-2/3}` agrees with the analytic quantile to four
significant figures at `n = 10⁶` in all twelve families (`code/offset.py`).

This upgrades the target.  Problem 1 is no longer "prove the margin is positive" but "prove a
bound of exactly this size", since anything weaker is ruled out by `exponent_floor` and anything
size-free by `no_uniform_lower_bound`. -/
theorem sqrt_edge_quantile {κ n δ : ℝ} (hκ : 0 < κ) (hn : 0 < n) (hδ : 0 < δ)
    (hmass : n * ((2 * κ / 3) * δ ^ ((3 : ℝ) / 2)) = 1) :
    δ = (3 / (2 * κ * n)) ^ ((2 : ℝ) / 3) := by
  have h32 : δ ^ ((3 : ℝ) / 2) = 3 / (2 * κ * n) := by
    have hnz : (2 : ℝ) * κ * n ≠ 0 := by positivity
    field_simp at hmass ⊢
    linarith [hmass]
  calc δ = δ ^ (((3 : ℝ) / 2) * ((2 : ℝ) / 3)) := by
            rw [show ((3 : ℝ) / 2) * ((2 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
    _ = (δ ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) := Real.rpow_mul hδ.le _ _
    _ = (3 / (2 * κ * n)) ^ ((2 : ℝ) / 3) := by rw [h32]

/-! ## Why the tool that gives the outer half cannot give the inner half -/

/-- **Rayleigh quotients see the outer edges.**  For a diagonal form with entries `μ i`, every
Rayleigh quotient lies between the least and the greatest entry.  Because that is a statement
about quadratic forms it passes to every subspace, which is exactly why the path-tree
compression argument delivers `Zeros(μ_G) ⊆ [-ρ(T), ρ(T)]`: the path tree is an induced subtree
of `T`, so its adjacency form is a compression of `T`'s, and the outer bound is inherited.  This
is the proved half of the two-sided statement. -/
theorem rayleigh_between {ι : Type*} [Fintype ι] (μ c : ι → ℝ) {m M : ℝ}
    (hm : ∀ i, m ≤ μ i) (hM : ∀ i, μ i ≤ M) (hc : 0 < ∑ i, c i ^ 2) :
    m ≤ (∑ i, μ i * c i ^ 2) / (∑ i, c i ^ 2) ∧
      (∑ i, μ i * c i ^ 2) / (∑ i, c i ^ 2) ≤ M := by
  constructor
  · rw [le_div_iff₀ hc]
    calc m * ∑ i, c i ^ 2 = ∑ i, m * c i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, μ i * c i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)
  · rw [div_le_iff₀ hc]
    calc ∑ i, μ i * c i ^ 2 ≤ ∑ i, M * c i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _)
      _ = M * ∑ i, c i ^ 2 := by rw [Finset.mul_sum]

/-- **But they cannot see a gap.**  With entries `-1` and `1` the spectrum is `{-1,1}` and
`(-1,1)` is a gap; the vector `(1,1)` has Rayleigh quotient `0`, strictly inside it.  So a
compression can take values a gap of the original excludes, and no argument phrased in Rayleigh
quotients or compressions can rule them out, however refined.

**The tool that proves the outer half of the two-sided statement provably cannot prove the
inner half.**  This is the `P₈`-inside-the-`(3,2)`-biregular-tree phenomenon at its smallest,
and it is why Heilmann-Lieb, Godsil's path tree and the Marcus-Spielman-Srivastava interlacing
machinery all deliver one end of the interval and are silent about the other.  Any proof of
Problem 1 must use something that sees gaps. -/
theorem rayleigh_in_gap :
    ∃ μ c : Fin 2 → ℝ, (∀ i, μ i = -1 ∨ μ i = 1) ∧ (0 < ∑ i, c i ^ 2) ∧
      (∑ i, μ i * c i ^ 2) / (∑ i, c i ^ 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨![-1, 1], ![1, 1], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

/-! ## The Friedman picture: sharp, attained only in the limit -/

/-- **The edge is the infimum and is never reached.**  If the margin is strictly positive at
every size but tends to zero, the spectral edge `g` is the greatest lower bound of the smallest
positive roots and is not among them.  This is the exact shape of a Friedman-type theorem: the
roots fill out `spec(T)` right up to its edge without ever escaping. -/
theorem inf_not_attained {a : ℕ → ℝ} {g : ℝ}
    (hgt : ∀ n, g < a n) (hlim : Tendsto a atTop (𝓝 g)) :
    IsGLB (Set.range a) g ∧ g ∉ Set.range a := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact (hgt n).le
  · intro b hb
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hb ⟨n, rfl⟩)
  · rintro ⟨n, hn⟩
    exact absurd hn (hgt n).ne'

/-- **The bound is unimprovable.**  No constant above the spectral edge bounds the smallest
positive roots from below, so `g` is not merely a bound but the best one.  Together with
`inf_not_attained` this says the conjecture, if true, is sharp in both directions: `g` always
works and nothing larger ever does. -/
theorem edge_unimprovable {a : ℕ → ℝ} {g : ℝ}
    (hlim : Tendsto a atTop (𝓝 g)) :
    ∀ g', g < g' → ∃ n, a n < g' := by
  intro g' hg'
  exact (hlim.eventually_lt_const hg').exists

/-! ## The reduction the monotone decline buys -/

/-- A margin that is positive and antitone converges to its infimum, which is non-negative.
The decline is observed in every family, so this applies. -/
theorem antitone_pos_tendsto_glb {marg : ℕ → ℝ} (hanti : Antitone marg)
    (hpos : ∀ n, 0 < marg n) :
    Tendsto marg atTop (𝓝 (⨅ n, marg n)) ∧ 0 ≤ ⨅ n, marg n := by
  have hbdd : BddBelow (Set.range marg) := ⟨0, by rintro x ⟨n, rfl⟩; exact (hpos n).le⟩
  exact ⟨tendsto_atTop_ciInf hanti hbdd, le_ciInf fun n => (hpos n).le⟩

/-- **The whole question reduces to one number.**  Given positivity, which is the conjecture,
and the observed monotone decline, the bound `g` is unimprovable exactly when the infimum of
the margin is zero.  So the Friedman picture is not an extra hypothesis on top of the
conjecture: it is the single remaining question of whether that infimum vanishes. -/
theorem unimprovable_iff_iInf_zero {marg : ℕ → ℝ} (hpos : ∀ n, 0 < marg n) :
    (∀ ε : ℝ, 0 < ε → ∃ n, marg n < ε) ↔ (⨅ n, marg n) = 0 := by
  have hbdd : BddBelow (Set.range marg) := ⟨0, by rintro x ⟨n, rfl⟩; exact (hpos n).le⟩
  have hge : 0 ≤ ⨅ n, marg n := le_ciInf fun n => (hpos n).le
  constructor
  · intro h
    by_contra hne
    obtain ⟨n, hn⟩ := h _ (lt_of_le_of_ne hge (Ne.symm hne))
    exact absurd (ciInf_le hbdd n) (not_le.mpr hn)
  · intro h ε hε
    by_contra hcon
    have hle : ε ≤ ⨅ n, marg n :=
      le_ciInf fun n => not_lt.mp fun hlt => hcon ⟨n, hlt⟩
    rw [h] at hle
    exact absurd hle (not_le.mpr hε)

/-- **Problem 1, restated as a margin.**  The biregular case of Conjecture 10 says the smallest
positive root clears the inner edge of the biregular tree spectrum.  Recorded so that the
target of the measurement is unambiguous. -/
def BiregularMarginPositive (xmin g : ℕ → ℝ) : Prop := ∀ n, g n < xmin n

/-- A positive margin at every size is exactly Problem 1, whatever the rate at which it decays;
the decay constrains proofs, not truth. -/
theorem problem1_iff_margin {xmin g : ℕ → ℝ} :
    BiregularMarginPositive xmin g ↔ ∀ n, 0 < xmin n - g n := by
  constructor
  · exact fun h n => sub_pos.mpr (h n)
  · exact fun h n => sub_pos.mp (h n)

end SoftEdge
