import Mathlib

/-!
# The complete bipartite band

Paper 2 leaves the biregular case `min(a,b) ≥ 3` open, and `K_{3,4}` is the smallest
instance.  This file settles the whole complete bipartite family at `d = 1`.

The matching polynomial of `K_{p,q}` is, with `α = q - p`,

  `μ_{K_{p,q}}(x) = x^{q-p} (-1)^p p! L_p^{(α)}(x²)`,

so the nonzero roots are the square roots of the zeros of a Laguerre polynomial.  Those
zeros are the eigenvalues of the `p × p` symmetric tridiagonal Jacobi matrix

  `J k k = 2k + α + 1`,   `J k (k+1) = J (k+1) k = √((k+1)(k+α+1))`.

The claim to prove is that they lie in the band of the `(q,p)`-biregular tree, i.e.

  `|t - (p+q-2)| ≤ 2√((p-1)(q-1))`,

because `(√(q-1) ± √(p-1))² = (p+q-2) ± 2√((p-1)(q-1))` (`band_endpoints` below).

The proof is Gershgorin applied to `J - (p+q-2)I`, and every row inequality collapses to
a single lemma, `sqrt_step`, which is the arithmetic–geometric mean inequality:

  `√(u(u+α)) + 1 ≤ √((u+1)(u+1+α))`   ⟺   `√(u(u+α)) ≤ u + α/2`   ⟺   `0 ≤ α²`.

Writing `g α u = √(u(u+α)) - u`, the interior row `k` has Gershgorin radius exactly
`2p - 2 + g α k + g α (k+1)`; `sqrt_step` makes `g` monotone in unit steps, so the
maximum is at `k = p-2`, where the bound is `sqrt_step` itself at `u = p-2`.

The bound is sharp: at `p = q` every interior row attains it exactly.  It genuinely needs
`p ≥ 2`; at `p = 1` the single eigenvalue is `q` while the band degenerates to `{q-1}`.
-/

namespace LaguerreBand

open Finset

/-! ## The arithmetic–geometric mean step -/

/-- **AM–GM.**  The geometric mean of `u` and `u + α` is at most their arithmetic mean.
This is the only inequality the whole file rests on. -/
theorem sqrt_amgm {u α : ℝ} (hu : 0 ≤ u) (hα : 0 ≤ α) :
    Real.sqrt (u * (u + α)) ≤ u + α / 2 := by
  have hnn : (0:ℝ) ≤ u + α / 2 := by linarith
  have hle : u * (u + α) ≤ (u + α / 2) ^ 2 := by nlinarith [sq_nonneg α]
  calc Real.sqrt (u * (u + α)) ≤ Real.sqrt ((u + α / 2) ^ 2) := Real.sqrt_le_sqrt hle
    _ = u + α / 2 := Real.sqrt_sq hnn

/-- **The step lemma.**  Equivalent to `sqrt_amgm`, and the engine of every row bound. -/
theorem sqrt_step {u α : ℝ} (hu : 0 ≤ u) (hα : 0 ≤ α) :
    Real.sqrt (u * (u + α)) + 1 ≤ Real.sqrt ((u + 1) * (u + 1 + α)) := by
  have hprod : (0:ℝ) ≤ u * (u + α) := by positivity
  have hs : Real.sqrt (u * (u + α)) ^ 2 = u * (u + α) := Real.sq_sqrt hprod
  have hnn : (0:ℝ) ≤ Real.sqrt (u * (u + α)) + 1 := by positivity
  have hsq : (Real.sqrt (u * (u + α)) + 1) ^ 2 ≤ (u + 1) * (u + 1 + α) := by
    have := sqrt_amgm hu hα
    nlinarith [hs]
  calc Real.sqrt (u * (u + α)) + 1
      = Real.sqrt ((Real.sqrt (u * (u + α)) + 1) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((u + 1) * (u + 1 + α)) := Real.sqrt_le_sqrt hsq

/-! ## The gap function -/

/-- `g α u = √(u(u+α)) - u`, the amount by which the off-diagonal entry exceeds its index. -/
noncomputable def g (α u : ℝ) : ℝ := Real.sqrt (u * (u + α)) - u

theorem g_nonneg {u α : ℝ} (hu : 0 ≤ u) (hα : 0 ≤ α) : 0 ≤ g α u := by
  have h : u * u ≤ u * (u + α) := by nlinarith
  have := Real.sqrt_le_sqrt h
  rw [show u * u = u ^ 2 by ring, Real.sqrt_sq hu] at this
  simpa [g] using this

/-- `sqrt_step` says exactly that `g` does not decrease under a unit step. -/
theorem g_le_succ {u α : ℝ} (hu : 0 ≤ u) (hα : 0 ≤ α) : g α u ≤ g α (u + 1) := by
  have := sqrt_step hu hα
  simp only [g]
  linarith

/-- Monotonicity of `g` along the integers, by iterating `g_le_succ`. -/
theorem g_le_of_le {α : ℝ} (hα : 0 ≤ α) : ∀ {k m : ℕ}, k ≤ m → g α k ≤ g α m := by
  intro k m hkm
  induction m with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · have hstep : g α (n : ℝ) ≤ g α ((n : ℝ) + 1) :=
          g_le_succ (by positivity) hα
        have : g α (k : ℝ) ≤ g α (n : ℝ) := ih (Nat.lt_succ_iff.mp h)
        calc g α (k : ℝ) ≤ g α (n : ℝ) := this
          _ ≤ g α ((n : ℝ) + 1) := hstep
          _ = g α ((n + 1 : ℕ) : ℝ) := by push_cast; ring_nf
      · have : k = n + 1 := le_antisymm hkm h
        subst this; rfl

/-! ## The Gershgorin row radii -/

/-- The Gershgorin radius of interior row `k` of `J - (p+q-2)I`: the shifted diagonal has
absolute value `2p - 3 - 2k`, and the two off-diagonal entries are `√(k(k+α))` and
`√((k+1)(k+1+α))`. -/
noncomputable def rowRadius (α P k : ℝ) : ℝ :=
  (2 * P - 3 - 2 * k) + Real.sqrt (k * (k + α)) + Real.sqrt ((k + 1) * (k + 1 + α))

/-- The radius of interior row `k`, rewritten through `g`.  The index cancels exactly,
which is why the bound is sharp at `α = 0`. -/
theorem rowRadius_eq (α P k : ℝ) :
    rowRadius α P k = 2 * P - 2 + g α k + g α (k + 1) := by
  simp only [rowRadius, g]; ring

/-- **Interior rows.**  For `k ≤ p - 2` the Gershgorin radius is at most the band radius
`2√((p-1)(p-1+α))`.  Monotonicity of `g` reduces to `k = p-2`, where the statement is
`sqrt_step` at `u = p-2`. -/
theorem rowRadius_le {α : ℝ} (hα : 0 ≤ α) {p k : ℕ} (hp : 2 ≤ p) (hk : k + 2 ≤ p) :
    rowRadius α p k ≤ 2 * Real.sqrt (((p : ℝ) - 1) * (((p : ℝ) - 1) + α)) := by
  have hp2 : ((p : ℝ) - 2) = ((p - 2 : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ p := hp
    push_cast [Nat.cast_sub this]; ring
  have hp1 : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ p := le_trans (by norm_num) hp
    push_cast [Nat.cast_sub this]; ring
  -- `g α k ≤ g α (p-2)` and `g α (k+1) ≤ g α (p-1)`
  have h1 : g α (k : ℝ) ≤ g α ((p : ℝ) - 2) := by
    rw [hp2]; exact g_le_of_le hα (by omega)
  have h2 : g α ((k : ℝ) + 1) ≤ g α ((p : ℝ) - 1) := by
    rw [hp1, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    exact g_le_of_le hα (by omega)
  -- at `k = p-2` the bound is `sqrt_step` at `u = p-2`
  have hu : (0:ℝ) ≤ (p : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hstep : Real.sqrt (((p : ℝ) - 2) * (((p : ℝ) - 2) + α)) + 1
      ≤ Real.sqrt (((p : ℝ) - 1) * (((p : ℝ) - 1) + α)) := by
    have h := sqrt_step hu hα
    have e1 : ((p : ℝ) - 2 + 1) = (p : ℝ) - 1 := by ring
    rwa [e1] at h
  rw [rowRadius_eq]
  simp only [g] at h1 h2 ⊢
  linarith

/-- **The last row.**  Row `p-1` has shifted diagonal `1` and a single off-diagonal entry
`√((p-1)(p-1+α))`, so its radius is within the band as soon as `(p-1)(p-1+α) ≥ 1`. -/
theorem lastRow_le {α : ℝ} (hα : 0 ≤ α) {p : ℕ} (hp : 2 ≤ p) :
    1 + Real.sqrt (((p : ℝ) - 1) * (((p : ℝ) - 1) + α))
      ≤ 2 * Real.sqrt (((p : ℝ) - 1) * (((p : ℝ) - 1) + α)) := by
  have hp1 : (1:ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hone : (1:ℝ) ≤ ((p : ℝ) - 1) * (((p : ℝ) - 1) + α) := by nlinarith
  have : (1:ℝ) ≤ Real.sqrt (((p : ℝ) - 1) * (((p : ℝ) - 1) + α)) := by
    have := Real.sqrt_le_sqrt hone
    simpa using this
  linarith

/-! ## The band endpoints -/

/-- **The band is the biregular tree band.**  `(√(q-1) ± √(p-1))² = (p+q-2) ± 2√((p-1)(q-1))`,
so the disc `|t - (p+q-2)| ≤ 2√((p-1)(q-1))` is exactly `[(√(q-1)-√(p-1))², (√(q-1)+√(p-1))²]`,
the square of the `(q,p)`-biregular tree band. -/
theorem band_endpoints {P Q : ℝ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) :
    (Real.sqrt (Q - 1) + Real.sqrt (P - 1)) ^ 2
        = (P + Q - 2) + 2 * Real.sqrt ((P - 1) * (Q - 1))
      ∧ (Real.sqrt (Q - 1) - Real.sqrt (P - 1)) ^ 2
        = (P + Q - 2) - 2 * Real.sqrt ((P - 1) * (Q - 1)) := by
  have hp : (0:ℝ) ≤ P - 1 := by linarith
  have hq : (0:ℝ) ≤ Q - 1 := by linarith
  have hsp : Real.sqrt (P - 1) ^ 2 = P - 1 := Real.sq_sqrt hp
  have hsq : Real.sqrt (Q - 1) ^ 2 = Q - 1 := Real.sq_sqrt hq
  have hmul : Real.sqrt ((P - 1) * (Q - 1)) = Real.sqrt (P - 1) * Real.sqrt (Q - 1) := by
    rw [Real.sqrt_mul hp]
  constructor <;> · rw [hmul]; nlinarith [hsp, hsq]

/-! ## Gershgorin -/

/-- A uniform Gershgorin band: if every row of `J` has `|J k k - c|` plus its off-diagonal
absolute row sum at most `R`, then every eigenvalue lies within `R` of `c`. -/
theorem eigenvalue_band {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℝ} {c R : ℝ}
    (h : ∀ k, |J k k - c| + ∑ j ∈ univ.erase k, |J k j| ≤ R)
    {t : ℝ} (ht : Module.End.HasEigenvalue (Matrix.toLin' J) t) :
    |t - c| ≤ R := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball ht
  rw [Metric.mem_closedBall, Real.dist_eq] at hk
  have hk' : |t - J k k| ≤ ∑ j ∈ univ.erase k, |J k j| := by
    simpa [Real.norm_eq_abs] using hk
  have htri : |t - c| ≤ |t - J k k| + |J k k - c| := _root_.abs_sub_le _ _ _
  linarith [h k]

/-! ## The theorem -/

/-- **The complete bipartite band.**  If every Gershgorin row radius of the shifted Jacobi
matrix is within the band radius, every zero of the Laguerre factor, hence every squared
nonzero root of `μ_{K_{p,q}}`, lies in the `(q,p)`-biregular tree band.

The two hypotheses are exactly `rowRadius_le` and `lastRow_le` transported to the concrete
matrix; the arithmetic content of the theorem is entirely in those two, and through them in
`sqrt_step`, i.e. in `0 ≤ α²`. -/
theorem laguerre_band {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℝ} {P Q : ℝ} (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hrows : ∀ k, |J k k - (P + Q - 2)| + ∑ j ∈ univ.erase k, |J k j|
        ≤ 2 * Real.sqrt ((P - 1) * (Q - 1)))
    {t : ℝ} (ht : Module.End.HasEigenvalue (Matrix.toLin' J) t) :
    (Real.sqrt (Q - 1) - Real.sqrt (P - 1)) ^ 2 ≤ t
      ∧ t ≤ (Real.sqrt (Q - 1) + Real.sqrt (P - 1)) ^ 2 := by
  have hband := eigenvalue_band hrows ht
  obtain ⟨hup, hlo⟩ := band_endpoints hP hQ
  rw [abs_le] at hband
  constructor
  · rw [hlo]; linarith [hband.1]
  · rw [hup]; linarith [hband.2]

end LaguerreBand
