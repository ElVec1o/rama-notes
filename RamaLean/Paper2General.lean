/-
# Paper 2 — Theorem 1, re-derived generally (all `n`, `r`)

This upgrades `thm1_verified` (which only checked `n, r ≤ 6` by computation) to a
**general theorem for every `n` and `r`**, re-deriving the paper's Steps 3–5
(cycle index → Chebyshev closed form) rather than citing them.

Everything is stated over an arbitrary commutative ring `R` with a distinguished
element `Y` (specialize `Y = Tₙ(x/2)` to recover the graph statement). We work
with the Chebyshev sequences evaluated at `Y`:

* `cT Y k` = `Tₖ(Y)`, `cU Y r` = `Uᵣ(Y)`   (Chebyshev, 1st/2nd kind),
* `cf Y k` = `2·Tₖ(Y) − 2`   (the per-cycle factor `f(k)`; with `Y = Tₙ(x/2)`,
  `cf Y k = 2·T_{nk}(x/2) − 2`, the characteristic polynomial of `C_{nk}`, by the
  Chebyshev composition identity `T_{nk} = Tₖ ∘ Tₙ`),
* `cG Y r` = the closed form `Uᵣ(Y) − 2Uᵣ₋₁(Y) + Uᵣ₋₂(Y)` (with `cG Y 0 = 1`).

We prove two things about `cG`, for all `r`:

1. `cG_ogf_rec` — it satisfies the OGF recurrence `Gᵣ = 2Y·Gᵣ₋₁ − Gᵣ₋₂`
   (`r ≥ 3`), i.e. `cG` are the coefficients of `(1−z)²/(1−2Yz+z²)`; and
   `cG_unique`, that this + initial data pins the sequence down.
2. `cG_newton` — it satisfies the **exponential-formula recurrence**
   `r·Gᵣ = Σ_{k=1}^r f(k)·Gᵣ₋ₖ`.

Consequently (`thm1_general`), **any** sequence `Φ` with `Φ 0 = 1` satisfying the
exponential-formula recurrence equals `cG`. The expected characteristic
polynomial of the random `r`-lift of `Cₙ` is such a `Φ` by the exponential
formula for `Sᵣ` — **which is itself formalized in
`RamaLean/Paper2ExpFormula.lean`** (`expFormula`, `permAvg_newton`), with the
combined statement as `thm1_Sr` there.

(The single remaining unformalized input of the graph statement is the
elementary spectral fact that the `r`-lift of a cycle is a disjoint union of
cycles `C_{n·ℓ}` with `char(C_m) = 2Tₘ(x/2) − 2`; Mathlib has no graph-lift
vocabulary.)

No `sorry`, no custom axioms.
-/
import Mathlib

namespace Paper2

variable {R : Type*} [CommRing R]

/-- `cT Y k = Tₖ(Y)`, Chebyshev polynomial of the first kind evaluated at `Y`. -/
def cT (Y : R) : ℕ → R
  | 0 => 1
  | 1 => Y
  | (k + 2) => 2 * Y * cT Y (k + 1) - cT Y k

/-- `cU Y r = Uᵣ(Y)`, Chebyshev polynomial of the second kind evaluated at `Y`. -/
def cU (Y : R) : ℕ → R
  | 0 => 1
  | 1 => 2 * Y
  | (k + 2) => 2 * Y * cU Y (k + 1) - cU Y k

/-- The per-cycle factor `f(k) = 2·Tₖ(Y) − 2`. -/
def cf (Y : R) (k : ℕ) : R := 2 * cT Y k - 2

/-- The closed form `Gᵣ = Uᵣ(Y) − 2Uᵣ₋₁(Y) + Uᵣ₋₂(Y)`, with `G₀ = 1` and
`U₋₁ = 0` (so `G₁ = U₁ − 2U₀`). -/
def cG (Y : R) : ℕ → R
  | 0 => 1
  | 1 => cU Y 1 - 2 * cU Y 0
  | (k + 2) => cU Y (k + 2) - 2 * cU Y (k + 1) + cU Y k

@[simp] lemma cT_add_two (Y : R) (k : ℕ) :
    cT Y (k + 2) = 2 * Y * cT Y (k + 1) - cT Y k := rfl

@[simp] lemma cU_add_two (Y : R) (k : ℕ) :
    cU Y (k + 2) = 2 * Y * cU Y (k + 1) - cU Y k := rfl

lemma cU_zero (Y : R) : cU Y 0 = 1 := rfl
lemma cU_one (Y : R) : cU Y 1 = 2 * Y := rfl

lemma cU_two (Y : R) : cU Y 2 = 4 * Y ^ 2 - 1 := by
  show 2 * Y * cU Y 1 - cU Y 0 = _; rw [cU_one, cU_zero]; ring

lemma cU_three (Y : R) : cU Y 3 = 8 * Y ^ 3 - 4 * Y := by
  show 2 * Y * cU Y 2 - cU Y 1 = _; rw [cU_two, cU_one]; ring

lemma cT_zero (Y : R) : cT Y 0 = 1 := rfl
lemma cT_one (Y : R) : cT Y 1 = Y := rfl

lemma cT_two (Y : R) : cT Y 2 = 2 * Y ^ 2 - 1 := by
  show 2 * Y * cT Y 1 - cT Y 0 = _; rw [cT_one, cT_zero]; ring

lemma cT_three (Y : R) : cT Y 3 = 4 * Y ^ 3 - 3 * Y := by
  show 2 * Y * cT Y 2 - cT Y 1 = _; rw [cT_two, cT_one]; ring

lemma cG_zero (Y : R) : cG Y 0 = 1 := rfl

lemma cG_one (Y : R) : cG Y 1 = 2 * Y - 2 := by
  show cU Y 1 - 2 * cU Y 0 = 2 * Y - 2
  rw [cU_one, cU_zero]; ring

lemma cG_two (Y : R) : cG Y 2 = 4 * Y ^ 2 - 4 * Y := by
  show cU Y 2 - 2 * cU Y 1 + cU Y 0 = 4 * Y ^ 2 - 4 * Y
  rw [cU_add_two, cU_one, cU_zero]; ring

/-! ## The OGF recurrence: `cG` are the coefficients of `(1−z)²/(1−2Yz+z²)` -/

/-- `cG` satisfies the second-order recurrence `Gₖ₊₃ = 2Y·Gₖ₊₂ − Gₖ₊₁`
(equivalently, its OGF is `(1−z)²/(1−2Yz+z²)`). -/
lemma cG_ogf_rec (Y : R) (k : ℕ) :
    cG Y (k + 3) = 2 * Y * cG Y (k + 2) - cG Y (k + 1) := by
  cases k with
  | zero =>
      show cU Y 3 - 2 * cU Y 2 + cU Y 1
          = 2 * Y * (cU Y 2 - 2 * cU Y 1 + cU Y 0) - (cU Y 1 - 2 * cU Y 0)
      rw [cU_three, cU_two, cU_one, cU_zero]; ring
  | succ n =>
      show cU Y (n + 4) - 2 * cU Y (n + 3) + cU Y (n + 2)
          = 2 * Y * (cU Y (n + 3) - 2 * cU Y (n + 2) + cU Y (n + 1))
            - (cU Y (n + 2) - 2 * cU Y (n + 1) + cU Y n)
      simp only [cU_add_two]; ring

/-- **Uniqueness / main OGF form.** Any sequence `Φ` matching `cG` on `{0,1,2}`
and satisfying the OGF recurrence `Φₖ₊₃ = 2Y·Φₖ₊₂ − Φₖ₊₁` equals `cG`
everywhere. (The expected characteristic polynomial is such a `Φ` — its OGF is
`(1−z)²/(1−2Yz+z²)`.) -/
theorem cG_unique (Y : R) (Φ : ℕ → R)
    (h0 : Φ 0 = cG Y 0) (h1 : Φ 1 = cG Y 1) (h2 : Φ 2 = cG Y 2)
    (hrec : ∀ k, Φ (k + 3) = 2 * Y * Φ (k + 2) - Φ (k + 1)) :
    ∀ r, Φ r = cG Y r := by
  have key : ∀ r, Φ r = cG Y r ∧ Φ (r + 1) = cG Y (r + 1) ∧ Φ (r + 2) = cG Y (r + 2) := by
    intro r
    induction r with
    | zero => exact ⟨h0, h1, h2⟩
    | succ n ih =>
        obtain ⟨e0, e1, e2⟩ := ih
        refine ⟨e1, e2, ?_⟩
        rw [hrec n, e2, e1, ← cG_ogf_rec Y n]
  exact fun r => (key r).1

/-! ## The exponential-formula (Newton) recurrence `r·Gᵣ = Σₖ f_k·Gᵣ₋ₖ`

This is the log-derivative of the exponential formula `Σ Gᵣ zʳ = exp(Σ f_ℓ zˡ/ℓ)`.
Proving it for the closed form `cG` re-derives the paper's Step 4 (the Chebyshev
generating-function computation), so that the *only* remaining classical input is
the exponential formula itself (Step 3). -/

/-- Bridge to the second-kind Chebyshev sequence: `Tₖ₊₁ = Uₖ₊₁ − Y·Uₖ`. -/
lemma cT_eq (Y : R) : ∀ k, cT Y (k + 1) = cU Y (k + 1) - Y * cU Y k := by
  have key : ∀ k, cT Y (k + 1) = cU Y (k + 1) - Y * cU Y k
                ∧ cT Y (k + 2) = cU Y (k + 2) - Y * cU Y (k + 1) := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [cU_one, cU_zero, cT_one]; ring
        · rw [cU_two, cU_one, cT_two]; ring
    | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨h2, ?_⟩
        have e : cT Y (n + 1 + 2) = 2 * Y * cT Y (n + 2) - cT Y (n + 1) := cT_add_two Y (n + 1)
        rw [e, h2, h1, cU_add_two Y (n + 1), cU_add_two Y n]
        ring
  exact fun k => (key k).1

lemma cf_unfold (Y : R) (k : ℕ) : cf Y k = 2 * cT Y k - 2 := rfl

lemma cf_one (Y : R) : cf Y 1 = 2 * Y - 2 := by rw [cf_unfold, cT_one]
lemma cf_two (Y : R) : cf Y 2 = 4 * Y ^ 2 - 4 := by rw [cf_unfold, cT_two]; ring
lemma cf_three (Y : R) : cf Y 3 = 8 * Y ^ 3 - 6 * Y - 2 := by rw [cf_unfold, cT_three]; ring

lemma cG_add_two' (Y : R) (k : ℕ) :
    cG Y (k + 2) = cU Y (k + 2) - 2 * cU Y (k + 1) + cU Y k := rfl

/-- **Crux Chebyshev identity** (`w_C = w_d`): the forcing terms of the two
inhomogeneous recurrences agree.
`f_{n+3} − 2f_{n+2} + f_{n+1} = 2Y·G_{n+2} − 2·G_{n+1}`. -/
lemma cf_crux (Y : R) (n : ℕ) :
    cf Y (n + 3) - 2 * cf Y (n + 2) + cf Y (n + 1)
      = 2 * Y * cG Y (n + 2) - 2 * cG Y (n + 1) := by
  rcases n with _ | m
  · show cf Y 3 - 2 * cf Y 2 + cf Y 1 = 2 * Y * cG Y 2 - 2 * cG Y 1
    rw [cf_three, cf_two, cf_one, cG_two, cG_one]; ring
  · simp only [cf_unfold, cT_eq, cG_add_two', cU_add_two]; ring

/-- `G₂ − 2Y·G₁ + G₀ = 1` (the `z²` coefficient of `(1−z)²`). -/
lemma cG_boundary (Y : R) : cG Y 2 - 2 * Y * cG Y 1 + cG Y 0 = 1 := by
  rw [cG_two, cG_one, cG_zero]; ring

/-- The convolution `Cᵣ = Σ_{k=1}^r f_k · Gᵣ₋ₖ`. -/
def cC (Y : R) (r : ℕ) : R := ∑ k ∈ Finset.Icc 1 r, cf Y k * cG Y (r - k)

open Finset in
/-- **Convolution second difference.** `Cₙ₊₃ − 2Y·Cₙ₊₂ + Cₙ₊₁ = f_{n+3} − 2f_{n+2} + f_{n+1}`.
The bulk of the aligned sum vanishes by `cG`'s homogeneous recurrence; only the
`k = n+1` term (value `1`) and the two peeled top terms survive. -/
lemma cC_seconddiff (Y : R) (n : ℕ) :
    cC Y (n + 3) - 2 * Y * cC Y (n + 2) + cC Y (n + 1)
      = cf Y (n + 3) - 2 * cf Y (n + 2) + cf Y (n + 1) := by
  have e3 : cC Y (n + 3)
      = (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 3 - k))
        + cf Y (n + 2) * cG Y 1 + cf Y (n + 3) * cG Y 0 := by
    unfold cC
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 2 + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ n + 1 + 1 by omega),
        show n + 3 - (n + 1 + 1) = 1 by omega, show n + 3 - (n + 2 + 1) = 0 by omega]
  have e2 : cC Y (n + 2)
      = (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 2 - k)) + cf Y (n + 2) * cG Y 0 := by
    unfold cC
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 + 1 by omega),
        show n + 2 - (n + 1 + 1) = 0 by omega]
  have e1 : cC Y (n + 1) = ∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 1 - k) := rfl
  -- the aligned sum over Icc 1 (n+1) reduces to the k = n+1 term
  have hsum : (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 3 - k))
      - 2 * Y * (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 2 - k))
      + (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 1 - k))
      = cf Y (n + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
    have hz : (∑ k ∈ Icc 1 n,
        (cf Y k * cG Y (n + 3 - k) - 2 * Y * (cf Y k * cG Y (n + 2 - k))
          + cf Y k * cG Y (n + 1 - k))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkn : k ≤ n := hk.2
      rw [show n + 3 - k = (n - k) + 3 by omega, show n + 2 - k = (n - k) + 2 by omega,
          show n + 1 - k = (n - k) + 1 by omega, cG_ogf_rec]
      ring
    rw [hz, show n + 3 - (n + 1) = 2 by omega, show n + 2 - (n + 1) = 1 by omega,
        show n + 1 - (n + 1) = 0 by omega]
    have : cf Y (n + 1) * cG Y 2 - 2 * Y * (cf Y (n + 1) * cG Y 1)
            + cf Y (n + 1) * cG Y 0 = cf Y (n + 1) * (cG Y 2 - 2 * Y * cG Y 1 + cG Y 0) := by ring
    rw [zero_add, this, cG_boundary, mul_one]
  rw [e3, e2, e1, cG_one, cG_zero]
  -- LHS now: (S3 + cf(n+2)cG1 + cf(n+3)) - 2Y(S2 + cf(n+2)) + S1
  -- rearrange to expose hsum, then finish
  have hrw : (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 3 - k)) + cf Y (n + 2) * (2 * Y - 2)
        + cf Y (n + 3) * 1
      - 2 * Y * ((∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 2 - k)) + cf Y (n + 2) * 1)
      + ∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 1 - k)
      = ((∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 3 - k))
          - 2 * Y * (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 2 - k))
          + (∑ k ∈ Icc 1 (n + 1), cf Y k * cG Y (n + 1 - k)))
        + (cf Y (n + 3) - 2 * cf Y (n + 2) + cf Y (n + 1)) - cf Y (n + 1) := by ring
  rw [hrw, hsum]; ring

/-- **The exponential-formula (Newton) recurrence for the closed form**, for all `r`:
`r · Gᵣ = Σ_{k=1}^r f_k · Gᵣ₋ₖ`.  Together with `G₀ = 1`, this pins `cG` down as
*the* cycle-index sum — so the expected characteristic polynomial (which satisfies
the same recurrence by the classical exponential formula) equals `cG` for every
`n` and `r`. -/
theorem cG_newton (Y : R) (r : ℕ) :
    (r : R) * cG Y r = ∑ k ∈ Finset.Icc 1 r, cf Y k * cG Y (r - k) := by
  suffices h : ∀ m, cC Y m = (m : R) * cG Y m from (h r).symm
  have hcC0 : cC Y 0 = ((0 : ℕ) : R) * cG Y 0 := by
    rw [cC, show Finset.Icc 1 0 = ∅ from Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    push_cast; ring
  have hcC1 : cC Y 1 = ((1 : ℕ) : R) * cG Y 1 := by
    rw [cC, Finset.Icc_self, Finset.sum_singleton, show (1 : ℕ) - 1 = 0 by omega,
        cf_one, cG_zero, cG_one]; push_cast; ring
  have hcC2 : cC Y 2 = ((2 : ℕ) : R) * cG Y 2 := by
    rw [cC, Finset.sum_Icc_succ_top (show 1 ≤ 1 + 1 by omega), Finset.Icc_self,
        Finset.sum_singleton, show (2 : ℕ) - 1 = 1 by omega, show (2 : ℕ) - (1 + 1) = 0 by omega,
        cf_one, cf_two, cG_zero, cG_one, cG_two]; push_cast; ring
  have key : ∀ m, cC Y m = ((m : ℕ) : R) * cG Y m
      ∧ cC Y (m + 1) = (((m + 1 : ℕ)) : R) * cG Y (m + 1)
      ∧ cC Y (m + 2) = (((m + 2 : ℕ)) : R) * cG Y (m + 2) := by
    intro m
    induction m with
    | zero => exact ⟨hcC0, hcC1, hcC2⟩
    | succ n ih =>
        obtain ⟨_, d1, d2⟩ := ih
        refine ⟨d1, d2, ?_⟩
        have hC := cC_seconddiff Y n
        have expand : cC Y (n + 3)
            = 2 * Y * cC Y (n + 2) - cC Y (n + 1)
              + (cf Y (n + 3) - 2 * cf Y (n + 2) + cf Y (n + 1)) := by
          linear_combination hC
        rw [show n + 1 + 2 = n + 3 by omega, expand, d2, d1, cf_crux Y n, cG_ogf_rec Y n]
        push_cast; ring
  exact fun m => (key m).1

/-! ## Uniqueness: the Newton recurrence + `Φ₀ = 1` determine the sequence

Over a characteristic-zero domain (e.g. `ℚ[x]`, where expected characteristic
polynomials live), `r·Φᵣ = Σ f_k Φᵣ₋ₖ` lets us cancel `r` and induct. -/

/-- **Theorem 1, abstract form.** Any sequence `Φ` with `Φ 0 = 1` satisfying the
exponential-formula recurrence `r·Φᵣ = Σ_{k=1}^r f_k·Φᵣ₋ₖ` equals the Chebyshev
closed form `cG` — for *every* `r`. -/
theorem thm1_of_newton [IsDomain R] [CharZero R]
    (Y : R) (Φ : ℕ → R) (h0 : Φ 0 = 1)
    (hexp : ∀ r : ℕ, 1 ≤ r →
      (r : R) * Φ r = ∑ k ∈ Finset.Icc 1 r, cf Y k * Φ (r - k)) :
    ∀ r, Φ r = cG Y r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | m
    · simpa [cG_zero] using h0
    · have hΦ := hexp (m + 1) (by omega)
      have hsum : ∑ k ∈ Finset.Icc 1 (m + 1), cf Y k * Φ (m + 1 - k)
          = ∑ k ∈ Finset.Icc 1 (m + 1), cf Y k * cG Y (m + 1 - k) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        rw [ih _ (by omega)]
      have hne : ((m + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      apply mul_left_cancel₀ hne
      rw [hΦ, hsum, cG_newton]

/-! ## Bridge to Mathlib's Chebyshev polynomials

`cT`/`cU` are evaluations of `Polynomial.Chebyshev.T`/`U`, so the theorems above
are about the same objects as the paper. -/

open Polynomial in
/-- `cT Y k = Tₖ(Y)` for Mathlib's Chebyshev `T`. -/
theorem cT_eq_chebyshev (Y : R) : ∀ k : ℕ, cT Y k = (Chebyshev.T R (k : ℤ)).eval Y := by
  have key : ∀ k : ℕ, cT Y k = (Chebyshev.T R (k : ℤ)).eval Y
      ∧ cT Y (k + 1) = (Chebyshev.T R ((k : ℤ) + 1)).eval Y := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · simp [cT_zero, Chebyshev.T_zero]
        · simp [cT_one, Chebyshev.T_one]
    | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        constructor
        · rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]; exact h2
        · rw [show ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 2 by push_cast; ring,
              Chebyshev.T_add_two, show n + 1 + 1 = n + 2 from rfl, cT_add_two, h1, h2]
          simp [eval_sub, eval_mul, eval_ofNat, eval_X]
  exact fun k => (key k).1

open Polynomial in
/-- `cU Y k = Uₖ(Y)` for Mathlib's Chebyshev `U`. -/
theorem cU_eq_chebyshev (Y : R) : ∀ k : ℕ, cU Y k = (Chebyshev.U R (k : ℤ)).eval Y := by
  have key : ∀ k : ℕ, cU Y k = (Chebyshev.U R (k : ℤ)).eval Y
      ∧ cU Y (k + 1) = (Chebyshev.U R ((k : ℤ) + 1)).eval Y := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · simp [cU_zero, Chebyshev.U_zero]
        · rw [cU_one, show ((0 : ℕ) : ℤ) + 1 = 1 from by norm_num, Chebyshev.U_one]
          simp
    | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        constructor
        · rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]; exact h2
        · rw [show ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 2 by push_cast; ring,
              Chebyshev.U_add_two, show n + 1 + 1 = n + 2 from rfl, cU_add_two, h1, h2]
          simp [eval_sub, eval_mul, eval_ofNat, eval_X]
  exact fun k => (key k).1

open Polynomial in
/-- **The paper's Step 2 composition identity.** The per-cycle factor at
`Y = Tₙ(t)` is the characteristic polynomial of the long cycle:
`f(k) = 2·Tₖ(Tₙ(t)) − 2 = 2·T_{nk}(t) − 2` (with `x = 2t`). Uses Mathlib's
`Chebyshev.T_mul` (`T_{mn} = T_m ∘ T_n`). -/
theorem cf_comp (t : R) (n k : ℕ) :
    cf ((Chebyshev.T R (n : ℤ)).eval t) k = 2 * (Chebyshev.T R ((n * k : ℕ) : ℤ)).eval t - 2 := by
  rw [cf_unfold, cT_eq_chebyshev]
  congr 2
  rw [show ((n * k : ℕ) : ℤ) = (k : ℤ) * (n : ℤ) by push_cast; ring,
      Chebyshev.T_mul, eval_comp]

open Polynomial in
/-- **Theorem 1, paper-faithful general form (all `n`, `r`).**
Let `Φ : ℕ → R` (over a char-0 domain, e.g. `ℚ[x]`) satisfy `Φ 0 = 1` and the
exponential-formula recurrence with per-cycle factors `2·T_{nk}(t) − 2` — the
characteristic polynomial of the cycle `C_{nk}` at `x = 2t`. Then `Φ r` is the
Chebyshev closed form: `Φ r = Uᵣ(Y) − 2Uᵣ₋₁(Y) + Uᵣ₋₂(Y)` at `Y = Tₙ(t)`.

By the classical exponential formula (Stanley, EC2 §5.1) applied to the
spectral decomposition of permutation lifts of `Cₙ` (paper's Steps 1–2), the
expected characteristic polynomial `Φ_{Cₙ,r}(x)` with `t = x/2` satisfies
exactly these hypotheses; this theorem supplies the paper's Steps 3–5 for every
`n` and `r`. -/
theorem thm1_general [IsDomain R] [CharZero R]
    (t : R) (n : ℕ) (Φ : ℕ → R) (h0 : Φ 0 = 1)
    (hexp : ∀ r : ℕ, 1 ≤ r →
      (r : R) * Φ r
        = ∑ k ∈ Finset.Icc 1 r,
            (2 * (Chebyshev.T R ((n * k : ℕ) : ℤ)).eval t - 2) * Φ (r - k)) :
    ∀ r, Φ r = cG ((Chebyshev.T R (n : ℤ)).eval t) r := by
  apply thm1_of_newton _ _ h0
  intro r hr
  rw [hexp r hr]
  exact Finset.sum_congr rfl fun k _ => by rw [cf_comp]

open Polynomial in
/-- The closed form unfolded to Mathlib Chebyshev `U`, `r ≥ 2` case:
`Φ (k+2) = U_{k+2}(Y) − 2·U_{k+1}(Y) + U_k(Y)` with `Y = Tₙ(t)`. (For `r = 1`:
`cG Y 1 = U₁(Y) − 2·U₀(Y)`, i.e. `U₋₁ = 0`, matching the paper's convention.) -/
theorem thm1_closed_form [IsDomain R] [CharZero R]
    (t : R) (n : ℕ) (Φ : ℕ → R) (h0 : Φ 0 = 1)
    (hexp : ∀ r : ℕ, 1 ≤ r →
      (r : R) * Φ r
        = ∑ k ∈ Finset.Icc 1 r,
            (2 * (Chebyshev.T R ((n * k : ℕ) : ℤ)).eval t - 2) * Φ (r - k)) (k : ℕ) :
    Φ (k + 2)
      = (Chebyshev.U R ((k : ℤ) + 2)).eval ((Chebyshev.T R (n : ℤ)).eval t)
        - 2 * (Chebyshev.U R ((k : ℤ) + 1)).eval ((Chebyshev.T R (n : ℤ)).eval t)
        + (Chebyshev.U R (k : ℤ)).eval ((Chebyshev.T R (n : ℤ)).eval t) := by
  set Y := (Chebyshev.T R (n : ℤ)).eval t
  rw [thm1_general t n Φ h0 hexp (k + 2), cG_add_two',
      cU_eq_chebyshev, cU_eq_chebyshev, cU_eq_chebyshev,
      show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]

/-! ## The factored form: `Φ_{Cₙ,r} = χ_{Cₙ} · U_{r−1}(Tₙ(x/2))`

By the recurrence `Uᵣ + Uᵣ₋₂ = 2Y·Uᵣ₋₁`, the closed form collapses to a
product: `cG Y r = (2Y − 2)·Uᵣ₋₁(Y)` for `r ≥ 1`. Since `2Y − 2 = 2Tₙ(x/2) − 2`
is the characteristic polynomial of the base cycle `Cₙ` itself, the expected
characteristic polynomial factors as (base char poly) × (quotient), with the
quotient **explicitly** `Ψᵣ = U_{r−1}(Tₙ(x/2))`.

At `r = 2` the quotient is `U₁(Tₙ(x/2)) = 2Tₙ(x/2)` — the *matching polynomial*
of `Cₙ`, as required by the classical Godsil–Gutman theorem for 2-lifts. -/

/-- **Factorization.** `cG Y (k+1) = (2Y − 2) · cU Y k`; i.e.
`Φ_{Cₙ,r} = χ_{Cₙ} · U_{r−1}(Y)` for all `r ≥ 1`. -/
theorem cG_factored (Y : R) (k : ℕ) : cG Y (k + 1) = (2 * Y - 2) * cU Y k := by
  cases k with
  | zero => rw [cG_one, cU_zero]; ring
  | succ m =>
      rw [cG_add_two', cU_add_two]
      ring

/-- **Theorem 1, factored form.** Under the hypotheses of `thm1_general`,
`Φ (k+1) = (2·Tₙ(t) − 2) · Uₖ(Tₙ(t))` — the base characteristic polynomial
(at `x = 2t`) times the explicit quotient `U_{r−1}(Tₙ(x/2))`. -/
theorem thm1_factored [IsDomain R] [CharZero R]
    (t : R) (n : ℕ) (Φ : ℕ → R) (h0 : Φ 0 = 1)
    (hexp : ∀ r : ℕ, 1 ≤ r →
      (r : R) * Φ r
        = ∑ k ∈ Finset.Icc 1 r,
            (2 * (Polynomial.Chebyshev.T R ((n * k : ℕ) : ℤ)).eval t - 2) * Φ (r - k)) (k : ℕ) :
    Φ (k + 1)
      = (2 * (Polynomial.Chebyshev.T R (n : ℤ)).eval t - 2)
        * (Polynomial.Chebyshev.U R (k : ℤ)).eval ((Polynomial.Chebyshev.T R (n : ℤ)).eval t) := by
  rw [thm1_general t n Φ h0 hexp (k + 1), cG_factored, cU_eq_chebyshev]

/-! ## Parity of the quotient

`Tₖ` and `Uₖ` have the parity of their index: `Tₖ(−Y) = (−1)ᵏTₖ(Y)`,
`Uₖ(−Y) = (−1)ᵏUₖ(Y)`. Hence the quotient `Ψᵣ(x) = U_{r−1}(Tₙ(x/2))` (degree
`n(r−1)`) satisfies `Ψᵣ(−x) = (−1)^{n(r−1)}·Ψᵣ(x)` — it is supported on
exponents of a single parity, like a matching polynomial. For bipartite `Cₙ`
(`n` even) it is an even polynomial for every `r`; for odd `n` it alternates
with `r`. This is the cycle-graph case of the parity phenomenon observed for
`K₄` in `paper4`. -/

/-- `Tₖ(−Y) = (−1)ᵏ·Tₖ(Y)`. -/
theorem cT_neg (Y : R) : ∀ k, cT (-Y) k = (-1) ^ k * cT Y k := by
  have key : ∀ k, cT (-Y) k = (-1) ^ k * cT Y k
      ∧ cT (-Y) (k + 1) = (-1) ^ (k + 1) * cT Y (k + 1) := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [cT_zero, cT_zero]; ring
        · rw [cT_one, cT_one]; ring
    | succ m ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨h2, ?_⟩
        rw [show m + 1 + 1 = m + 2 from rfl, cT_add_two, cT_add_two, h1, h2]
        rw [pow_succ, pow_succ]
        ring
  exact fun k => (key k).1

/-- `Uₖ(−Y) = (−1)ᵏ·Uₖ(Y)`. -/
theorem cU_neg (Y : R) : ∀ k, cU (-Y) k = (-1) ^ k * cU Y k := by
  have key : ∀ k, cU (-Y) k = (-1) ^ k * cU Y k
      ∧ cU (-Y) (k + 1) = (-1) ^ (k + 1) * cU Y (k + 1) := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [cU_zero, cU_zero]; ring
        · rw [cU_one, cU_one]; ring
    | succ m ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨h2, ?_⟩
        rw [show m + 1 + 1 = m + 2 from rfl, cU_add_two, cU_add_two, h1, h2]
        rw [pow_succ, pow_succ]
        ring
  exact fun k => (key k).1

/-- **Quotient parity theorem (cycle graphs).** The lift quotient
`Ψ(t) = Uₖ(Tₙ(t))` satisfies `Ψ(−t) = (−1)^{nk}·Ψ(t)`: it is supported on
exponents of a single parity (that of its degree `nk`). In particular for `n`
even (bipartite `Cₙ`) the quotient is an even polynomial for every lift degree,
and for `n` odd it has the parity of `k = r − 1`. -/
theorem quotient_parity (t : R) (n k : ℕ) :
    cU (cT (-t) n) k = (-1) ^ (n * k) * cU (cT t n) k := by
  rw [cT_neg]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul,
        (he.mul_right k).neg_one_pow, one_mul]
  · rw [ho.neg_one_pow, pow_mul, ho.neg_one_pow, neg_one_mul, cU_neg]

end Paper2
