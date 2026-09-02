import Mathlib

/-!
# A degree bound that sharpens as the eigenvalue approaches zero

`RamaLean/DegreeBound.lean` proves `2 * δ ≤ Δ + 1` from the fact that a `θ`-Aomoto subset with
`θ ≠ 0` has no singleton component, i.e. from `2 * c ≤ s`. That input is crude. By Lemma 4.2 of
Banks, Garza-Vargas and Mukherjee an Aomoto tree carries a nowhere-vanishing `θ`-eigenvector, and
such a tree cannot be small when `θ` is small: `K₂` carries only `θ = ±1`, `P₃` only `θ = ±√2`, so
`0 < |θ| < 1` already needs four vertices. Writing `κ` for the least order of a tree with a
nowhere-vanishing `θ`-eigenvector, every component has at least `κ` vertices, so `κ * c ≤ s`.

This file replaces `2 * c ≤ s` by `κ * c ≤ s` throughout the same counting chain and concludes
`(δ - 2) * κ + 2 < Δ`, written without truncated subtraction as `δ * κ + 2 < Δ + 2 * κ`.
Taking `κ = 2` recovers `2 * δ ≤ Δ + 1`.

As in `RamaLean/DegreeBound.lean` the criterion of [BGM] is the analytic input and is cited rather
than reproved, and the combinatorial facts enter as hypotheses:
`h_hand` is the handshake count `(δ - 2) * s + 2 * c ≤ e`, `h_absorb` is `e ≤ Δ * b`, `h_aom` is
the Aomoto inequality `b < c`, and `h_kappa` is the component-order bound `κ * c ≤ s`.
-/

/-- The counting chain with a general lower bound `κ` on the order of each component. -/
theorem degree_bound_kappa (δ Δ s c b e κ : ℕ)
    (hδ : 2 ≤ δ) (hc : 0 < c)
    (h_hand : δ * s + 2 * c ≤ e + 2 * s)
    (h_absorb : e ≤ Δ * b)
    (h_aom : b < c)
    (h_kappa : κ * c ≤ s) :
    δ * κ + 2 < Δ + 2 * κ := by
  have hZ : ∀ m n : ℕ, m ≤ n → (m : ℤ) ≤ (n : ℤ) := fun _ _ h => Int.ofNat_le.mpr h
  have A : (δ : ℤ) * s + 2 * c ≤ (Δ : ℤ) * b + 2 * s := by
    have h1 := hZ _ _ h_hand
    have h2 := hZ _ _ h_absorb
    push_cast at h1 h2 ⊢
    linarith
  have hs : (κ : ℤ) * c ≤ s := by exact_mod_cast hZ _ _ h_kappa
  have hbc : (b : ℤ) + 1 ≤ c := by exact_mod_cast hZ _ _ h_aom
  have hd : (2 : ℤ) ≤ δ := by exact_mod_cast hZ _ _ hδ
  have hcpos : (1 : ℤ) ≤ c := by exact_mod_cast hZ _ _ hc
  have hDnn : (0 : ℤ) ≤ Δ := Int.natCast_nonneg Δ
  have hknn : (0 : ℤ) ≤ κ := Int.natCast_nonneg κ
  -- (δ - 2) * (s - κ * c) ≥ 0 pushes the handshake count down to the component bound
  have p1 : (0 : ℤ) ≤ ((δ : ℤ) - 2) * ((s : ℤ) - (κ : ℤ) * c) :=
    mul_nonneg (by linarith) (by linarith)
  -- Δ * ((c - 1) - b) ≥ 0 absorbs the boundary
  have p2 : (0 : ℤ) ≤ (Δ : ℤ) * (((c : ℤ) - 1) - b) := mul_nonneg hDnn (by linarith)
  have key : (c : ℤ) * (((δ : ℤ) - 2) * κ + 2) ≤ (Δ : ℤ) * ((c : ℤ) - 1) := by nlinarith [p1, p2]
  have hstrict : ((δ : ℤ) - 2) * κ + 2 < (Δ : ℤ) := by nlinarith [key, hcpos, hknn, hd]
  have : (δ : ℤ) * κ + 2 < (Δ : ℤ) + 2 * κ := by linarith [hstrict]
  exact_mod_cast this

/-- `κ = 2` is the case proved in `RamaLean/DegreeBound.lean`: no singleton components. -/
theorem degree_bound_of_kappa_two (δ Δ s c b e : ℕ)
    (hδ : 2 ≤ δ) (hc : 0 < c)
    (h_hand : δ * s + 2 * c ≤ e + 2 * s)
    (h_absorb : e ≤ Δ * b)
    (h_aom : b < c)
    (h_two : 2 * c ≤ s) :
    2 * δ ≤ Δ + 1 := by
  have := degree_bound_kappa δ Δ s c b e 2 hδ hc h_hand h_absorb h_aom h_two
  omega

/-- Contrapositive in the form used: if the degree spread is too small for `κ`, there is no
`θ`-Aomoto subset, hence `θ` is not an eigenvalue of the universal cover. -/
theorem no_eigenvalue_of_spread_lt_kappa (δ Δ s c b e κ : ℕ)
    (hδ : 2 ≤ δ) (hc : 0 < c)
    (h_hand : δ * s + 2 * c ≤ e + 2 * s)
    (h_absorb : e ≤ Δ * b)
    (h_kappa : κ * c ≤ s)
    (hspread : Δ + 2 * κ ≤ δ * κ + 2) :
    ¬ b < c := by
  intro h
  have := degree_bound_kappa δ Δ s c b e κ hδ hc h_hand h_absorb h h_kappa
  omega
