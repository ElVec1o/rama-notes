import Mathlib

/-!
# A degree obstruction to point spectrum in the universal cover

Banks, Garza-Vargas and Mukherjee characterise the point spectrum of the universal cover `T_G`:
`θ` is an eigenvalue of `T_G` iff `G` has a **`θ`-Aomoto subset**, a set `S ⊆ V(G)` with `G[S]` a
forest, `θ` an eigenvalue of every component of `G[S]`, and `|∂S| < cc(G[S])`.

This file extracts a purely numerical consequence. Write `δ` and `Δ` for the minimum and maximum
degree of `G`, and suppose `S` is a `θ`-Aomoto subset with `θ ≠ 0`, `s = |S|`, `c = cc(G[S])`,
`b = |∂S|`, `e = e(S, ∂S)` the number of edges leaving `S`. Three combinatorial facts feed the
count, and each is a hypothesis below rather than something proved here:

* `h_hand`  : `δ * s + 2 * c ≤ e + 2 * s`.  This is the handshake identity
  `e = Σ_{v ∈ S} deg v - 2 * e(G[S])` together with `deg v ≥ δ` and, because `G[S]` is a forest
  with `c` components, `e(G[S]) = s - c`.
* `h_absorb`: `e ≤ Δ * b`.  Every edge leaving `S` lands on a boundary vertex, and a boundary
  vertex has at most `Δ` edges in total.
* `h_two`   : `2 * c ≤ s`.  For `θ ≠ 0` no component of the forest is a single vertex, since the
  one-vertex graph has only the eigenvalue `0`.

together with the Aomoto inequality itself, `h_aom : b < c`.

`degree_bound` is the conclusion: `2 * δ ≤ Δ + 1`, that is `Δ > 2 * (δ - 1)`.

## What it says

`no_eigenvalue_of_small_spread` is the contrapositive and is the form we use: if `Δ + 1 < 2 * δ`
then no such configuration exists, so `T_G` has **no nonzero eigenvalue at all**. In particular a
graph of minimum degree three and maximum degree four has a universal cover with empty nonzero
point spectrum. Taking `Δ = δ` recovers the classical fact that a regular tree has no eigenvalues.

For minimum degree three the bound reads `Δ ≥ 5`: a graph of minimum degree three whose universal
cover has a nonzero eigenvalue must carry a vertex of degree at least five.

## Status

`degree_bound` and `no_eigenvalue_of_small_spread` are `VERIFIED`. The Aomoto criterion itself is
the analytic input and is cited, not reproved, exactly as in `AomotoObstruction`.
-/

namespace DegreeBound

/-- **The counting bound.**  From the handshake identity, the fact that boundary vertices absorb at
most `Δ` edges each, the Aomoto inequality `b < c`, and `2 * c ≤ s`, the degree spread of `G` is
forced: `2 * δ ≤ Δ + 1`. -/
theorem degree_bound (δ Δ s c b e : ℕ)
    (hδ : 2 ≤ δ) (hc : 0 < c)
    (h_hand : δ * s + 2 * c ≤ e + 2 * s)
    (h_absorb : e ≤ Δ * b)
    (h_aom : b < c)
    (h_two : 2 * c ≤ s) :
    2 * δ ≤ Δ + 1 := by
  by_contra hcon
  push_neg at hcon
  have hΔ : Δ + 2 ≤ 2 * δ := by omega
  have hb : b + 1 ≤ c := h_aom
  -- move to `ℤ`, where the three product hints below are linear combinations of the hypotheses
  have hZ : ∀ m n : ℕ, m ≤ n → (m : ℤ) ≤ (n : ℤ) := fun _ _ h => Int.ofNat_le.mpr h
  have A : (δ : ℤ) * s + 2 * c ≤ (Δ : ℤ) * b + 2 * s := by
    have h1 := hZ _ _ h_hand
    have h2 := hZ _ _ h_absorb
    push_cast at h1 h2 ⊢
    linarith
  have hs : (2 : ℤ) * c ≤ s := by exact_mod_cast hZ _ _ h_two
  have hbc : (b : ℤ) + 1 ≤ c := by exact_mod_cast hZ _ _ hb
  have hd : (2 : ℤ) ≤ δ := by exact_mod_cast hZ _ _ hδ
  have hcpos : (1 : ℤ) ≤ c := by exact_mod_cast hZ _ _ hc
  have hDs : (Δ : ℤ) + 2 ≤ 2 * δ := by exact_mod_cast hZ _ _ hΔ
  have hDnn : (0 : ℤ) ≤ Δ := Int.natCast_nonneg Δ
  -- the three products that turn the hypotheses into a contradiction
  have p1 : (0 : ℤ) ≤ ((δ : ℤ) - 2) * ((s : ℤ) - 2 * c) :=
    mul_nonneg (by linarith) (by linarith)
  have p2 : (0 : ℤ) ≤ (Δ : ℤ) * (((c : ℤ) - 1) - b) := mul_nonneg hDnn (by linarith)
  have p3 : (0 : ℤ) ≤ (c : ℤ) * (2 * (δ : ℤ) - 2 - Δ) := mul_nonneg (by linarith) (by linarith)
  nlinarith [p1, p2, p3, hcpos, hd, mul_pos (by linarith : (0:ℤ) < (c:ℤ)) (by linarith : (0:ℤ) < (δ:ℤ) - 1)]

/-- **The contrapositive, and the form that is used.**  If the degree spread is small, no
configuration satisfying the Aomoto criterion at a nonzero `θ` can exist, so the universal cover has
no nonzero eigenvalue. With `δ = 3` this excludes every `Δ ≤ 4`. -/
theorem no_eigenvalue_of_small_spread (δ Δ s c b e : ℕ)
    (hδ : 2 ≤ δ) (hspread : Δ + 1 < 2 * δ) (hc : 0 < c)
    (h_hand : δ * s + 2 * c ≤ e + 2 * s)
    (h_absorb : e ≤ Δ * b)
    (h_two : 2 * c ≤ s) :
    ¬ b < c := fun h_aom =>
  absurd (degree_bound δ Δ s c b e hδ hc h_hand h_absorb h_aom h_two) (by omega)

/-- Minimum degree three, maximum degree four: no nonzero eigenvalue in the cover. -/
theorem mindeg_three_maxdeg_four (s c b e : ℕ) (hc : 0 < c)
    (h_hand : 3 * s + 2 * c ≤ e + 2 * s)
    (h_absorb : e ≤ 4 * b)
    (h_two : 2 * c ≤ s) :
    ¬ b < c :=
  no_eigenvalue_of_small_spread 3 4 s c b e (by norm_num) (by norm_num) hc h_hand h_absorb h_two

end DegreeBound
