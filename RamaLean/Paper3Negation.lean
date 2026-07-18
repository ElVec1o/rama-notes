import Mathlib
open Finset

/-!
# The negation identity: `c_v(I) = c_v(−I)` (engine of the anti-period law)

The reflection `w ↦ 2v − w` preserves both parity (for `v` odd... in fact for any `v`, since `2v` is
even) and `gcd(v,·)`; it maps the interval `(a, b]` onto `[2v−b, 2v−a)`. Hence the gcd-χ₄ window
counts of a window and its reflection agree — the fourth identity of the word theory (Paper 3 §7),
from which the anti-period law `2^{m/2} ≡ −1 (v) ⟹ word[i+m/2] = word[i] ⊕ t₃(v)` follows.

Machine-checked: `gcd_reflect` (the gcd invariance) and `count_reflect` (the window-count equality).
-/
namespace Paper3Negation

/-- Reflection preserves the gcd: `gcd(v, 2v−w) = gcd(v, w)` for `w ≤ 2v`. -/
lemma gcd_reflect {v w : ℕ} (hw : w ≤ 2 * v) : Nat.gcd v (2 * v - w) = Nat.gcd v w := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have h1 : Nat.gcd v (2 * v - w) ∣ 2 * v := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
    have h2 : Nat.gcd v (2 * v - w) ∣ 2 * v - w := Nat.gcd_dvd_right _ _
    have h4 := Nat.dvd_sub h1 h2
    have h5 : 2 * v - (2 * v - w) = w := by omega
    rwa [h5] at h4
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have h1 : Nat.gcd v w ∣ 2 * v := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
    exact Nat.dvd_sub h1 (Nat.gcd_dvd_right _ _)

/-- **The negation identity**: the gcd-χ₄ count of a window equals that of its reflection. -/
theorem count_reflect {v a b : ℕ} (hab : a ≤ b) (hb : b ≤ 2 * v) :
    ((Finset.Ioc a b).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = ((Finset.Ico (2 * v - b) (2 * v - a)).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  apply Finset.card_bij (fun w _ => 2 * v - w)
  · intro w hw
    rw [Finset.mem_filter, Finset.mem_Ioc] at hw
    obtain ⟨⟨haw, hwb⟩, hodd, hgcd⟩ := hw
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rw [gcd_reflect (by omega)]
    exact hgcd
  · intro w hw w' hw' h
    rw [Finset.mem_filter, Finset.mem_Ioc] at hw hw'
    omega
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_Ico] at hu
    obtain ⟨⟨hlu, hub⟩, hodd, hgcd⟩ := hu
    refine ⟨2 * v - u, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rw [gcd_reflect (by omega)]
    exact hgcd

/-- **The single-period parity (Theorem A, mod 2).** For odd `v`, the number of `w` in one period
`(0, 2v]` with `w` odd and `gcd(v,w) ≡ 3 (mod 4)` — i.e. `t₃(v)` — is odd iff `v ≡ 3 (mod 4)`.
Proof: the reflection `w ↦ 2v − w` is a gcd-preserving involution of the filter whose ONLY fixed
point is `w = v`; it contributes iff `gcd(v,v) = v ≡ 3 (mod 4)`, and all other `w` pair off, so the
count `≡ [v ≡ 3 (4)] (mod 2)`. This is the exact mod-2 value the deficit mechanism uses. -/
theorem t3_card_parity {v : ℕ} (hv : v % 2 = 1) :
    ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card % 2
      = (if v % 4 = 3 then 1 else 0) := by
  classical
  set S := (Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3) with hS
  have hvpos : 0 < v := by omega
  -- split S by (· < v)
  have e1 := Finset.card_filter_add_card_filter_not (s := S) (fun w => w < v)
  -- the ¬(·<v) part splits into (·=v) and (v<·)
  have e2 := Finset.card_filter_add_card_filter_not (s := S.filter (fun w => ¬ w < v)) (fun w => w = v)
  -- (S.filter ¬<v).filter (=v) = S.filter (=v)
  have hEq : (S.filter (fun w => ¬ w < v)).filter (fun w => w = v) = S.filter (fun w => w = v) := by
    ext w; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨hws, _⟩, hwv⟩; exact ⟨hws, hwv⟩
    · rintro ⟨hws, hwv⟩; exact ⟨⟨hws, by omega⟩, hwv⟩
  -- (S.filter ¬<v).filter (¬=v) = S.filter (v<·)
  have hGt : (S.filter (fun w => ¬ w < v)).filter (fun w => ¬ w = v) = S.filter (fun w => v < w) := by
    ext w; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨hws, hge⟩, hne⟩; exact ⟨hws, by omega⟩
    · rintro ⟨hws, hgt⟩; exact ⟨⟨hws, by omega⟩, by omega⟩
  -- bijection: S.filter(·<v) ≃ S.filter(v<·) via w ↦ 2v−w
  have hbij : (S.filter (fun w => w < v)).card = (S.filter (fun w => v < w)).card := by
    apply Finset.card_bij (fun w _ => 2 * v - w)
    · intro w hw
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc] at hw
      obtain ⟨⟨⟨_, hwb⟩, hodd, hgcd⟩, hlt⟩ := hw
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨⟨by omega, by omega⟩, by omega, ?_⟩, by omega⟩
      rw [gcd_reflect (by omega)]; exact hgcd
    · intro w hw w' hw' h
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc] at hw hw'
      omega
    · intro u hu
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc] at hu
      obtain ⟨⟨⟨hlu, hub⟩, hodd, hgcd⟩, hgt⟩ := hu
      refine ⟨2 * v - u, ?_, by omega⟩
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨⟨by omega, by omega⟩, by omega, ?_⟩, by omega⟩
      rw [gcd_reflect (by omega)]; exact hgcd
  -- the fixed-point card = [v ∈ S] = [v % 4 = 3]
  have hmem : (v ∈ S) ↔ (v % 4 = 3) := by
    rw [hS, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨_, _, hgcd⟩; rwa [Nat.gcd_self] at hgcd
    · intro h3; exact ⟨⟨by omega, by omega⟩, hv, by rw [Nat.gcd_self]; exact h3⟩
  have hFix : (S.filter (fun w => w = v)).card = (if v % 4 = 3 then 1 else 0) := by
    rw [Finset.filter_eq' S v]
    by_cases h3 : v % 4 = 3
    · rw [if_pos (hmem.mpr h3), Finset.card_singleton, if_pos h3]
    · rw [if_neg (fun hm => h3 (hmem.mp hm)), Finset.card_empty, if_neg h3]
  rw [hEq, hGt] at e2
  rw [hFix, ← hbij] at e2
  -- e1: card(<) + card(¬<) = card S ;  e2: [v%4=3] + card(<) = card(¬<)
  -- so card S = 2·card(<) + [v%4=3]
  by_cases h3 : v % 4 = 3
  · simp only [h3, if_true] at e2 ⊢; omega
  · simp only [h3, if_false] at e2 ⊢; omega
