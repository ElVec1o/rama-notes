import Mathlib
import RamaLean.Paper3CMinus1
open Finset BigOperators

/-!
# The transposition involution: `κ(a,a) ≡ [a = 2] (mod 2)`

The first identity *outside* the swap calculus of Paper 3 §7. Let
`κ(a,a) = #{(v,w) : v,w odd < 2^a, gcd(v,w) ≡ 3 (mod 4)}`. The transposition `(v,w) ↦ (w,v)` is an
involution of this set whose fixed points are the diagonal; off-diagonal pairs cancel mod 2, and the
diagonal is `#{v < 2^a : v ≡ 3 (4)} = 2^(a−2)` (`card_three_mod_four`). Hence
`κ(a,a) ≡ 2^(a−2) ≡ [a=2] (mod 2)` — machine-checked here as `kappa_diag`.

This evaluates the equal-scale stratum of the digit-pair correlation
`Corr(k) ≡ #{(v,w) : v ≤ 2^(k−1), w ≤ 2^k, oddpart(gcd) ≡ 3 (4)}` (the product-swap identity);
the surviving core is the adjacent-scale strips `κ(a,a+1)`.
-/
namespace Paper3Involution

/-- The square gcd-χ₄ pair set at scale `2^a`. -/
def S (a : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (2 ^ a)).filter (fun v => v % 2 = 1)) ×ˢ
   ((Finset.range (2 ^ a)).filter (fun w => w % 2 = 1))).filter
    (fun p => Nat.gcd p.1 p.2 % 4 = 3)

/-- **The involution theorem**: `κ(a,a) ≡ [a=2] (mod 2)` for `a ≥ 2`. -/
theorem kappa_diag {a : ℕ} (ha : 2 ≤ a) :
    (S a).card % 2 = if a = 2 then 1 else 0 := by
  classical
  -- split into diagonal and off-diagonal parts
  have hsplit : ((S a).filter (fun p => p.1 = p.2)).card
      + ((S a).filter (fun p => ¬ p.1 = p.2)).card = (S a).card :=
    Finset.card_filter_add_card_filter_not (s := S a) (fun p => p.1 = p.2)
  -- off-diagonal part: the two strict halves are swapped bijectively ⟹ even
  have hoff : ((S a).filter (fun p => ¬ p.1 = p.2)).card % 2 = 0 := by
    have hLG : ((S a).filter (fun p => ¬ p.1 = p.2)).card
        = ((S a).filter (fun p => p.1 < p.2)).card
          + ((S a).filter (fun p => p.2 < p.1)).card := by
      rw [← Finset.card_filter_add_card_filter_not
            (s := (S a).filter (fun p => ¬ p.1 = p.2)) (fun p => p.1 < p.2)]
      congr 1
      · congr 1
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hs, _⟩, hlt⟩; exact ⟨hs, hlt⟩
        · rintro ⟨hs, hlt⟩; exact ⟨⟨hs, by omega⟩, hlt⟩
      · congr 1
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hs, hne⟩, hnlt⟩; exact ⟨hs, by omega⟩
        · rintro ⟨hs, hlt⟩; exact ⟨⟨hs, by omega⟩, by omega⟩
    have hswap : ((S a).filter (fun p => p.1 < p.2)).card
        = ((S a).filter (fun p => p.2 < p.1)).card := by
      apply Finset.card_bij (fun p _ => (p.2, p.1))
      · intro p hp
        rw [Finset.mem_filter] at hp ⊢
        obtain ⟨hpS, hlt⟩ := hp
        unfold S at hpS ⊢
        rw [Finset.mem_filter, Finset.mem_product] at hpS ⊢
        exact ⟨⟨⟨hpS.1.2, hpS.1.1⟩, by rw [Nat.gcd_comm]; exact hpS.2⟩, hlt⟩
      · intro p hp q hq h
        have h1 : p.2 = q.2 := congrArg Prod.fst h
        have h2 : p.1 = q.1 := congrArg Prod.snd h
        exact Prod.ext h2 h1
      · intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqS, hlt⟩ := hq
        unfold S at hqS
        rw [Finset.mem_filter, Finset.mem_product] at hqS
        refine ⟨(q.2, q.1), ?_, rfl⟩
        rw [Finset.mem_filter]
        constructor
        · unfold S
          rw [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hqS.1.2, hqS.1.1⟩, by rw [Nat.gcd_comm]; exact hqS.2⟩
        · exact hlt
    omega
  -- diagonal part: image of the AP set `v ≡ 3 (mod 4)` under `v ↦ (v,v)`
  have hdiag : ((S a).filter (fun p => p.1 = p.2)).card = 2 ^ (a - 2) := by
    have himg : (S a).filter (fun p => p.1 = p.2)
        = ((Finset.range (2 ^ a)).filter (fun v => v % 4 = 3)).image (fun v => (v, v)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hpS, heq⟩
        unfold S at hpS
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpS
        obtain ⟨⟨⟨hv, _⟩, _⟩, hgcd⟩ := hpS
        refine ⟨p.1, ⟨hv, ?_⟩, ?_⟩
        · rw [← heq] at hgcd
          rwa [Nat.gcd_self] at hgcd
        · exact Prod.ext rfl heq
      · rintro ⟨v, ⟨hv, hmod⟩, rfl⟩
        constructor
        · unfold S
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          have hodd : v % 2 = 1 := by omega
          exact ⟨⟨⟨hv, hodd⟩, ⟨hv, hodd⟩⟩, by simpa [Nat.gcd_self] using hmod⟩
        · rfl
    rw [himg, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h),
        Paper3CMinus1.card_three_mod_four ha]
  -- combine
  rcases eq_or_lt_of_le ha with h2 | h3
  · -- a = 2
    subst h2
    rw [if_pos rfl]
    norm_num at hdiag
    omega
  · -- a ≥ 3
    have hne : a ≠ 2 := by omega
    rw [if_neg hne]
    have heven : 2 ^ (a - 2) = 2 * 2 ^ (a - 3) := by
      have h1 : a - 2 = (a - 3) + 1 := by omega
      rw [h1, pow_succ]; ring
    omega

end Paper3Involution
