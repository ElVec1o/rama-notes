import Mathlib

/-!
# The counting steps behind `child_count_drop`, formalized

`RatioRoute.min_children` and `child_count_drop` were stated as arithmetic, with their three
graph-theoretic inputs proved only in prose.  This file proves those inputs.

Setting: a bipartite graph with sides `L` and `R`, a self-avoiding path `π` ending at `w ∈ R`,
`k = |N(w) ∖ π|` its child count in the path tree, and `u ∈ N(w) ∖ π` a child, with `ku` its own
child count.  Write `pL = |π ∩ L|`, `pR = |π ∩ R|`.

* `blocked_le_left`: the blocked neighbours of `w` lie in `L`, so `|N(w) ∩ π| ≤ pL`.
* `alt_count`: `π` alternates between the sides, so on the side of its last vertex it has at
  least as many vertices as on the other; ending in `R` gives `pL ≤ pR`.
* `unblocked_le`: the neighbours of `u` lie in `R`, so an unblocked one avoids `π ∩ R` and
  `ku ≤ |R| - pR`.

The alternation count is the only one with content.  It is proved on `List Bool`, recording each
path vertex by the side it lies on: a list with no two adjacent entries equal has at least as
many entries equal to its head as different from it.  Reversing transfers this from the head to
the last vertex, which is the form the path argument needs.
-/

namespace PathCount

open Finset

/-! ## The alternation count -/

/-- A list alternates when no two adjacent entries agree.  A walk in a bipartite graph, recorded
by which side each vertex lies on, alternates in exactly this sense. -/
def Alt : List Bool → Prop
  | [] => True
  | [_] => True
  | x :: y :: t => x ≠ y ∧ Alt (y :: t)

/-- **An alternating list has at least as many entries agreeing with its head as differing.**
Proved by peeling two entries at a time: the second must differ from the first, so each pair
contributes one to each count and the tail again starts on the head's side. -/
theorem alt_count : ∀ (l : List Bool) (a : Bool), Alt l → l.head? = some a →
    l.count (!a) ≤ l.count a
  | [], _, _, h => by simp at h
  | [x], a, _, h => by
      have hx : x = a := by simpa using h
      subst hx; cases x <;> simp
  | x :: y :: t, a, hAlt, h => by
      have hx : x = a := by simpa using h
      subst hx
      obtain ⟨hxy, hrest⟩ := hAlt
      have hy : y = !x := by cases x <;> cases y <;> simp_all
      subst hy
      have key : t.count (!x) ≤ t.count x := by
        cases t with
        | nil => simp
        | cons c t' =>
            have hc : c = x := by
              have h1 : (!x) ≠ c := hrest.1
              cases x <;> cases c <;> simp_all
            have h2 := alt_count (c :: t') c hrest.2 (by simp)
            simpa [hc] using h2
      cases x <;> simp_all

/-- The form the path argument uses: an alternating path ending on one side has at least as many
vertices there as on the other.  Counts are unchanged by reversal, and reversal turns the last
entry into the head. -/
theorem alt_count_last (l : List Bool) (a : Bool) (hrev : Alt l.reverse)
    (hne : l ≠ []) (hlast : l.getLast hne = a) :
    l.count (!a) ≤ l.count a := by
  have hgl : l.getLast? = some a := by
    rw [← hlast]; exact List.getLast?_eq_some_getLast hne
  have hhead : l.reverse.head? = some a := by rw [List.head?_reverse, hgl]
  have := alt_count l.reverse a hrev hhead
  simpa using this

/-! ## The two set-counting steps -/

variable {V : Type*} [DecidableEq V]

/-- **Step 1.**  The blocked neighbours of `w` lie in `L`, so they are counted by `pL`. -/
theorem blocked_le_left {Nw L P : Finset V} (h : Nw ⊆ L) :
    (Nw ∩ P).card ≤ (L ∩ P).card :=
  card_le_card (inter_subset_inter_right h)

/-- **Step 3.**  The neighbours of `u` lie in `R`, so an unblocked one avoids `π ∩ R`, giving
`ku ≤ |R| - pR`. -/
theorem unblocked_le {Nu R P : Finset V} (h : Nu ⊆ R) :
    (Nu \ P).card ≤ R.card - (R ∩ P).card := by
  have hsub : Nu \ P ⊆ R \ P := sdiff_subset_sdiff h (le_refl P)
  have h1 : (Nu \ P).card ≤ (R \ P).card := card_le_card hsub
  have h2 : (R \ P).card + (R ∩ P).card = R.card := card_sdiff_add_card_inter R P
  omega

/-- **The three steps assembled.**  With `q = |N(w)|`, `k = |N(w) ∖ π|`, `pL`, `pR` as above and
`r = |R|`, the counting gives `q - k ≤ pL ≤ pR` and `ku ≤ r - pR`, hence
`ku ≤ r - q + k`: the child count drops by at least `q - r` at each level. -/
theorem child_drop {q k pL pR r ku : ℤ}
    (h1 : q - k ≤ pL) (h2 : pL ≤ pR) (h3 : ku ≤ r - pR) :
    ku ≤ k - (q - r) := by linarith

end PathCount
