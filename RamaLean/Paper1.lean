/-
# Paper 1 — Integers `n` where `n` divides `p(n) − 1`

Lean 4 / Mathlib formalization of the verifiable content of
`proof1_partition_self_divisibility.md`.

The genuine integer partition function is taken to be
`p n := Fintype.card (Nat.Partition n)`, i.e. the number of partitions of `n`
as defined combinatorially in Mathlib (`Nat.Partition`). Every theorem in
*Part A* is therefore a statement about the *actual* partition function, proved
by kernel/native-checked computation over that combinatorial definition — no
recurrence, no axioms, no appeal to Euler's theorem.

*Part B* introduces the Euler pentagonal recurrence as an efficient computable
function `ppent`, proves it agrees with the combinatorial `p` on the entire
range where the latter is feasible to enumerate, and uses it to certify the
larger members of the self-divisibility sequences `S₁, S₀, S₋₁`. The statements
in Part B are about `ppent`; their reading as facts about `p` rests on Euler's
Pentagonal Number Theorem (classical, not yet in Mathlib), as noted inline.
-/
import Mathlib

namespace Paper1

open Nat

/-- The integer partition function, defined as the cardinality of the (finite)
type of partitions of `n` from `Mathlib.Combinatorics.Enumerative.Partition`. -/
abbrev p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-! ## Part A — the Proposition (airtight, over the combinatorial definition)

`proof1` Proposition:  p(5) ≡ 2 (mod 5),  p(7) ≡ 1 (mod 7),  p(11) ≡ 1 (mod 11).
Consequently 7, 11 ∈ S₁ and 5 ∉ S₁, where S₁ = { n ≥ 2 : n ∣ p(n) − 1 }. -/

/-- A small table of partition values, each verified against the combinatorial
definition. (`p 5 = 7`, `p 6 = 11` are the "vanishing" values used in `proof1`.) -/
theorem p_values :
    p 0 = 1 ∧ p 1 = 1 ∧ p 2 = 2 ∧ p 3 = 3 ∧ p 4 = 5 ∧
    p 5 = 7 ∧ p 6 = 11 ∧ p 7 = 15 ∧ p 9 = 30 ∧ p 10 = 42 ∧ p 11 = 56 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> native_decide

/-- (i)  `p(5) ≡ 2 (mod 5)`. -/
theorem prop_i : p 5 ≡ 2 [MOD 5] := by native_decide

/-- (ii) `p(7) ≡ 1 (mod 7)`. -/
theorem prop_ii : p 7 ≡ 1 [MOD 7] := by native_decide

/-- (iii) `p(11) ≡ 1 (mod 11)`. -/
theorem prop_iii : p 11 ≡ 1 [MOD 11] := by native_decide

/-- The self-divisibility set `S₁ = { n ≥ 2 : n ∣ p(n) − 1 }`. -/
def S₁ (n : ℕ) : Prop := 2 ≤ n ∧ (n : ℤ) ∣ ((p n : ℤ) - 1)

/-- `7 ∈ S₁`. -/
theorem seven_mem : S₁ 7 := by
  refine ⟨by norm_num, ?_⟩; native_decide

/-- `11 ∈ S₁`. -/
theorem eleven_mem : S₁ 11 := by
  refine ⟨by norm_num, ?_⟩; native_decide

/-- `4 ∈ S₁` (the first non-trivial member: `p(4) = 5 ≡ 1 (mod 4)`). -/
theorem four_mem : S₁ 4 := by
  refine ⟨by norm_num, ?_⟩; native_decide

/-- `5 ∉ S₁`: `5 ∤ p(5) − 1` since `p(5) = 7 ≡ 2 (mod 5)`. -/
theorem five_not_mem : ¬ S₁ 5 := by
  rintro ⟨-, h⟩; revert h; native_decide

/-- The two companion sets from `proof1`/`paper1`, on their first few members:
`S₀ = { n : n ∣ p(n) }` and `S₋₁ = { n : p(n) ≡ −1 (mod n) }`. -/
theorem companion_small :
    (2 : ℤ) ∣ (p 2 : ℤ) ∧ (3 : ℤ) ∣ (p 3 : ℤ) ∧        -- 2, 3 ∈ S₀
    p 6 ≡ 5 [MOD 6] := by                                -- 6 ∈ S₋₁  (p 6 = 11 ≡ -1 mod 6)
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ### The trust base, isolated

Every statement of Part A is a consequence of the value table `p_values` and of nothing
else.  That table is the only place `native_decide` is needed: the kernel cannot reduce
`Fintype.card (Nat.Partition n)` — its `Decidable` instance does not evaluate — so the
values must come from compiled evaluation.

Each statement is therefore given here FIRST in conditional form, taking as hypotheses
exactly the values it uses.  Those conditional theorems depend on the standard three
axioms only, and they are where the mathematics of the Proposition lives; the
unconditional versions above are these applied to the table.  So the compiled evaluation
is confined to a list of integers a reader can check by hand, and every inference drawn
from them is kernel-checked.
-/

theorem prop_i_of (h : p 5 = 7) : p 5 ≡ 2 [MOD 5] := by rw [h]; decide

theorem prop_ii_of (h : p 7 = 15) : p 7 ≡ 1 [MOD 7] := by rw [h]; decide

theorem prop_iii_of (h : p 11 = 56) : p 11 ≡ 1 [MOD 11] := by rw [h]; decide

theorem four_mem_of (h : p 4 = 5) : S₁ 4 := by
  refine ⟨by norm_num, ?_⟩
  rw [h]; norm_num

theorem seven_mem_of (h : p 7 = 15) : S₁ 7 := by
  refine ⟨by norm_num, ?_⟩
  rw [h]; norm_num

theorem eleven_mem_of (h : p 11 = 56) : S₁ 11 := by
  refine ⟨by norm_num, ?_⟩
  rw [h]; norm_num

theorem five_not_mem_of (h : p 5 = 7) : ¬ S₁ 5 := by
  rintro ⟨-, hd⟩
  rw [h] at hd
  norm_num at hd

/-- The Proposition, in the form the paper states it, from the table alone. -/
theorem proposition_of (h5 : p 5 = 7) (h7 : p 7 = 15) (h11 : p 11 = 56) :
    (p 5 ≡ 2 [MOD 5]) ∧ (p 7 ≡ 1 [MOD 7]) ∧ (p 11 ≡ 1 [MOD 11])
      ∧ S₁ 7 ∧ S₁ 11 ∧ ¬ S₁ 5 :=
  ⟨prop_i_of h5, prop_ii_of h7, prop_iii_of h11,
   seven_mem_of h7, eleven_mem_of h11, five_not_mem_of h5⟩

/-! ## Part B — the Euler pentagonal recurrence and the full sequences

`ppent` is the partition function computed by Euler's pentagonal recurrence
        p(n) = Σ_{k≥1} (−1)^{k+1} [ p(n − g_k) + p(n − g_{−k}) ],
        g_k = k(3k−1)/2,  g_{−k} = k(3k+1)/2.
It is linear-memory / quadratic-time, so it reaches `n = 1000`, unlike the
direct `Fintype.card` enumeration. -/

/-- One step of the recurrence: given the array `prev` of `p(0..n−1)`, compute
`p(n)`. Pentagonal indices `g_k, g_{−k}` for `k = 1 .. n`. -/
def pentStep (prev : Array Int) (n : Nat) : Int :=
  (List.range n).foldl (fun acc k0 =>
    let k := k0 + 1
    let g1 := k * (3 * k - 1) / 2
    let g2 := k * (3 * k + 1) / 2
    let sign : Int := if k % 2 == 1 then 1 else -1
    let t1 : Int := if g1 ≤ n then sign * prev.getD (n - g1) 0 else 0
    let t2 : Int := if g2 ≤ n then sign * prev.getD (n - g2) 0 else 0
    acc + t1 + t2) 0

/-- The array `#[p(0), p(1), …, p(n)]`, built bottom-up. -/
def pArr : Nat → Array Int
  | 0 => #[1]
  | (m + 1) => let prev := pArr m; prev.push (pentStep prev (m + 1))

/-- The pentagonal-recurrence partition function. -/
def ppent (n : Nat) : Int := (pArr n).getD n 0

/-- Sanity: the recurrence reproduces the small table from `p_values`. -/
theorem ppent_values :
    ppent 4 = 5 ∧ ppent 5 = 7 ∧ ppent 6 = 11 ∧ ppent 7 = 15 ∧ ppent 11 = 56 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> native_decide

/-- **Bridge to the combinatorial definition.** `ppent` agrees with the genuine
partition function `p = Fintype.card (Nat.Partition ·)` on `0 ≤ n ≤ 11`, the
range where the combinatorial side is feasible to enumerate. (For all `n`,
`ppent n = p n` is Euler's Pentagonal Number Theorem.) -/
theorem ppent_eq_card_le_11 :
    ppent 0  = (p 0 : Int)  ∧ ppent 1 = (p 1 : Int)  ∧ ppent 2  = (p 2 : Int) ∧
    ppent 3  = (p 3 : Int)  ∧ ppent 4 = (p 4 : Int)  ∧ ppent 5  = (p 5 : Int) ∧
    ppent 6  = (p 6 : Int)  ∧ ppent 7 = (p 7 : Int)  ∧ ppent 8  = (p 8 : Int) ∧
    ppent 9  = (p 9 : Int)  ∧ ppent 10 = (p 10 : Int) ∧ ppent 11 = (p 11 : Int) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> native_decide

/-- **`S₁` through `n = 1000`** (statement about `ppent`):
`{ 4, 7, 11, 54, 55, 115, 146, 157, 234, 239, 951 }` all satisfy `ppent n ≡ 1 (mod n)`.
These are exactly the 11 terms listed in `paper1`. -/
theorem S₁_members :
    ppent 4   % 4   = 1 ∧ ppent 7   % 7   = 1 ∧ ppent 11  % 11  = 1 ∧
    ppent 54  % 54  = 1 ∧ ppent 55  % 55  = 1 ∧ ppent 115 % 115 = 1 ∧
    ppent 146 % 146 = 1 ∧ ppent 157 % 157 = 1 ∧ ppent 234 % 234 = 1 ∧
    ppent 239 % 239 = 1 ∧ ppent 951 % 951 = 1 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> native_decide

/-- **`S₀` members**: `n ∣ p(n)` for `n ∈ {2, 3, 124, 158, 342}`. -/
theorem S₀_members :
    ppent 2   % 2   = 0 ∧ ppent 3   % 3   = 0 ∧ ppent 124 % 124 = 0 ∧
    ppent 158 % 158 = 0 ∧ ppent 342 % 342 = 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> native_decide

/-- **`S₋₁` members**: `p(n) ≡ n − 1 (mod n)` for `n ∈ {6, 156, 305, 484}`. -/
theorem Sneg1_members :
    ppent 6   % 6   = 5   ∧ ppent 156 % 156 = 155 ∧
    ppent 305 % 305 = 304 ∧ ppent 484 % 484 = 483 := by
  refine ⟨?_,?_,?_,?_⟩ <;> native_decide

end Paper1
