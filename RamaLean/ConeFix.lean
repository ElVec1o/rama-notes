/-
Audit-session formalization: the corrected solvability criterion behind
`prop:cone` of paper2b_note/note.tex.

CONTEXT. Idempotency at order two is `X_k - P_k X_k - X_k P_k = D_k^2`, whose
`(i,j)` entry for a coordinate projection is `X_ij * (1 - (P_k)_ii - (P_k)_jj)`.
Write `c k` for that coefficient and `d k` for `(D_k^2)_ij`. Then

  c k = -1  if both i,j lie in e_k        (X_ij forced)
  c k = +1  if neither lies in e_k        (X_ij forced)
  c k =  0  if exactly one lies in e_k    (X_ij free, and the equation demands d k = 0)

For `D` in the kernel of the linearisation, `D_k` is supported on pairs with exactly
one endpoint in `e_k`, so `D_k^2` vanishes on those pairs: that is the hypothesis
`hcd` below, and it is automatic rather than assumed.

The paper's proof of sufficiency takes `X` diagonal with every off-diagonal block
zero. That is invalid: the diagonal BLOCKS of `D_k^2` are `M Mᵀ` and `Mᵀ M`, which
are not diagonal, so at a same-side off-diagonal entry the coefficient is ±1 and
`X_ij` is forced to a nonzero value. `solvable_iff` below is what actually governs
each entry.

CONSEQUENCE. Summing over `k`, the entry `(i,j)` is solvable iff some `k` splits the
pair (leaving a free entry to absorb the sum) or the forced values already cancel.
Since `c k = 0` exactly when `k` splits `{i,j}`, and a pair is split by no hyperedge
exactly when the two vertices lie in the same hyperedges, the criterion `Q_j(D) = 0`
(the diagonal case, where no `k` ever splits `{j,j}`) is complete **iff the family has
no twin vertices**. With twins, each twin pair contributes one further quadric.
-/
import Mathlib

open Finset

namespace ConeFix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Entrywise solvability of the order-two equation.**

`c k` is the coefficient `1 - (P_k)_ii - (P_k)_jj`, `d k` is `(D_k²)_ij`, and `hcd`
records that where the coefficient vanishes so does the right-hand side.

A correction with `∑ k, x k = 0` exists at this entry exactly when some `k` leaves it
free, or else the forced values already sum to zero. Division by zero is `0` in Lean,
so the sum `∑ k, d k / c k` automatically ranges over the forced entries only. -/
theorem solvable_iff (c d : κ → ℝ) (hcd : ∀ k, c k = 0 → d k = 0) :
    (∃ x : κ → ℝ, (∀ k, x k * c k = d k) ∧ ∑ k, x k = 0) ↔
      ((∃ k, c k = 0) ∨ ∑ k, d k / c k = 0) := by
  constructor
  · rintro ⟨x, hx, hsum⟩
    by_cases h : ∃ k, c k = 0
    · exact Or.inl h
    · push_neg at h
      refine Or.inr ?_
      rw [← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hx k, mul_div_assoc, div_self (h k), mul_one]
  · rintro (⟨k₀, hk₀⟩ | hsum)
    · -- a free entry at `k₀` absorbs whatever the forced entries sum to
      set S := ∑ m ∈ univ.erase k₀, d m / c m with hS
      refine ⟨fun k => if k = k₀ then -S else d k / c k, fun k => ?_, ?_⟩
      · dsimp only
        by_cases hk : k = k₀
        · rw [if_pos hk, hk, hk₀, mul_zero]
          exact (hcd k₀ hk₀).symm
        · rw [if_neg hk]
          by_cases hc : c k = 0
          · rw [hc, mul_zero]; exact (hcd k hc).symm
          · exact div_mul_cancel₀ _ hc
      · dsimp only
        rw [← Finset.add_sum_erase _ _ (mem_univ k₀), if_pos rfl]
        have hrest : ∑ m ∈ univ.erase k₀, (if m = k₀ then -S else d m / c m) = S := by
          rw [hS]
          exact Finset.sum_congr rfl fun m hm => if_neg (Finset.ne_of_mem_erase hm)
        rw [hrest]
        ring
    · -- the forced values already cancel
      refine ⟨fun k => d k / c k, fun k => ?_, hsum⟩
      dsimp only
      by_cases hc : c k = 0
      · rw [hc, mul_zero]; exact (hcd k hc).symm
      · exact div_mul_cancel₀ _ hc

/-- The order-two coefficient `1 - (P_k)_ii - (P_k)_jj` at entry `(i,j)`, written from
the two membership bits. -/
def coef (bi bj : Bool) : ℝ := 1 - (if bi then 1 else 0) - (if bj then 1 else 0)

/-- **The coefficient vanishes exactly when the hyperedge splits the pair.**

This is what makes `solvable_iff`'s free case combinatorial: `c k = 0` iff exactly one
of `i`, `j` lies in `e_k`. -/
theorem coef_eq_zero_iff (bi bj : Bool) : coef bi bj = 0 ↔ bi ≠ bj := by
  cases bi <;> cases bj <;> norm_num [coef]

omit [DecidableEq κ] in
/-- **The missing hypothesis, in combinatorial form.**

No hyperedge splits `{i,j}` precisely when `i` and `j` lie in exactly the same
hyperedges: they are twins. Combined with `solvable_iff`, this is the condition under
which `prop:cone`'s criterion `Q_j(D) = 0` is complete. A diagonal entry has `bi = bj`
always, so no `k` splits it and the criterion there is exactly `Q_j(D) = 0`; an
off-diagonal entry is free somewhere unless its two vertices are twins, in which case
it contributes one further quadric that the proposition does not state. The research
log records the twin-free condition as measured ("no pair (i,j) has K_ij empty at any
family tested"), not proved. -/
theorem no_free_entry_iff_twin (b b' : κ → Bool) :
    (∀ k, coef (b k) (b' k) ≠ 0) ↔ (∀ k, b k = b' k) := by
  constructor
  · intro h k
    by_contra hk
    exact h k ((coef_eq_zero_iff (b k) (b' k)).2 hk)
  · intro h k
    simp only [ne_eq, coef_eq_zero_iff, not_not]
    exact h k

/- **The counterexample entry.**

Family: vertices `{0,…,5}`, hyperedges `{0,1,2}, {0,1,3}, {2,4,5}, {3,4,5}` — distinct,
3-uniform, 2-regular, so `∑_k P_k = 2I` with every `P_k` of rank 3. The vertices `0` and
`1` are twins. Kernel direction (checked in exact rational arithmetic):

  `D₁ = E₀₄+E₄₀+E₁₄+E₄₁`,  `D₂ = 0`,  `D₃ = -(E₀₄+E₄₀)`,  `D₄ = -(E₁₄+E₄₁)`

Each `D_k` is supported on pairs split by `e_k`, `∑_k D_k = 0`, and `Q_j(D) = 0` at all
six vertices — so `D` satisfies `prop:cone`'s criterion in full. At the twin entry
`(0,1)` the coefficients are `(-1,-1,+1,+1)`, all nonzero, and the right-hand sides
`(D_k²)₀₁` are `(1,0,0,0)`. Every `(X_k)₀₁` is therefore forced and their sum is `-1 ≠ 0`,
so no second-order correction exists.

Hence the proposition's "if and only if" is **false as stated**: this `D` satisfies
`Q_j(D) = 0` everywhere and admits no `X`. -/
/-- coefficients at the twin entry `(0,1)`: `-1` for the two hyperedges containing both
vertices, `+1` for the two containing neither. -/
def cEx : Fin 4 → ℝ := fun k => if (k : ℕ) < 2 then -1 else 1

/-- right-hand sides `(D_k²)₀₁` at that entry. -/
def dEx : Fin 4 → ℝ := fun k => if (k : ℕ) = 0 then 1 else 0

theorem cone_counterexample :
    ¬ ∃ x : Fin 4 → ℝ, (∀ k, x k * cEx k = dEx k) ∧ ∑ k, x k = 0 := by
  intro h
  have hcd : ∀ k, cEx k = 0 → dEx k = 0 := by
    intro k; fin_cases k <;> simp [cEx, dEx]
  rcases (solvable_iff _ _ hcd).1 h with ⟨k, hk⟩ | hsum
  · fin_cases k <;> simp [cEx] at hk
  · rw [Fin.sum_univ_four] at hsum
    simp [cEx, dEx] at hsum


end ConeFix
