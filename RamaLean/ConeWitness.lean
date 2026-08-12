/-
Audit-session formalization: the matrix-level facts of the counterexample to
`prop:cone` (paper2b_note/note.tex:1999-2007), so that the whole witness is
machine-checked rather than checked in exact arithmetic outside Lean.

Family: vertices `Fin 6`, hyperedges `{0,1,2}, {0,1,3}, {2,4,5}, {3,4,5}` — distinct,
3-uniform, 2-regular, so every `P_k` has rank 3 and `∑_k P_k = 2·I`. Vertices `0` and `1`
lie in exactly the same hyperedges (`{0,1,2}` and `{0,1,3}`): they are twins.

Direction: `D₀ = E₀₄+E₄₀+E₁₄+E₄₁`, `D₁ = 0`, `D₂ = -(E₀₄+E₄₀)`, `D₃ = -(E₁₄+E₄₁)`.

The four theorems below establish, by kernel computation:
  * each `D_k` is supported on pairs split by `e_k`, so `P_k D_k + D_k P_k = D_k`;
  * `∑_k D_k = 0`, the linearised tightness constraint;
  * `Q_j(D) = 0` at every one of the six vertices — the proposition's criterion, in full;
  * the forced sum at the twin entry `(0,1)` equals `-1 ≠ 0`.

Since `0` and `1` are twins, no hyperedge splits that pair, so every `(X_k)₀₁` is forced
by order two and their sum cannot be corrected: no second-order `X` exists. Combined with
`ConeFix.solvable_iff`, this refutes the proposition's "if and only if".
-/
import Mathlib

open Matrix

namespace ConeWitness

/-- the four hyperedges -/
def E : Fin 4 → List (Fin 6) := ![[0, 1, 2], [0, 1, 3], [2, 4, 5], [3, 4, 5]]

/-- vertex `i` lies in hyperedge `k` -/
def mem (k : Fin 4) (i : Fin 6) : Bool := (E k).contains i

/-- `σ_k(j) = 1 - 2(P_k)_jj`, the order-two coefficient at a diagonal entry -/
def sgn (k : Fin 4) (i : Fin 6) : ℤ := if mem k i then -1 else 1

/-- the kernel direction, one matrix per hyperedge -/
def D : Fin 4 → Matrix (Fin 6) (Fin 6) ℤ :=
  ![ !![0,0,0,0,1,0; 0,0,0,0,1,0; 0,0,0,0,0,0; 0,0,0,0,0,0; 1,1,0,0,0,0; 0,0,0,0,0,0],
     0,
     !![0,0,0,0,-1,0; 0,0,0,0,0,0; 0,0,0,0,0,0; 0,0,0,0,0,0; -1,0,0,0,0,0; 0,0,0,0,0,0],
     !![0,0,0,0,0,0; 0,0,0,0,-1,0; 0,0,0,0,0,0; 0,0,0,0,0,0; 0,-1,0,0,0,0; 0,0,0,0,0,0] ]

/-- **Vertices 0 and 1 are twins**: every hyperedge contains both or neither. Hence no
hyperedge splits the pair `(0,1)`, so every `(X_k)₀₁` is forced by order two. -/
theorem twins : ∀ k, mem k 0 = mem k 1 := by decide

/-- **Each `D_k` is supported on pairs split by `e_k`**, which is exactly the order-one
equation `P_k D_k + D_k P_k = D_k` for a coordinate projection. -/
theorem cross_supported : ∀ k i j, D k i j ≠ 0 → mem k i ≠ mem k j := by decide

/-- **Linearised tightness**: the direction is admissible. -/
theorem sum_D_eq_zero : ∑ k, D k = 0 := by decide

/-- **The proposition's criterion holds in full**: `Q_j(D) = 0` at all six vertices. -/
theorem Q_eq_zero : ∀ j, (∑ k, sgn k j * (D k * D k) j j) = 0 := by decide

/-- **But the twin entry cannot be corrected**: the forced values of `(X_k)₀₁` sum to `-1`.
With `ConeFix.solvable_iff` (all four coefficients at this entry are `±1`, hence nonzero),
no second-order correction exists — refuting the proposition as stated. -/
theorem twin_obstruction : (∑ k, sgn k 0 * (D k * D k) 0 1) = -1 := by decide


end ConeWitness
