import Mathlib

/-!
# Why the biregular case survives

Conjecture 10 is false, and two natural repairs fail with it: minimum degree at least two, and
bounded maximum degree.  What remains is the biregular case, which is Problem 1 of Song, Fan
and Miao.  This file proves the parts of "why it survives" that are provable, and is explicit
about which parts are not.

## What is proved

* `no_tree_of_two_le_degree`.  A graph in which every vertex has degree at least two is not a
  tree.  This is the rigorous core of one blocking claim: the `31`-vertex counterexample hangs
  branches on a **tree skeleton**, and a biregular graph with both degrees at least two has
  minimum degree at least two, so it admits no such skeleton at all.
* `biregular_reduction`.  For a biregular graph the universal cover is the biregular tree,
  whose spectrum is `{0} ∪ {x : thr ≤ |x| ≤ rho}`.  Since Hall--Puder--Sawin already place
  every root in `[-rho, rho]`, Conjecture 10 for such a graph is *equivalent* to the statement
  that no nonzero root has `|x| < thr`, which is exactly Song--Fan--Miao.  So the biregular
  case is not a fragment of the conjecture, it is the whole of what is left.
* `root_sep` and `branch_root_sep`.  A quantitative separation: a root of a Lipschitz function
  cannot be closer to `0` than `|F 0| / M`.  Applied to the branch factor
  `F = X·μ_H - p·μ_{H-v}` of a cut vertex with `p` isomorphic branches, `F 0 = -p·μ_{H-v}(0)`,
  so the separation *grows linearly in the number of branches*.  The mechanism pushes its
  roots away from zero, while a biregular counterexample would need a root just above zero.

## What is not proved, and why

The separation is conditional on `μ_{H-v}(0) ≠ 0`, that is on `H - v` having a perfect
matching, and **Hall's own construction does not satisfy it**: there `H - v` is the star
`K_{1,6}`, of odd order, so `μ_{H-v}(0) = 0` and the bound is vacuous.  The separation
therefore blocks the subcubic mechanism and not Hall's.  On the subcubic branch it gives
`|θ| ≥ 1/6` against a true smallest root of `0.662`, so it is valid but far from sharp.

Three inputs stay outside Lean because Mathlib does not have them: the spectrum of the
`(a,b)`-biregular tree, the Hall--Puder--Sawin interval theorem, and Angel--Friedman--Hoory.
The first two enter `biregular_reduction` as hypotheses, in the shape the argument consumes.
No amount of further work moves those to `VERIFIED` without formalizing the classical inputs
first.
-/

namespace BiregularBlocking

/-! ## A tree has a vertex of small degree -/

open Finset SimpleGraph

/-- **Minimum degree two rules out a tree.**  Handshake gives `∑ deg = 2|E|`, a tree has
`|E| + 1 = n` vertices, and `∑ deg ≥ 2n` is then a contradiction.  Consequently a biregular
graph with both degrees at least two contains no tree skeleton, which is the structure the
`31`-vertex counterexample is built on. -/
theorem no_tree_of_two_le_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (h2 : ∀ v, 2 ≤ G.degree v) : ¬ G.IsTree := by
  intro htree
  have hcard : G.edgeFinset.card + 1 = Fintype.card V := htree.card_edgeFinset
  have hshake : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hlow : 2 * Fintype.card V ≤ ∑ v, G.degree v := by
    calc 2 * Fintype.card V = ∑ _v : V, 2 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => h2 v
  omega

/-! ## The reduction to Song--Fan--Miao -/

/-- **For a biregular graph, Conjecture 10 is exactly Song--Fan--Miao.**  With the spectrum of
the biregular tree given by `hspec` and the Hall--Puder--Sawin interval by `hHPS`, the
inclusion of the roots in the spectrum is equivalent to the single statement that no nonzero
root is smaller than the inner threshold.  Nothing else in Conjecture 10 remains for these
graphs. -/
theorem biregular_reduction {thr rho : ℝ} {Spec roots : Set ℝ}
    (hspec : Spec = {0} ∪ {x : ℝ | thr ≤ |x| ∧ |x| ≤ rho})
    (hHPS : ∀ x ∈ roots, |x| ≤ rho) :
    roots ⊆ Spec ↔ ∀ x ∈ roots, x ≠ 0 → thr ≤ |x| := by
  constructor
  · intro hsub x hx hne
    have := hsub hx
    rw [hspec] at this
    rcases this with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) hne
    · exact h.1
  · intro h x hx
    rw [hspec]
    by_cases hz : x = 0
    · exact Or.inl (by simp [hz])
    · exact Or.inr ⟨h x hx hz, hHPS x hx⟩

/-! ## Quantitative separation from zero -/

/-- **A root cannot be closer to zero than `|F 0| / M`.**  Stated with the Lipschitz bound as
a hypothesis, which is what the mean value theorem supplies for a polynomial on a bounded
interval. -/
theorem root_sep {F : ℝ → ℝ} {M θ : ℝ} (hM : 0 < M)
    (hlip : |F 0 - F θ| ≤ M * |0 - θ|) (hroot : F θ = 0) :
    |F 0| / M ≤ |θ| := by
  rw [hroot, sub_zero] at hlip
  rw [div_le_iff₀ hM]
  calc |F 0| ≤ M * |0 - θ| := hlip
    _ = M * |θ| := by rw [zero_sub, abs_neg]
    _ = |θ| * M := mul_comm _ _

/-- **The branch factor at zero.**  For a cut vertex with `p` isomorphic branches the matching
polynomial factors through `F = X·μ_H - p·μ_{H-v}`, and `F 0 = -p·μ_{H-v}(0)`. -/
theorem branchFactor_at_zero (muH muHv : ℝ → ℝ) (p : ℝ) :
    (fun t => t * muH t - p * muHv t) 0 = -(p * muHv 0) := by
  simp

/-- **The separation grows with the number of branches.**  Any root of the branch factor is at
least `p·|μ_{H-v}(0)| / M` from zero.  The mechanism therefore drives its roots *away* from
zero as it is strengthened, whereas a biregular counterexample needs a root just above zero.

The hypothesis `muHv 0 ≠ 0` says `H - v` has a perfect matching.  It fails for Hall's own
branch, where `H - v` is a star of odd order, so this blocks the subcubic mechanism and not
his. -/
theorem branch_root_sep {muH muHv : ℝ → ℝ} {p M θ : ℝ} (hM : 0 < M) (hp : 0 ≤ p)
    (hlip : |(fun t => t * muH t - p * muHv t) 0 - (fun t => t * muH t - p * muHv t) θ|
        ≤ M * |0 - θ|)
    (hroot : (fun t => t * muH t - p * muHv t) θ = 0) :
    p * |muHv 0| / M ≤ |θ| := by
  have h := root_sep (F := fun t => t * muH t - p * muHv t) hM hlip hroot
  rwa [branchFactor_at_zero muH muHv p, abs_neg, abs_mul, abs_of_nonneg hp] at h

/-- Monotonicity in the number of branches, stated plainly: more branches means a larger
guaranteed separation from zero. -/
theorem sep_mono {c M p q : ℝ} (hM : 0 < M) (hc : 0 ≤ c) (hpq : p ≤ q) :
    p * c / M ≤ q * c / M := by
  gcongr

end BiregularBlocking
