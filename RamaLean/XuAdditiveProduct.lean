import Mathlib
import RamaLean.HallCounterexample

/-!
# Xu's additive-product conjecture is false, and his own remark is the proof

Zili Xu (personal communication, August 2026) proposes a spectral-inclusion conjecture for
additive products. Let `A_1, …, A_c` be adjacency matrices of finite simple graphs on a common
vertex set, `X = AddProd(A_1,…,A_c)` the Mohanty–O'Donnell additive product, and

  `α(A_1,…,A_c; x) = E det(x I - ∑_j Q_j* A_j Q_j)`

the additive characteristic polynomial, the expectation over independent uniform `±1` diagonal
signings. Mohanty–O'Donnell prove `α` real-rooted with `Z(α) ⊆ [-ρ(X), ρ(X)]`, and Xu conjectures
the strengthening

  **Conjecture 2.1.** `Z(α(A_1,…,A_c; x)) ⊆ Spec(X)`.

His Remark 2.2 observes that taking the atoms to be the individual edge-adjacency matrices of a
finite graph `G` gives `α = μ_G` and `AddProd = UCT(G) = T`, so Conjecture 2.1 specialises to
`Z(μ_G) ⊆ Spec(T)` — which is Conjecture 10 of the companion work at `d = 1`.

**That statement is false.** Chris Hall's graph is a counterexample, and this file assembles the
refutation from pieces already proved: `HallCounterexample.muG_root_sqrt5` puts `√5` among the
zeros of `μ_G`, and the exclusion `√5 ∉ Spec(T)` is the Angel–Friedman–Hoory certificate whose
algebra is verified in `HallCounterexample` Parts B–D and packaged by
`RatioCertificate.spec_excluded`.

So Conjecture 2.1 falls, and it falls through Xu's own Remark 2.2 rather than through any new
mathematics. `xu_conj24_false` records that Conjecture 2.4, the `(k,m)`-characteristic-polynomial
restatement, falls with it via his Proposition 2.3.

## What is hypothesis and what is proved

The edge-atom specialisation is Xu's Remark 2.2, and it enters as the hypothesis `hedge`: the
additive characteristic polynomial of the edge-atom system of Hall's graph *is* `μ_G`. The
exclusion enters as `hspec`, since Angel–Friedman–Hoory is not in Mathlib and the note carries it
as a cited input throughout. Everything between those two inputs and the conclusion is checked
here. That is the honest division: we do not re-prove his remark or their theorem, we show that
together with the verified certificate they refute the conjecture.

## Why this matters beyond the one conjecture

Xu closes his note with a dichotomy: either Conjecture 2.1 holds for all additive products, in
which case the graph case follows by the edge-atom specialisation, or it fails somewhere, in
which case real-rootedness, the free-like walk moment identities and the spectral-radius bound
are not sufficient for spectral inclusion, and any proof must use an additional property of
edge-atom systems. `xu_dichotomy_second_branch` records which branch holds, and it is sharper
than the dichotomy allows: the failure is **already in the edge-atom case**, so it is not a
question of how general the atoms are, and no further property of edge-atom systems can rescue
the statement. The repair has to restrict the graph class.

## Status

`xu_conj21_false`, `xu_conj24_false` and `xu_dichotomy_second_branch` are `VERIFIED`, modulo the
two inputs named above. The conjecture they refute is Xu's, stated as he states it.
-/

namespace XuAdditiveProduct

open Polynomial

variable {Sys : Type*}

/-- **Xu's Conjecture 2.1**, over an abstract index `Sys` of atom systems: for every system,
every zero of its additive characteristic polynomial lies in the spectrum of its additive
product. -/
def AdditiveProductInclusion (alpha : Sys → ℝ → ℝ) (Spec : Sys → Set ℝ) : Prop :=
  ∀ S : Sys, ∀ y : ℝ, alpha S y = 0 → y ∈ Spec S

/-- **Conjecture 2.1 is false.**  Instantiating at the edge-atom system of Hall's graph, where
Xu's Remark 2.2 identifies `α` with `μ_G` and the additive product with the universal cover,
the value `√5` is a zero of `μ_G` and lies outside the spectrum. -/
theorem xu_conj21_false (alpha : Sys → ℝ → ℝ) (Spec : Sys → Set ℝ) (edge : Sys)
    (hedge : ∀ y : ℝ, alpha edge y = aeval y HallCounterexample.muG)
    (hspec : Real.sqrt 5 ∉ Spec edge) :
    ¬ AdditiveProductInclusion alpha Spec := by
  intro h
  refine hspec (h edge (Real.sqrt 5) ?_)
  rw [hedge]
  exact HallCounterexample.muG_root_sqrt5

/-- **Conjecture 2.4 falls with it.**  Xu's Proposition 2.3 gives
`ψ_{k,m}[k 𝒜_bd] = α(A_1,…,A_k)`, so the block-diagonal `(k,m)` restatement is the same
statement and the same instance refutes it. -/
theorem xu_conj24_false (psi alpha : Sys → ℝ → ℝ) (Spec : Sys → Set ℝ) (edge : Sys)
    (hprop23 : ∀ S : Sys, ∀ y : ℝ, psi S y = alpha S y)
    (hedge : ∀ y : ℝ, alpha edge y = aeval y HallCounterexample.muG)
    (hspec : Real.sqrt 5 ∉ Spec edge) :
    ¬ AdditiveProductInclusion psi Spec := by
  intro h
  refine hspec (h edge (Real.sqrt 5) ?_)
  rw [hprop23, hedge]
  exact HallCounterexample.muG_root_sqrt5

/-- **Which branch of the dichotomy holds, and it is sharper than stated.**  Xu's second branch
supposes the conjecture fails for *some* atom system, leaving open that a proof for graphs might
still be recovered from an extra property of edge-atom systems.  It fails for the edge-atom
system itself, so there is nothing about edge atoms left to add: the graph statement is false as
it stands, and only restricting the class can repair it. -/
theorem xu_dichotomy_second_branch (alpha : Sys → ℝ → ℝ) (Spec : Sys → Set ℝ) (edge : Sys)
    (hedge : ∀ y : ℝ, alpha edge y = aeval y HallCounterexample.muG)
    (hspec : Real.sqrt 5 ∉ Spec edge) :
    ¬ (∀ y : ℝ, alpha edge y = 0 → y ∈ Spec edge) := by
  intro h
  refine hspec (h (Real.sqrt 5) ?_)
  rw [hedge]
  exact HallCounterexample.muG_root_sqrt5

end XuAdditiveProduct
