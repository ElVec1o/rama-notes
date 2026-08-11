import Mathlib

/-!
# No bound that reads only the spectra can settle the extremality question

The obstruction recorded as I21 in the research log, and in the note's obstruction list. It is the
reason a sweep of standard tools all failed in the same way, and it is short enough that there is no
excuse for leaving it as prose.

## The statement

Fix `p, q, a, b` and let the class be the tight rank-`b` projection families: `A_k` symmetric
idempotent of rank `b`, with `∑ₖ A_k = a·I`. Suppose someone proposes

  `maxroot μ[A] ≤ F(a, b, p, q, spec A_1, …, spec A_q)`.

Then that bound cannot reduce the extremality question, for a reason with no analysis in it. Every
block of every family in the class is a rank-`b` projection, so its spectrum is `b` ones and `p - b`
zeros, the *same* multiset for every family. So the right-hand side is a constant on the class. A
bound by a constant that is valid on the class has that constant at least the supremum, and a bound
strong enough to give the target has it at most the target's value. The two force equality: such an
`F` is the band edge itself, and assuming it is assuming the conclusion.

## What is formalised

Two independent halves, so the argument cannot lean on a slogan.

* **The spectra really are constant.** `pow_succ_of_idem` gives `A^(j+1) = A` for an idempotent, so
  every power trace equals the trace, which is the rank. `traces_eq_of_idem` turns that into: two
  families of idempotents with equal block traces have equal power traces at every order.
  `const_of_factors_through_traces` is the consequence for any functional that reads only those,
  which is what "spectral" means, the power sums determining the spectrum of a symmetric matrix.
  `variance_of_idem` is the special case that killed the dream lemma D1: the Poisson-binomial
  variance `b/a - tr(A_k²)/a²` of the DPP marginal collapses to `(b/a)(1 - 1/a)` identically.

* **The no-go template.** `le_const_of_spectral_bound`, then `le_of_approach` for the lower bound on
  `F` coming from families approaching the edge, then `spectral_bound_is_the_target`, which is the
  punchline: an `F` that is both valid and strong enough satisfies `F s₀ = L`, and the bound it
  gives is literally `∀ A, m A ≤ L`, the statement one wanted to prove.

The template is stated for an arbitrary class, an arbitrary real functional `m` and arbitrary
"spectral data" `S`, because the argument uses nothing else. Instantiating it needs the class
nonempty and `m` approaching `L`, which is Proposition 38 of the note, the commuting families
realising the constant; that is the content of `XuSharp.approach_of_tendsto` and is a hypothesis
here rather than a claim.

## What this does not say

It does not say the extremality question is hard, and it does not say no proof exists. It says the
proof must read a functional that separates families with identical block spectra, hence a *joint*
invariant of the tuple. The commutator sum `∑_{i<j} ‖[A_i, A_j]‖²_F` is such a functional and is
not blocked; that observation is the successor question, not something proved here.

## Status

`pow_succ_of_idem`, `trace_pow_of_idem`, `traces_eq_of_idem`, `const_of_factors_through_traces`,
`variance_of_idem`, `le_const_of_spectral_bound`, `le_of_approach`, `spectral_bound_is_the_target`
and `target_gives_spectral_bound` are `VERIFIED`.
-/

namespace SpectralNoGo

open Matrix

section Idempotent

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- An idempotent is its own every positive power. The whole spectral collapse is this line: a
rank-`b` projection has no data in it beyond `b`. -/
theorem pow_succ_of_idem (A : Matrix n n R) (h : A * A = A) : ∀ j : ℕ, A ^ (j + 1) = A := by
  intro j
  induction j with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h]

/-- Every power trace of an idempotent is its trace, which for a projection is its rank. -/
theorem trace_pow_of_idem (A : Matrix n n R) (h : A * A = A) (j : ℕ) :
    trace (A ^ (j + 1)) = trace A := by
  rw [pow_succ_of_idem A h j]

/-- Two families of idempotents with equal block traces have equal power traces at every order.
For symmetric matrices the power sums determine the spectrum, so this says the two families are
spectrally indistinguishable, block by block, however different they are as tuples. -/
theorem traces_eq_of_idem {κ : Type*} (A B : κ → Matrix n n R)
    (hA : ∀ k, A k * A k = A k) (hB : ∀ k, B k * B k = B k)
    (htr : ∀ k, trace (A k) = trace (B k)) (k : κ) (j : ℕ) :
    trace ((A k) ^ (j + 1)) = trace ((B k) ^ (j + 1)) := by
  rw [trace_pow_of_idem _ (hA k), trace_pow_of_idem _ (hB k), htr k]

/-- **Any spectral functional is constant on the class.** `S` is spectral when it factors through
the power traces of the blocks, which is what it means to depend only on the spectra. Then `S`
cannot tell two tight rank-`b` projection families apart, since the block ranks are the same `b`
for both. No hypothesis about `∑ₖ A_k` is needed: idempotency alone does it. -/
theorem const_of_factors_through_traces {κ : Type*} {σ : Type*}
    (S : (κ → Matrix n n R) → σ) (G : (κ → ℕ → R) → σ)
    (hfac : ∀ A, S A = G (fun k j => trace ((A k) ^ (j + 1))))
    (A B : κ → Matrix n n R)
    (hA : ∀ k, A k * A k = A k) (hB : ∀ k, B k * B k = B k)
    (htr : ∀ k, trace (A k) = trace (B k)) :
    S A = S B := by
  rw [hfac A, hfac B]
  exact congrArg G (funext fun k => funext fun j => traces_eq_of_idem A B hA hB htr k j)

end Idempotent

/-- The dream lemma D1 collapses. `Var_k = b/a - tr(A_k²)/a²` is the variance of the
Poisson-binomial marginal of the associated determinantal process, and on the class it takes the
single value `(b/a)(1 - 1/a)` for every family and every block. A bound increasing in `Var_k` and
equal to the band edge at that value therefore says exactly `maxroot ≤ band edge`, which is the
target, not a reduction of it. -/
theorem variance_of_idem {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : A * A = A) (a b : ℝ) (ha : a ≠ 0) (htr : trace A = b) :
    b / a - trace (A * A) / a ^ 2 = (b / a) * (1 - 1 / a) := by
  rw [h, htr]
  field_simp

section NoGo

variable {C : Type*} {σ : Type*} {m : C → ℝ} {S : C → σ} {s₀ : σ} {F : σ → ℝ} {L : ℝ}

/-- A bound through data that is constant on the class is a bound by a constant. -/
theorem le_const_of_spectral_bound (hconst : ∀ A, S A = s₀) (hF : ∀ A, m A ≤ F (S A)) (A : C) :
    m A ≤ F s₀ := by
  have h := hF A
  rwa [hconst A] at h

/-- If the class contains families whose value approaches `L`, then any valid spectral bound has
`F s₀ ≥ L`. In the application `L = (√(a-1) + √(b-1))²` and the approaching families are the
commuting ones of Proposition 38. -/
theorem le_of_approach (hconst : ∀ A, S A = s₀) (hF : ∀ A, m A ≤ F (S A))
    (happ : ∀ ε > 0, ∃ A : C, L - ε < m A) : L ≤ F s₀ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨A, hA⟩ := happ ε hε
  have : L - ε < F s₀ := lt_of_lt_of_le hA (le_const_of_spectral_bound hconst hF A)
  linarith

/-- **The no-go.** Suppose `F` is a valid spectral bound and is strong enough to deliver the target
`m ≤ L`, that is `F s₀ ≤ L`. Then `F s₀ = L` on the nose, and the bound it provides is the target
verbatim. So no such `F` reduces the problem: proving the bound and proving the target are the same
task, and the sweep of tools that all produce bounds of this shape was never going to close it. -/
theorem spectral_bound_is_the_target (hconst : ∀ A, S A = s₀) (hF : ∀ A, m A ≤ F (S A))
    (happ : ∀ ε > 0, ∃ A : C, L - ε < m A) (huse : F s₀ ≤ L) :
    F s₀ = L ∧ ∀ A, m A ≤ L :=
  ⟨le_antisymm huse (le_of_approach hconst hF happ),
   fun A => le_trans (le_const_of_spectral_bound hconst hF A) huse⟩

/-- The converse direction, which is what makes the previous theorem an obstruction rather than a
curiosity: the target does produce a spectral bound, the constant one. So spectral bounds valid on
the class are exactly the statements at least as strong as the target, and none is weaker. -/
theorem target_gives_spectral_bound (htarget : ∀ A : C, m A ≤ L) (S : C → σ) :
    ∃ F : σ → ℝ, ∀ A, m A ≤ F (S A) :=
  ⟨fun _ => L, htarget⟩

end NoGo

end SpectralNoGo
