import Mathlib

/-!
# Zero in the point spectrum of the universal cover is Hall's condition

By the criterion of Banks, Garza-Vargas and Mukherjee, `θ` is an eigenvalue of the universal
cover `T_G` iff `G` has a `θ`-Aomoto subset: a set `S` with `G[S]` a forest, `θ` an eigenvalue of
every component of `G[S]`, and `|∂_G S| < cc(G[S])`.

NOT NEW. This is Observation 4.2 of [BGM] combined with their Theorems 3.1 and 3.3. They prove
the reduction more strongly and more cheaply: their Lemma 4.2 gives each Aomoto tree a
nowhere-vanishing `λ`-eigenvector, and a kernel vector of a zero-potential tree operator cannot be
nonzero at the parent of a leaf, so at `λ = 0` every Aomoto tree is a single vertex. What follows
is a re-derivation by counting, kept because the counting core is reused elsewhere.

At `θ = 0` the criterion collapses to something elementary. An independent set has all components `K_1`,
whose eigenvalue is `0`, and `cc(G[S]) = |S|` with `∂_G S = N(S)`, so the Aomoto condition reads
`|N(S)| < |S|`: exactly the failure of Hall's marriage condition. The content is the converse,
that a general `0`-Aomoto subset can be replaced by an independent one.

The construction: the components `T_i` of `G[S]` are trees with no perfect matching (a forest has
`0` as an eigenvalue iff it has no perfect matching), so each has deficiency
`d i = |T_i| - 2 * nu i ≥ 1`. Take a maximum independent set in each; by König
`α i = |T_i| - nu i`, and their union `S'` is independent in `G` because distinct components of an
induced subgraph have no edges between them. Then `|S'| = Σ (nu i + d i)` and
`|N(S')| ≤ Σ nu i + |∂_G S|`.

`hall_zero_counting` below is the arithmetic core of that construction: it is what forces
`|N(S')| < |S'|`. As in `RamaLean/DegreeBound.lean`, the criterion of [BGM] is the analytic input
and is cited rather than reproved, and the combinatorial facts listed above (König, the deficiency
of a forest without a perfect matching, and the two cardinality bounds) enter as hypotheses.
-/

open Finset

/-- The counting core. Given components indexed by `comps`, each with matching number `nu i` and
deficiency `d i ≥ 1`, a boundary of size `b < comps.card`, an independent set `S'` of size
`sp = Σ (nu i + d i)` and a neighbourhood of size `nb ≤ Σ nu i + b`, Hall's condition fails for
`S'`. -/
theorem hall_zero_counting {ι : Type*} (comps : Finset ι) (nu d : ι → ℕ) (b sp nb : ℕ)
    (hd : ∀ i ∈ comps, 1 ≤ d i)
    (hb : b < comps.card)
    (hsp : sp = ∑ i ∈ comps, (nu i + d i))
    (hnb : nb ≤ (∑ i ∈ comps, nu i) + b) :
    nb < sp := by
  have hsplit : ∑ i ∈ comps, (nu i + d i) = (∑ i ∈ comps, nu i) + ∑ i ∈ comps, d i :=
    Finset.sum_add_distrib
  have hcard : comps.card ≤ ∑ i ∈ comps, d i := by
    calc comps.card = ∑ _i ∈ comps, 1 := by simp
      _ ≤ ∑ i ∈ comps, d i := Finset.sum_le_sum hd
  omega

/-- The same statement in the form it is used: a `0`-Aomoto subset yields an independent set
violating Hall's condition, so it is never a strictly weaker witness. -/
theorem hall_violator_of_aomoto_zero {ι : Type*} (comps : Finset ι) (nu d : ι → ℕ)
    (b sp nb : ℕ)
    (hd : ∀ i ∈ comps, 1 ≤ d i)
    (haom : b + 1 ≤ comps.card)
    (hsp : sp = ∑ i ∈ comps, (nu i + d i))
    (hnb : nb ≤ (∑ i ∈ comps, nu i) + b) :
    nb + 1 ≤ sp :=
  hall_zero_counting comps nu d b sp nb hd (by omega) hsp hnb
