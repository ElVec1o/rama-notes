# Lean 4 formalization — Papers 1 & 2

Machine-checked Lean 4 / Mathlib formalization of the verifiable content of
`proof1_partition_self_divisibility.md` and `proof2_cycle_graph_lift.md`.

- Toolchain: `leanprover/lean4:v4.30.0`, Mathlib `v4.30.0` (see `lean-toolchain`, `lakefile.toml`).
- Build: `lake exe cache get && lake build` (full build ≈ 2 min once Mathlib cache is present).
- Files: `RamaLean/Paper1.lean`, `RamaLean/Paper2.lean`, `RamaLean/Paper2General.lean`,
  `RamaLean/Paper2ExpFormula.lean`, `RamaLean/Paper3Permanent.lean`.

Trust base for every theorem: the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) plus, for the computational
lemmas only, the `native_decide` compiler axiom. The general theorems in
`Paper2General.lean` use **only the three standard axioms**. **No `sorry`, no
custom mathematical axioms** (verified with `#print axioms`).

## Paper 1 — `Paper1.lean`

The partition function is `p n := Fintype.card (Nat.Partition n)`, Mathlib's
genuine *combinatorial* definition (number of partitions of `n`).

**Part A (airtight, over the combinatorial definition — no recurrence, no Euler):**

| Theorem | Statement |
|---|---|
| `prop_i/ii/iii` | `p 5 ≡ 2 (mod 5)`, `p 7 ≡ 1 (mod 7)`, `p 11 ≡ 1 (mod 11)` |
| `seven_mem`, `eleven_mem`, `four_mem` | `7, 11, 4 ∈ S₁ = {n ≥ 2 : n ∣ p(n)−1}` |
| `five_not_mem` | `5 ∉ S₁` |
| `p_values`, `companion_small` | partition table; first members of `S₀`, `S₋₁` |

This is exactly the Proposition of `proof1`, proved against the real partition
type (feasible because `native_decide` enumerates `Nat.Partition n` for `n ≤ 11`).

**Part B (the full sequences, via Euler's pentagonal recurrence `ppent`):**
`ppent` is the efficient `O(n²)` recurrence; `ppent_eq_card_le_11` proves it
matches the combinatorial `p` everywhere the latter is enumerable. `S₁_members`,
`S₀_members`, `Sneg1_members` certify all the sequence terms listed in `paper1`
(through `n = 951`). These are statements about `ppent`; identifying `ppent` with
`p` for large `n` is Euler's Pentagonal Number Theorem (classical, not yet in
Mathlib), as flagged in the file.

## Paper 2 — `Paper2General.lean` (the derivation, re-derived in general)

**Theorem 1, general form** (`thm1_general` / `thm1_closed_form`), for **every**
`n` and `r`, over any characteristic-zero integral domain (e.g. `ℚ[x]`): any
sequence `Φ` with `Φ 0 = 1` satisfying the exponential-formula recurrence

    r·Φᵣ = Σ_{k=1}^r (2·T_{nk}(t) − 2)·Φᵣ₋ₖ

equals the Chebyshev closed form `Uᵣ(Y) − 2Uᵣ₋₁(Y) + Uᵣ₋₂(Y)` at `Y = Tₙ(t)`
(`x = 2t`; `T`, `U` are Mathlib's genuine Chebyshev polynomials, via the bridges
`cT_eq_chebyshev` / `cU_eq_chebyshev`). This re-derives the paper's Steps 3–5 —
the entire novel derivation — as machine-checked general theorems:

- `cf_comp` — Step 2's composition identity `f(k) = 2·Tₖ(Tₙ(t)) − 2 = 2·T_{nk}(t) − 2`
  (uses Mathlib's `Chebyshev.T_mul`).
- `cG_newton` — the closed form satisfies the exponential-formula (Newton)
  recurrence `r·Gᵣ = Σ f_k·Gᵣ₋ₖ` for all `r` (Steps 3–4 in log-derivative form;
  proved via a second-difference induction, `cC_seconddiff` + `cf_crux`).
- `cG_ogf_rec` / `cG_unique` — the OGF form: `cG` are exactly the coefficients of
  `(1−z)²/(1−2Yz+z²)` (Step 4), and this characterizes them (Step 5).
- `thm1_of_newton` — uniqueness: the Newton recurrence + `Φ₀ = 1` pin down `Φ = cG`.
- `cG_factored` / `thm1_factored` — **Theorem 1′**: the closed form factors,
  `Φᵣ = (2·Tₙ(t) − 2)·U_{r−1}(Tₙ(t)) = χ_{Cₙ}·Ψᵣ` — base characteristic
  polynomial × explicit quotient. (Via HPS 2018, `Ψᵣ` is the (r−1)-matching
  polynomial of `Cₙ`; the identity is equivalent to Hall's conjecture, proved
  combinatorially by Cochran et al. 2018 — this file gives an independent,
  machine-checked derivation.)
- `cT_neg` / `cU_neg` / `quotient_parity` — **parity corollary**:
  `Ψᵣ(−x) = (−1)^{n(r−1)}·Ψᵣ(x)`; the quotient is parity-supported like a
  matching polynomial (cf. `paper4`, where the same phenomenon for `K₄` is
  explained by HPS).

These use **only the standard axioms** (no `native_decide`).

**The exponential formula is now formalized too** (`Paper2ExpFormula.lean`,
July 2 round 3): `expFormula` proves `r·Aᵣ = Σₖ r^{(k)}·f k·Aᵣ₋ₖ` for the
`Sᵣ`-total of cycle weights over any commutative ring (via Mathlib's Cauchy
cycle-type count `card_of_cycleType_mul_eq`, a fiberwise grouping, and a
marked-part re-indexing of cycle types); `permAvg_newton` is the `Sᵣ`-average
version over a `ℚ`-algebra; and the capstone

    thm1_Sr : E_{σ∈Sᵣ}[ ∏_{ℓ ∈ cycles(σ)} (2·T_{nℓ}(t) − 2) ] = cG(Tₙ(t), r)

holds for every `n, r` over any `ℚ`-algebra domain — standard axioms only.

**What remains cited (one item):** a permutation lift of `Cₙ` by `σ` is the
disjoint union of cycles `C_{nℓ}`, `ℓ` over the cycle structure of `σ`, with
`char(C_m)(x) = 2·T_m(x/2) − 2`. Given that sentence, `thm1_Sr` IS the paper's
Theorem 1 (at `x = 2t`).

**Honest note on formalizing that sentence (investigated July 2, round 4).**
It is elementary *mathematics* but NOT a quick Lean close — it needs two pieces
Mathlib does not have: (a) permutation graph-lift infrastructure (adjacency of a
lift + its cycle decomposition), and (b) the spectrum of the cycle graph
(`Matrix.circulant` and `SimpleGraph.cycleGraph` exist, but there is **no**
circulant determinant/eigenvalue theorem, so `char(Cₘ) = 2Tₘ(x/2) − 2` must be
built from scratch — e.g. via the path-graph continuant `charpoly(Pₘ) = Uₘ(x/2)`
plus a cyclic corner expansion, then `Uₘ − Uₘ₋₂ = 2Tₘ`). Both are real
sub-projects (hundreds of lines of Fin-indexed determinant cofactor work);
together they are a legitimate Mathlib contribution, not a one-liner. So the
earlier "one elementary sentence" phrasing described the *math*, not the
*formalization cost*: closing it fully is future work, correctly scoped here.

## Paper 2 — `Paper2.lean` (computational cross-checks)

**`thm1_verified`**: the closed form checked in the kernel against the **direct
cycle-index computation** for all `n ∈ {2,…,6}`, `r ∈ {1,…,6}` — the same range
`paper2` checked in SymPy. Since the general derivation is now proved, this
computation serves as a small-case cross-check of the two *cited* classical
steps above.

**Corollary 1** (real-rootedness), proved in full generality:
- `cor1_numerator`: `sin(a+φ) − 2 sin a + sin(a−φ) = 2 sin a (cos φ − 1)`
- `cor1_factored`: `… = −4 sin a · sin²(φ/2)`, exhibiting all roots at
  `sin(rφ)=0` or `sin(φ/2)=0`, i.e. `x = 2cos θ ∈ [−2, 2]`.

**Corollary 2** (Fibonacci–Lucas evaluation `Φ_{C_n,r}(3) = (L(2n)−2)F(2nr)/F(2n)`):
- `cor2_reduction` — the **general** algebraic collapse
  `u_r − 2u_{r−1} + u_{r−2} = (t−2)u_{r−1}` (proved by `ring`).
- `cor2_fibLucas`, `cor2_phi3`, `cor2_n3` — the Fibonacci–Lucas number identity
  verified over `paper2`'s tested range (reproduces its "30/30 matches").

## Paper 3 — `Paper3Permanent.lean` (the mod-p permanent lemma)

The engine of Paper 3's Theorem 3 (`3 ∣ a(n)` for `n ≥ 13`), fully proved
(no `sorry`, standard axioms only):

- `permanent_eq_zero_of_col_period` — **Lemma A**: over `ZMod p`, if `c` has
  `orderOf c = p` and is a *column period* of `M` (`M i (c j) = M i j`), then
  `M.permanent = 0`. Proof: the permanent summand is constant on the left cosets
  of `⟨c⟩` (`summand_invariant`, `summand_zpow`), and each coset has
  `orderOf c = p` elements, so every coset contributes `p • (·) = 0` in `ZMod p`.
  With `c` a `p`-cycle through `p` equal columns this is "`≥ p` equal columns
  mod `p` ⟹ `p ∣ permanent`".
- `permanent_eq_zero_of_two_cols_eq` — the `p = 2` case (a transposition of two
  equal columns), i.e. the parity mechanism `2 ∣ a(n)`.

## Paper 3 — `Paper3Congruence.lean` (Theorem 3 end-to-end)

`three_dvd_gcd_permanent : ∀ n, 13 ≤ n → (gcdMat n).permanent = 0` over `ZMod 3`
— i.e. **`3 ∣ a(n)` for all `n ≥ 13`, fully machine-checked** (no `sorry`, no
`native_decide`, standard axioms only). It builds the 3-cycle through the
columns `1, 7, 13` (each `≡ (1,…,1) mod 3`, since every divisor of `1,7,13` is
`≡ 1 mod 3`) and applies Lemma A. So Theorem 3 is now formalized end-to-end,
number theory included.

## Paper 3 — `Paper3FourDivides.lean` (`4 ∣ a(n)`, machine-checked)

`Paper3Four.four_dvd_permanent : (4:ℤ) ∣ (gcdMat n).permanent` for **all `n ≥ 4`**
— i.e. `4 ∣ a(n)`, sharpening `2 ∣ a(n)` (`n ≥ 3`). Standard axioms only
(`propext, Classical.choice, Quot.sound`), no `sorry`, no `native_decide`.

The proof chain (226 lines, all self-contained over Mathlib):
- `permanent_sub_det` — the permanent−determinant identity `per M − det M = 2·S`,
  `S = ∑_{sign σ = −1} ∏ M(σi) i`.
- `gcd_factor` — **Smith factorization** `M = L·D·Lᵀ` (`L_{i,d}=[d+1∣i+1]`,
  `D=diag φ`), from `gcd = ∑_{d∣gcd} φ(d)` (`entry_sum`, via `Nat.sum_totient`).
- `gcd_det` — **Smith's determinant** `det[gcd(i,j)] = ∏_{k≤n} φ(k)` (a valuable
  standalone result: `det L = 1` since `L` is lower-triangular unit-diagonal).
- `four_dvd_gcd_det` — `4 ∣ det` for `n ≥ 4` (from `φ(3)φ(4) = 4`).
- `oddsum_even` — `2 ∣ S`: the even double transposition `τ = (0 2)(1 3)` is a
  fixed-point-free involution on the sign-`(−1)` permutations that preserves
  `∏ gcd mod 2` (it swaps values of equal parity), so mod 2 the sum pairs to `0`
  (via `Finset.sum_involution` over `ZMod 2` and `CharTwo.add_self_eq_zero`).
- Combining: `per = det + 2S`, `4 ∣ det`, `2 ∣ S` ⟹ `4 ∣ per`.

## `OrbitSumDivisibility.lean` — the tower engine (now a general ring lemma)

`card_dvd_sum_of_free_invariant` (the primitive): if a finite group `G` acts **freely**
on a fintype `X` and `f : X → R` (any `CommRing`) is `G`-invariant, then
`(Fintype.card G : R) ∣ ∑ x, f x` (each orbit has size `|G|`, `f` constant on it,
contributes `|G| • f(rep) = |G| * f(rep)`). Standard axioms, no `sorry`. Two corollaries:
- `sum_zmod_eq_zero_of_free_invariant` (`R = ZMod |G|`, so `|G| = 0`): the 2-adic tower —
  a free `(ℤ/2)^k` action by even permutations on the sign-`(−1)` terms, permuting the rows
  `≡ (1,…,1) mod 2^k`, gives `2^k ∣ Σ` hence `2^{k+1} ∣ a(n)`, and drives `4∣a`, `8∣a`.
- `factorial_dvd_permanent_of_ones_rows` (below): the linear-`v₂` kernel.

## `PermanentFactorial.lean` — `c! ∣ per M` for `c` all-ones rows (machine-checked)

`factorial_dvd_permanent_of_ones_rows : (c! : ℤ) ∣ M.permanent` whenever `c` rows of `M`
(indexed by `ι : Fin c ↪ Fin n`) are all-ones. Standard axioms, no `sorry`. Proof:
`Perm (Fin c)` acts freely on `Perm (Fin n)` by `τ • σ = (viaEmbeddingHom ι τ) * σ`; the
summand `∏ᵢ M (σ i) i = per`-term is invariant (an all-ones row contributes `1` however it
is permuted), so `card_dvd_sum_of_free_invariant` gives `|Perm (Fin c)| = c! ∣ per M`.
This is the machine-checked **kernel** of the linear bound (see next).

## `OddPermanentBound.lean` — `v₂(per) ≥ n − log₂n − 1` for any all-odd matrix

`OddPerm.two_pow_dvd_permanent_odd : (2:ℤ)^(n − ⌊log₂n⌋ − 1) ∣ (2·e + 1).permanent` — for
EVERY integer matrix all of whose entries are odd (standard axioms, no `sorry`). Proof:
`per(2e+1) = Σ_t 2^{|t|}·per(M_t)` (multilinear `Finset.prod_add` expansion; `M_t` = `e`-columns
on `t`, all-ones off `t`), each `per(M_t)` divisible by `(n−|t|)!` (`factorial_dvd_permanent`),
combined via `Finset.dvd_sum` + the exact factorial valuation `v₂((n−|t|)!)=(n−|t|)−s₂(·)`.
This is the engine of the **`c=1` attack**: the `w=0` grade of `a(n)=per[gcd]` is `N₀=per(M₁)²`
with `M₁` all-odd, so `v₂(N₀)=2·v₂(per M₁) ≥ n − O(log)` — the provable half of `c=1`.

## Paper 3 — `Paper3LinearRate.lean` (linear `v₂` bound, machine-checked, FULLY formalized)

`Paper3Linear.two_pow_dvd_permanent : (2:ℤ)^(⌈n/2⌉−⌊log₂n⌋−1) ∣ (gcdMat n).permanent`, i.e.
`v₂(a(n)) ≥ ⌈n/2⌉−log₂n−1 ~ n/2` — a **linear** lower rate `c=½` (replacing the old `½·log₂n`
tower), machine-checked end to end, standard axioms, no `sorry`. Chain:
- `gcd_eq_sum_divisors` — Smith pointwise `gcd(a,b) = ∑_{d∣b} [d∣a] φ(d)`.
- `permanent_expansion` — the Smith expansion of the **permanent**
  `a(n) = ∑_x (∏_i φ(x i)) · per(M_x)` (column multilinearity via `Finset.prod_univ_sum`) —
  the step that previously "needed Mathlib permanent multilinearity", now done from `permanent`'s
  definition + `prod_univ_sum`.
- `factorial_dvd_perm_Mx` — all-ones columns (`x i=1`) give `c₁! ∣ per(M_x)` (the kernel above).
- `two_pow_sub_digitsum_dvd_factorial` (exact `v₂(c₁!)=c₁−s₂(c₁)`, via
  `Nat.sub_one_mul_factorization_factorial`) + `Nat.totient_even` + `card_even_succ_le` assemble
  `2^{(c₁−s₂(c₁))+c₃} ∣` each term with `(c₁−s₂(c₁))+c₃ ≥ ⌈n/2⌉−log₂n−1`, then `Finset.dvd_sum`.

This is constant `c=½`, matching the paper's hand-bound exactly. The tighter `c=1`
(`v₂(a(n))~v₂(n!)`) needs a cancellation argument and stays open.

## Paper 3 — `Paper3EightDivides.lean` (`8 ∣ a(n)`, machine-checked)

`Paper3Four.eight_dvd_permanent : (8:ℤ) ∣ (gcdMat n).permanent` for **all `n ≥ 17`**.
Axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`. Structure:
- `abbrev KleinG := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)` — the acting
  group `(ℤ/2)²` (as a **reducible `abbrev`**, so the `Fintype`/`Group` instances are
  found without a diamond; a `set`/`let`-bound local silently breaks TC resolution here).
- `involHom a ha : Multiplicative (ZMod 2) →* G` — an involution `a` (`a²=1`) as a hom,
  glued by `MonoidHom.noncommCoprod` into `φ : KleinG →* Perm (Fin n)`.
- The action carries **four** rows `m = 1,5,13,17` (positions `0,4,12,16`), all `≡ 1 mod 4`,
  by the **regular `V₄`** `a=(c₀c₁)(c₂c₃)`, `b=(c₀c₂)(c₁c₃)`. The generators share points,
  so `Commute a b` comes from `perm_conj_swap` (`e·(swap c d)·e⁻¹ = swap (e c) (e d)`):
  `a·b·a⁻¹ = (c₁c₃)(c₀c₂) = b`.
- `φ` is injective (freeness): the four group elements send `c₀ ↦ c₀,c₁,c₂,c₃`, so
  `φ g` fixing `c₀` alone pins `g = 1` (a 4-way case split on the two exponents).
- `gcd_mod4_one`: every divisor of `m ≡ 1 mod 4` ⟹ `gcd(m,·) ≡ 1 mod 4`, so the action
  preserves `∏ gcd mod 4`. The engine then gives `4 ∣ Σ`; with `8 ∣ det`
  (`eight_dvd_gcd_det`, from `φ(3)·φ(5)=8`) and `per = det + 2Σ`, we get `8 ∣ per`.

This matches the paper's hand-bound (`n ≥ 17`) exactly. The reusable helper `perm_conj_swap`
(swap conjugation, proved by `ext` + `apply_ite`) is what makes the non-disjoint `V₄` clean.
