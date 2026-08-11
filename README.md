# RAMA-NOTEBOOK

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21433867.svg)](https://doi.org/10.5281/zenodo.21433867)

Four short number-theory / combinatorics notes and a methodology note, each pairing a computational
result with a Lean 4 + Mathlib formalization. Everything here builds and is machine-checked; conjectures
are labeled as such.

> **Formalization status:** the Lean library `RamaLean/` builds against Mathlib with **no `sorry`**. Every
> mathematical theorem depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
> `Quot.sound`). `native_decide`, which additionally uses `Lean.ofReduceBool`, appears only where the
> kernel provably cannot evaluate: Paper 1's partition *values* (the `Decidable` instance for
> `Fintype.card (Nat.Partition n)` does not reduce) and bounded checks in the superseded merged Paper 2.
> In Paper 1 the inferences drawn from those values are separated out and kernel-checked, so nothing
> mathematical rests on the compiled step. **Papers 2a and 2b cite no declaration that uses
> `native_decide`**: every Lean name they reference depends on the three standard axioms or a strict
> subset, so their formal surface is entirely kernel-checked.

## Papers

### Paper 2a — Roots of $d$-matching polynomials and the spectrum of the universal cover
`paper2a_note/` · [note.pdf](paper2a_note/note.pdf) · 22pp

Hall–Puder–Sawin place the roots of $\mu_{d,G}$ in $[-\rho,\rho]$. We conjectured they lie in
$\operatorname{spec}(T)$ itself — a proper subset whenever the universal cover has a spectral gap.

- **That conjecture is FALSE, and the counterexample is due to Chris Hall.** A simple connected
  bipartite graph on 41 vertices: five copies of $K_{2,5}$, a pendant leaf on one degree-five
  vertex of each, and a central vertex joined to the other five. Its matching polynomial is
  $x^{21}(x^4-11x^2+25)^4(x^2-5)(x^2-11)$, and $\sqrt5$ sits in an internal gap of
  $\operatorname{spec}(T)$, certified by an Angel–Friedman–Hoory ratio system with decay
  $0.9636<1$, exact in $\mathbb{Q}(\sqrt5,\sqrt{41})$. We verified his certificate independently
  and machine-checked its algebra. GAPCOUNT falls with it.
- **Proved** for every $G$ of first Betti number one and every $d$, by a closed form
  $\mu_{d,G}=V_d$ for $V_d=\mu_G V_{d-1}-\mu_{G-V(C)}^2V_{d-2}$. For the cycle this specializes to
  $\Phi_{n,r}=\chi_{C_n}U_{r-1}(T_n(x/2))$, equivalent to Hall's conjecture (first proved by
  Cochran–Groothuis–Herring–Rohatgi–Stucky, 2018), by an independent elementary route. **Formalized.**
- **Proved** for every subdivision at $d=1$, settling the case $\min(d,r)=2$ of Song–Fan–Miao.
- **The repair, and its threshold.** Minimum degree two fails (pendant cycles for Hall's leaves,
  92 vertices), bounded maximum degree fails, and 2-connectivity fails — so connectivity is a
  confound and the mechanism is a *separation*. **D3** (minimum degree $\ge3$) is the surviving
  hypothesis and three is the exact threshold. **Formalized** (`CutVertexMechanism`,
  `SeparationOrder`, `MinimumDegreeThreshold`, `GluedSearch`).
- D3 is a **conjecture**. It survives 806 cut-based configurations built to Hall's own mechanism,
  419 graphs with no separator at all, and 39 with a separating pair — all on an instrument whose
  correctness is itself formalized (`SpectralAtom`).

### Paper 2b — The biregular case: the weighted plane class and its obstructions
`paper2b_note/` · [note.pdf](paper2b_note/note.pdf) · 60pp

The biregular case survives the refutation and contains Problem 1 of Song–Fan–Miao. At $b=2$ the
object is the *weighted plane class*: families $\{(c_k,V_k)\}$ with $\sum_k c_kP_{V_k}\preceq aI$,
whose matching polynomial is the Marcus–Spielman–Srivastava mixed characteristic polynomial.

- **Proved** for every complete bipartite $K_{d,q}$: the margin is $\sqrt{d-1}-h_d/2>0$ by
  Gershgorin on the Hermite Jacobi matrix, so no $K_{d,q}$ refutes the statement however wide its
  gap. **Formalized** (`CompleteBipartiteMargin`).
- **But the margin decays like $n^{-2/3}$**, the soft-edge exponent, over eight families with
  $R^2\ge0.999$. The statement is true but tight, and **no size-free bound can prove it** —
  which disqualifies the Gershgorin constant above as a route to the general case.
  **Formalized** (`SoftEdge`, `no_uniform_lower_bound`).
- An exact vertex recursion for the plane class, its cross-term decomposed into pieces $C_r$
  whose nonnegativity would give the band, and two unconditional bounds from real-rootedness.
- **The obstructions are the substance.** A rank-blind barrier reads Marchenko–Pastur and cannot
  reach the tree band at either edge; compressions cannot reach the inner end at all; the
  coefficient ladder's reach is unbounded in the moment order but an input at a uniform rate *is*
  the conclusion it would prove, so the dimension restriction is intrinsic
  (`MomentLadder.band_of_all_moments`); and the tree moment bound, the natural a priori input, is
  false off the coordinate case.
- A **ratio route** escapes these and settles the inner edge on a nontrivial class, closing for
  six of seven families tested; the $(3,6,5)$ defect is stated, not hidden.
- $\mu_G(2\sqrt{d-1})$ counts pseudo-forests, answering a question of Csikvári using his own
  machinery with Bencs. **Formalized** (`PseudoForest`, `EvenEval`).
- **Open:** the band itself, reduced to one sign $X_e\le0$.

> **Superseded.** `paper2_note/` is the single 68pp document these two were split from. It is kept
> for reference and for the DOI record; the split above is current. Nothing in it is retracted by
> the split, which is editorial.
### Paper 3 — The permanent of the GCD matrix
`paper3_note/` · [note.pdf](paper3_note/note.pdf)

$a(n)=\operatorname{per}[\gcd(i,j)]_{1\le i,j\le n}$ (OEIS [A085244](https://oeis.org/A085244)). Whereas
$\det[\gcd(i,j)]=\prod_{k\le n}\varphi(k)$ (Smith, 1876), the permanent's arithmetic appears unstudied.
- Congruences: $2\mid a(n)\ (n\ge3)$, $4\mid a(n)\ (n\ge4)$, $3\mid a(n)\ (n\ge13)$ — **formalized.**
- $v_2(a(n))\to\infty$ — **formalized.**
- Growth: $(a(n)/n!)^{1/n}\to\infty$, with $(\log n)^{\theta+o(1)}$, $2\ln\varphi-\varphi^{-2}\le\theta\le\log2$.
- The 2-adic deficit at the peaks $n=2^k+1$, through a mechanism: two exact valuation theorems for odd
  permanents give $D_{N_0}(2^k+1)=2k-4$ for the **weight-zero grade** $N_0$ whenever a computable
  "achiever parity" is odd. Transfer to $a$ itself needs $v_2(a)=v_2(N_0)$, verified only for $k\le5$.
- **Open:** whether that parity is odd infinitely often — a Selberg-type parity problem.

### Paper 4 — Coefficient stability of $d$-matching polynomials
`paper4_note/` · [note.pdf](paper4_note/note.pdf)

For $\mu_{d,G}$ (Hall–Puder–Sawin) and fixed $k$, $[x^{|V|d-2k}]\mu_{d,G}$ is a degree-$k$ polynomial in
$d$; explicit top coefficients in graph invariants (edges, 2-paths, claws, triangles). At $k=3$ the
constant term counts triangles, $c_3(0)=-\#\triangle(G)$; for $k\ge4$ it is a genuinely higher invariant,
**not** a simple count of $k$-edge cyclic subgraphs. **Formalized:** the coefficient extraction
(`Paper4Coeff`), the inclusion–exclusion for an arbitrary conflict relation (`ConflictIE`), and the
cover counts $M=|E|d$, $p_2=Pd$ (`CoverCounts`).

### Paper 1 — Integers $n$ with $n\mid p(n)-1$
`paper1_partition_self_divisibility.md` — a minor note. The sequence is OEIS
[A128836](https://oeis.org/A128836) (the shifts $S_0=\{n\mid p(n)\}$ and $S_{-1}=\{n\mid p(n)+1\}$ are
[A051177](https://oeis.org/A051177) and [A203023](https://oeis.org/A203023)); 13 terms to $10^6$;
elementary explanation of a Ramanujan-prime appearance. The value is the Lean formalization plus the
elementary explanation, not the sequence; carried as a case study in the methodology note.

### Methodology note — Machine-Verified Experimental Mathematics: Four Ramanujan-Style Case Studies
`methodology_note/` · [note.pdf](methodology_note/note.pdf)

The contribution is the pipeline, not any single theorem: computation → conjecture → Lean-4/Mathlib
proof, across the four notes, with a reusable formal permanent library and an honest account of failure
modes.

## Layout
- `RamaLean/` — the Lean 4 development (see `LEAN_README.md`); build with `lake build`.
- `code/` — Python / Rust / C engines and data (see `code/README.md`); includes exact $a(n)$ data and
  the `vperm` engine for $v_2(N_0(2^k+1))$ beyond Ryser.
- `paper*/`, `methodology_note/` — LaTeX sources and compiled PDFs.

## For a reviewer

The fastest route to checking this rather than reading it.

**Label conventions.** Every mathematical statement carries exactly one:

| Label | Meaning |
|---|---|
| VERIFIED | Formalized in Lean 4. `lake build` clean, zero `sorry`, axioms checked. |
| PROVED | Complete proof written out, not yet formalized. |
| HEURISTIC | Supported by computation only. |
| CONJECTURE | Believed, no proof. |
| FALSE | Counterexample in hand. |

A result is only as strong as the weakest label it depends on, and the notes say so where it
matters. Section headings and Lean file docstrings both carry the label of what they contain.

**Three checks, in increasing cost.**

1. `lake build` then `#print axioms` on any theorem. Nothing in `RamaLean/` contains a `sorry`;
   axioms should be `[propext, Classical.choice, Quot.sound]` throughout, and any file that needs
   more says so in its docstring.
2. `python3 code/lean_map.py` prints every Lean name the papers cite and where it lives, plus
   anything cited and missing. It should report no dangling names.
3. `python3 code/cite_check.py` re-runs every script the papers cite and diffs the output against
   the recorded snapshots in `code/snapshots/`. Long searches honour `--quick`, which shrinks
   their configuration, not their time budget, so a short run is a prefix of the same work and is
   reproducible. Sixteen scripts still exceed the checker's budget and are named by it rather than
   passed over.

**Dependencies.** Python 3.12 with `numpy`, `scipy`, `sympy`, `networkx`, `mpmath`. Lean 4 with
Mathlib, pinned by `lean-toolchain` and `lake-manifest.json`.

**What is not proved, and is the honest state of the main line.** Xu's Conjecture 1.4 is a theorem
on the commuting locus at every rank, and the constant there is attained; both are in Paper 2b.
Everything the conjecture still asserts lies off that locus. The commuting locus is a singular
point of the tight-projection variety, its tangent cone is an explicit intersection of quadrics,
and the curvature of the top root is negative there; whether the locus is extremal, which would
close the general conjecture, is a CONJECTURE and is labelled as one.

## Reproducing
- Lean: `lake build` (needs Lean 4 + a Mathlib cache; see `LEAN_README.md`).
- Data: the Python in `code/` is self-contained (`python3 code/paper3_gcd_permanent.py`, etc.).

## Citing
Archived on Zenodo. Cite the concept DOI
[10.5281/zenodo.21433867](https://doi.org/10.5281/zenodo.21433867), which always resolves to the newest
release. The current release is **v2.0** (2026-08-01),
[10.5281/zenodo.21739117](https://doi.org/10.5281/zenodo.21739117). Machine-readable metadata is in
[`CITATION.cff`](CITATION.cff).

## License
Dual-licensed — code (Apache-2.0), papers (CC-BY-4.0). See [`LICENSING.md`](LICENSING.md).
