# RAMA-NOTEBOOK

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21433867.svg)](https://doi.org/10.5281/zenodo.21433867)

Four short number-theory / combinatorics notes and a methodology note, each pairing a computational
result with a Lean 4 + Mathlib formalization. Everything here builds and is machine-checked; conjectures
are labeled as such.

> **Formalization status:** the Lean library `RamaLean/` builds against Mathlib with **no `sorry`**. Every
> mathematical theorem depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
> `Quot.sound`). `native_decide`, which additionally uses `Lean.ofReduceBool`, appears only where the
> kernel provably cannot evaluate: Paper 1's partition *values* (the `Decidable` instance for
> `Fintype.card (Nat.Partition n)` does not reduce) and two bounded checks in Paper 2. In Paper 1 the
> inferences drawn from those values are separated out and kernel-checked, so nothing mathematical rests
> on the compiled step.

## Papers

### Paper 2 — Roots of $d$-matching polynomials and the spectrum of the universal cover
`paper2_note/` · [note.pdf](paper2_note/note.pdf) · 40pp

Hall–Puder–Sawin place the roots of $\mu_{d,G}$ in the interval $[-\rho,\rho]$. We conjecture they lie in
$\operatorname{spec}(T)$ itself — a proper subset whenever the universal cover has a spectral gap — which
is the matching-polynomial form of their Question 6.3 and contains Problem 1 of Song–Fan–Miao.
- **Proved** for every $G$ of first Betti number one and every $d$, by a closed form
  $\mu_{d,G}=V_d$ for $V_d=\mu_G V_{d-1}-\mu_{G-V(C)}^2V_{d-2}$. For the cycle this specializes to
  $\Phi_{n,r}=\chi_{C_n}U_{r-1}(T_n(x/2))$, equivalent to Hall's conjecture (first proved by
  Cochran–Groothuis–Herring–Rohatgi–Stucky, 2018), by an independent elementary route. **Formalized.**
- **Proved** for every subdivision at $d=1$, settling the case $\min(d,r)=2$ of Song–Fan–Miao.
- A vertex recursion for weighted 2-plane families valid in *every* direction, whose cavity term is a
  sum of squares; in Gram coordinates it is the matching determinant lemma. **Formalized.**
- The leading cross term is a perfect square, hence $\ge 0$ — **formalized with no hypotheses.**
- The band is the support of a free convolution *power*; the cavity ratio at the threshold is exactly
  $1+1/(1+\sqrt a)$ (Kesten–McKay). **Formalized.**
- **Open:** the band itself, reduced to one sign $X_e\le0$, and the sharper Conjecture on the ratio.

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
