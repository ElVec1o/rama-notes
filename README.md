# RAMA-NOTEBOOK

Four short number-theory / combinatorics notes and a methodology note, each pairing a computational
result with a Lean 4 + Mathlib formalization. Everything here builds and is machine-checked; conjectures
are labeled as such.

> **Formalization status:** the Lean library `RamaLean/` builds against Mathlib with **no `sorry`**. The
> genuine mathematical theorems depend only on Lean's three standard axioms (`propext`, `Classical.choice`,
> `Quot.sound`); the `native_decide` computational checks (Paper 1, and Paper 2's `thm1_verified` /
> `cor2_fibLucas`) additionally use `Lean.ofReduceBool`. Paper 4 has no dedicated Lean file — its formal
> backing is the shared Paper 2 matching-polynomial identities.

## Papers

### Paper 2 — The expected characteristic polynomial of a random lift of a cycle
`paper2_note/` · [note.pdf](paper2_note/note.pdf)

For the expected characteristic polynomial of a uniformly random permutation $r$-lift of $C_n$,
$$\Phi_{n,r}(x)=\chi_{C_n}(x)\,U_{r-1}\!\big(T_n(x/2)\big),\qquad \chi_{C_n}(x)=2T_n(x/2)-2,$$
equivalently the $d$-matching polynomial of $C_n$ is $U_d(T_n(x/2))$. This is an independent proof of a
conjecture of Hall (first proved by Cochran–Groothuis–Herring–Rohatgi–Stucky, 2018), via the
exponential formula and a Chebyshev generating function. **Fully formalized in Lean.**

### Paper 3 — The permanent of the GCD matrix
`paper3_note/` · [note.pdf](paper3_note/note.pdf)

$a(n)=\operatorname{per}[\gcd(i,j)]_{1\le i,j\le n}$ (OEIS [A085244](https://oeis.org/A085244)). Whereas
$\det[\gcd(i,j)]=\prod_{k\le n}\varphi(k)$ (Smith, 1876), the permanent's arithmetic appears unstudied.
- Congruences: $2\mid a(n)\ (n\ge3)$, $4\mid a(n)\ (n\ge4)$, $3\mid a(n)\ (n\ge13)$ — **formalized.**
- $v_2(a(n))\to\infty$ — **formalized.**
- Growth: $(a(n)/n!)^{1/n}\to\infty$, with $(\log n)^{\theta+o(1)}$, $2\ln\varphi-\varphi^{-2}\le\theta\le\log2$.
- **Open:** whether the 2-adic deficit $v_2(n!)-v_2(a(n))$ is unbounded — a Selberg-type parity problem.

### Paper 4 — Coefficient stability of $d$-matching polynomials
`paper4_note/` · [note.pdf](paper4_note/note.pdf)

For $\mu_{d,G}$ (Hall–Puder–Sawin) and fixed $k$, $[x^{|V|d-2k}]\mu_{d,G}$ is a degree-$k$ polynomial in
$d$; explicit top coefficients in graph invariants (edges, 2-paths, claws, triangles), with
$c_k(0)=$ signed count of $k$-edge cyclic subgraphs ($c_3(0)=-\#\triangle(G)$).

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

## License
Dual-licensed — code (Apache-2.0), papers (CC-BY-4.0). See [`LICENSING.md`](LICENSING.md). Cite via
[`CITATION.cff`](CITATION.cff).
