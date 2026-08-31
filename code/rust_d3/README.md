# d3sweep — can Hall's construction be run at minimum degree three?

If it can, Conjecture D3 is false. A centre joined to `p` copies of a block `B` at a root vertex
`r`, with the block chosen so every vertex of the assembled graph has degree at least three: every
vertex of `B` except `r` has degree ≥ 3 inside `B`, and `r` has degree ≥ 2, gaining its third from
the centre.

    cd code/rust_d3 && cargo run --release

Reads `blocks.json` (1340 block/root pairs on 4..7 vertices, emitted from the graph atlas), writes
`results.txt` for candidates and `checkpoint.txt` continuously, so a killed run keeps its results.

## Why the arithmetic stays small

`μ_G = A^{p-1}(xA - p·B_r)` with `A = μ_B` and `B_r = μ_{B-r}`, so **every root of `μ_G` is a root
of `A` or of the bracket**, both of degree at most 8. No polynomial of the assembled graph is ever
built. An earlier version computed `μ` of the 46-vertex graph by naive deletion recursion and hung;
that is what the rooted formula is for.

Roots are counted by **Sturm sequences over the integers**, not by floating-point root finding.
Roots of `A` are skipped: the branch union is a θ-Aomoto subset whenever `p > 1`, so by
Banks–Garza-Vargas–Mukherjee they are eigenvalues of the cover and lie in `spec(T)` by construction.
Only bracket roots can be violations.

## Result

    5528 cases, 591s, 0 candidates.  D3 survives this sweep.

against the 118 + 350 configurations of the published searches.

## The limitation, which is real

The band structure is found by a cavity scan at step **0.02**, and that cannot resolve a gap
narrower than about 0.04. The gaps holding the five known counterexamples are 0.030, 0.002, 0.018,
0.026 and 0.038 wide (`code/gapwidth_underreport.py`, `code/gapscale2.py`), so **this sweep would
miss a violation sitting in a gap of the size where violations are known to occur.** A conclusive
sweep needs a step of about 0.001, costing roughly twenty times more, which is around three hours
here. The result below is therefore evidence, not a proof, and weaker evidence than its scale
suggests.
