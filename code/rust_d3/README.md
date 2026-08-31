# d3sweep — can Hall's construction be run at minimum degree three?

If it can, Conjecture D3 is false. A centre joined to `p` copies of a block `B` at a root vertex
`r`, with the block chosen so every vertex of the assembled graph has degree at least three.

    cd code/rust_d3 && cargo run --release -- --selftest    # run this first
    cd code/rust_d3 && cargo run --release

Reads `blocks.json` (1340 block/root pairs on 4..7 vertices from the graph atlas), writes
`results.txt` for candidates and `checkpoint.txt` continuously, so a killed run keeps its results.

## The test is resolution-free

An earlier version scanned for band gaps on a grid and then asked whether a root fell inside one.
That is the wrong shape: at step 0.02 it cannot see a gap narrower than about 0.04, and the gaps
holding the five known counterexamples are 0.030, 0.002, 0.018, 0.026 and 0.038 wide, so it would
have missed a violation of exactly the kind that is known to occur. Refining the grid to 0.001
would have cost about twenty times more and still had a resolution.

There is no need for a grid. **Every root of `mu_G` is a root of `A` or of the bracket**, since
`mu_G = A^{p-1}(xA - p·B_r)`, and both have degree at most 8. So the roots can be found directly
and each classified *at the root itself*, by how `|Im sum_w G_w|` scales in `eta`. No gap can be
missed however narrow, because nothing is being scanned for.

Roots of `A` are skipped on principle, not by measurement: the branch union is a θ-Aomoto subset
whenever `p > 1`, so by Banks–Garza-Vargas–Mukherjee they are eigenvalues of the cover and lie in
`spec(T)`. Only bracket roots can be violations.

## Validation

`--selftest` must pass before any sweep result means anything. It checks Sturm root isolation
against three polynomials with known roots (including the n=36 counterexample's minimal
polynomial, verified against sympy), the classifier against three W_6 roots and one K_4 point that
must all read "band", and `mu(K_4) = x^4 - 6x^2 + 3`.

The method itself was validated in Python beforehand: called at the root, the classifier returns
"outside spec" for all five known counterexamples, and "in a band" for all fourteen wheel roots of
W_6, W_9 and W_12, with no false candidates.

## Result

    8208 cases, 59s, 0 candidates.  D3 survives this sweep.

against the 118 + 350 configurations of the published searches. Arithmetic is exact where it
decides anything: integer polynomials, Sturm sequences over the integers, no floating-point root
finding. The classification of a root as band or gap is numerical, and is the one place a wrong
answer could hide; the controls above are what stand behind it.
