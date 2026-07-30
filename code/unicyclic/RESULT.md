# d-matching polynomials of unicyclic graphs

Answer to the question raised by D. Puder (25 Jul 2026): does the exponential-formula / Chebyshev
derivation of the cycle case say anything beyond cycles?

It extends to exactly the graphs of first Betti number 1, and the boundary is sharp.

## What the cycle proof actually uses

Not "cycle-ness". Three facts, in order:

1. after gauge-fixing a spanning tree, the r-lift is determined by a *single* permutation
   `sigma` in `S_r` — this needs `|E| - |V| + 1 = 1`, i.e. exactly one non-tree edge;
2. the gauge-fixed lift decomposes into connected components indexed by the cycles of `sigma`,
   the component of an `l`-cycle being the `l`-fold cyclic cover `G_l`;
3. `chi(G_l)` is a Chebyshev-type function of `l`, so the exponential formula sums in closed form.

Only (1) is special to cycles among the three, and it holds for every unicyclic graph
(one cycle, trees attached).

## Statement

Let `G` be connected with first Betti number 1 and let `e` be its unique non-tree edge. Put

    chi^+ = char poly of G,        chi^- = char poly of G with e weighted -1,
    A = (chi^+ + chi^-)/2,         B = (chi^+ - chi^-)/4.

These are the coefficients of the twisted characteristic polynomial
`det(xI - A_G(z)) = A(x) + B(x)(z + 1/z)`, recovered by evaluating at `z = +1, -1`.
Define

    V_0 = 1,   V_1 = A,   V_d = A*V_{d-1} - B^2*V_{d-2}.

Then

    (i)   mu_{d,G} = V_d                                    (d-matching polynomial)
    (ii)  mu_{d,G}(x) = prod_{k=1..d} det(xI - A_G(e^{i k pi/(d+1)}))
    (iii) E[char poly of a uniformly random r-lift] = chi^+ * V_{r-1}

(ii) follows from (i) by `U_d(y) = 2^d prod_k (y - cos(k pi/(d+1)))` with `y = -A/(2B)`.

Cycle case: `A = 2T_m(x/2)`, `B = -1`, so `V_d = U_d(T_m(x/2))`, recovering Hall's conjecture for
cycles (Cochran-Groothuis-Herring-Rohatgi-Stucky 2018) as the case `B = -1`.

## Corollary (real-rootedness, two lines)

Each factor in (ii) is the characteristic polynomial of `A_G(z)` at `|z| = 1`, a Hermitian matrix,
hence real-rooted. So `mu_{d,G}` is a product of `d` real-rooted polynomials and its roots are
exactly the eigenvalues of the twisted adjacency matrices at the angles `k pi/(d+1)`.
This is the Hall-Puder-Sawin real-rootedness theorem for this family, with an explicit description
of the roots.

## Proof status

Proof in hand, not yet written out carefully or formalized. The ingredients are classical:
gauge fixing; the Fourier decomposition `chi(G_l) = prod_j F(x, omega^j)` of a cyclic cover; the
exponential formula for `S_r` averages. Generating function computation:

    sum_r Phi_r z^r = exp( sum_l chi(G_l) z^l / l ) = (1-w)^2 / (1 - 2yw + w^2),   w = -Bz,

and extracting coefficients gives (iii). The work remaining is writing it properly.

## Verification (code/unicyclic, exact integer arithmetic, Rust)

| test | result |
|---|---|
| gauge fixing: full brute force over all edges vs one permutation | MATCH, 6 graphs, r = 2,3 |
| (iii) vs brute-forced lift average | OK on 13 named unicyclic graphs, r = 1..6 |
| (i) vs the *definition* of `mu_d` (average matching polynomial over all d-covers) | OK, 6 graphs, d = 1,2 |
| random sweep, seeded | 34/34 unicyclic graphs, r up to 5 |
| **negative control**: first Betti number >= 2 | **FAILS** for theta, bowtie, K_4, K_{2,3}, two triangles + bridge, at every r >= 2 |

The negative control is the informative one: the formula is not merely unverified for Betti >= 2,
it is false there, so Betti number 1 is exactly the reach of the method, not an artefact of what
was tested.

Examples of the pair `(A, B)`:

| G | A(x) | B(x) |
|---|---|---|
| `C_3` | `x^3 - 3x` | `-1` |
| `C_5` | `x^5 - 5x^3 + 5x` | `-1` |
| tadpole `T(3,1)` | `x^4 - 4x^2 + 1` | `-x` |
| `C_3` + 2 pendants | `x^5 - 5x^3 + 3x` | `-x^2` |
| `C_3` + path `P_2` | `x^5 - 5x^3 + 4x` | `-x^2 + 1` |
| `C_4` + path `P_3` | `x^7 - 7x^5 + 13x^3 - 6x` | `-x^3 + 2x` |

`B = -1` exactly for the cycles; for a general unicyclic graph `B` carries the trees.

## Novelty

Preliminary and shallow: two searches and one paper fetched. No closed form or recurrence for
d-matching polynomials of unicyclic graphs was found. The nearest hit, "Higher order matching
polynomials and d-orthogonality" (arXiv:0909.1655), covers paths, cycles, complete and complete
bipartite graphs by sign-reversing involutions, with no overlap in method or family. Worth
checking "Multivariate matching polynomials of cyclically labelled graphs" (Discrete Math 2009)
before making any claim.

## Why it stops at Betti number 1 (verified, `src/bin/betti2.rs`)

For Betti number `b` the lift is an action of the free group `F_b` on `[r]`, and its components are
the orbits. The exponential formula therefore survives for every `b`, in the form

    N_r = sum_{l=1..r} binomial(r-1, l-1) * C_l * N_{r-l},
    N_r = (r!)^b * Phi_r,      C_l = sum over TRANSITIVE b-tuples on [l] of chi(connected cover).

Verified to hold for `b = 1, 2, 3` (tadpole, theta, bowtie, `K_4`). What dies at `b >= 2` is the
atom, not the formula:

| graph | b | distinct char polys among connected `l`-covers, `l = 1,2,3,4` |
|---|---|---|
| tadpole `T(3,1)` | 1 | 1, 1, 1, 1 |
| theta | 2 | 1, 2, 5, 14 |
| bowtie | 2 | 1, 2, 4, 10 |
| `K_4` | 3 | 1, 2, 8 |

For `b = 1` every transitive tuple gives the *same* cover `G_l`, so `C_l = (l-1)! chi(G_l)`: one
graph per `l`, with `chi(G_l)` Chebyshev in `l`. That single fact is what closes the generating
function. For `b >= 2` the transitive tuples number `(l-1)!` times the count of index-`l` subgroups
of `F_b` (for `b = 2`: 1, 3, 13, 71, matching the computed 1, 3, 26, 426 tuples), and they spread
over many non-isomorphic covers with distinct spectra, so `C_l` is an unstructured sum.

## Formalization

`RamaLean/Paper2Unicyclic.lean` formalizes the algebra of the recurrence over a commutative ring:
`cV_homogeneous` (homogeneity in `(A,B)`), `cV_neg_right` (dependence on `B` only through `B^2`),
`cV_cycle` (the specialization `A = 2Y`, `B = -1` gives the Chebyshev `U_d`, i.e. the cycle case),
and `cV_eq_cheb` (over a field with `B` invertible, `cV A B d = (-B)^d U_d(-A/(2B))`). Builds with
no `sorry`; axioms are `[propext, Quot.sound]` for the first three and additionally
`Classical.choice` for the field statement. The graph-theoretic input is not formalized.

## Honest limitation

This does not show that cycles illuminate the general d-matching polynomial. It shows the method's
reach is exactly Betti number 1, and no further — now with the mechanism of the failure identified
rather than merely observed. Betti number 1 is still a thin class.
