# (3,4)-biregular search, exact

Conjecture 10 asks whether every zero of the matching polynomial mu_G lies in spec(T_G), T_G the
universal cover. It is false in general (Hall). Conjecture D3 asks whether minimum degree three
repairs it, and is open.

`RamaLean/DegreeBound.lean` proves that a theta-Aomoto subset with theta != 0 forces
Delta > 2(delta - 1). So for a graph with degrees in {3,4} the universal cover has NO nonzero
point spectrum, and the mechanism that invalidated every previous attack in this repository is
provably unavailable. In that class a root of mu_G outside the BANDS of spec(T_G) is a genuine
counterexample, with no Aomoto escape.

Random graphs with degrees in {3,4} turn out to have no spectral gap near the origin at all, so
there is nowhere for a root to go. The exception is the biregular case: for a (3,4)-biregular
graph the universal cover is the (3,4)-biregular tree, whose spectrum is known in closed form,

    spec = {0}  union  +-[ sqrt3 - sqrt2 , sqrt3 + sqrt2 ]  =  {0} union +-[0.3178.., 3.1462..].

So the target is exact and needs no spectral computation at all. The complement of spec has TWO
windows and both are tested: (0, sqrt3 - sqrt2) and (sqrt3 + sqrt2, infinity). The upper one is
not empty a priori, since Heilmann-Lieb only gives |x| < 2 sqrt3 = 3.4641 > 3.1462. A root of
mu_G in either window is a counterexample to D3, and to Conjecture 10, in the trap-free class.

RESULT: 82896 graphs tested, 0 hits, 0 consistency failures. Exhaustive at t = 1 and t = 2 (all
2895 connected labelled graphs on 14 vertices), 20000 random graphs at each of t = 3..6, n <= 42.
The run ended because the t range was exhausted, not the time budget. The verdicts are exact; the
coverage is a sample. See data/biregular_sweep_result.json.

## Why this is resolution-free

Nothing here uses floating point in the verdict.

* mu_G is computed exactly. For a bipartite graph the matching counts m_k come from a DP over
  subsets of the smaller side, in integer arithmetic.
* mu_G = x^(n-2nu) * Q(x^2) with Q of degree nu and all roots real and strictly positive
  (Heilmann-Lieb). Counting roots of mu_G in (0, r) is counting roots of Q in (0, r^2).
* Because Q is hyperbolic with positive roots, the Budan-Fourier count is exact, not an upper
  bound with an even defect. The number of roots of Q in (0, R] equals deg Q - V(R), where V(R)
  is the number of sign variations in Q, Q', Q'', ... at R.
* R is the rational (3178/10000)^2, a strict under-estimate of (sqrt3 - sqrt2)^2, and every sign
  is computed in exact big-integer arithmetic. A reported root really is inside the gap.

V(0) = deg Q for a polynomial with all roots positive, and this is asserted on every graph as an
internal consistency check on the DP.

## Coverage

* t = 1, 2: exhaustive over labelled graphs, with the B side generated in non-decreasing subset
  order, which quotients out the B-relabelling only. This is a superset of the isomorphism classes,
  so the coverage claim is honest.
* t >= 3: random sampling.

n = 7t, with the 3t vertices of degree 4 and the 4t vertices of degree 3.

## Run

    cargo run --release -- --selftest
    cargo run --release

Progress, ETA and an interim checkpoint go to `checkpoint.txt`; hits go to `hits.json`.
