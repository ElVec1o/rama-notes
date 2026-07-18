# code/ — computation scripts and outputs (July 2, 2026 enhancement sessions)

All computations are exact (integer/rational arithmetic) unless noted.

## Paper 1 — partition self-divisibility
- `paper1_extend_sequences.py` → `paper1_output_n200000.txt` — S₁/S₀/S₋₁ to 2×10⁵ (round 1)
- `paper1_million.py` → `paper1_output_n1000000.txt` — N = 10⁶ with control
  residue classes (0, ±1, ±2, ±3, +5) + uniformity histogram (round 2)

## Paper 3 — gcd permanent
- `paper3_gcd_permanent.py` → `paper3_output_n23.txt` — a(n) to n = 23,
  parity theorem check, factorizations (round 1)
- `paper3_extend27.py` → `paper3_output_n27.txt` — a(24)..a(27) + growth
  analysis (round 2)

## Paper 4 — K₄ lifts
- `paper4_exact_k4_lifts.py` → `paper4_output_exact_r2to5.txt` — exact
  Ψ_r, r = 2..5 (Bareiss + interpolation + conjugacy reduction; round 1;
  found the June Ψ₂/Ψ₃ errors)
- `paper4_verify_independent.py` — independent SymPy cross-check of the
  pipeline and of Ψ₂ = x⁴−6x²+3
- `paper4_r6.py` → `paper4_output_r6.txt` — exact Ψ₆ (faster orbit
  machinery; validates itself by recomputing Ψ₃ first; round 2)
- `paper4_ramanujan_exact.py` → `paper4_output_ramanujan_exact.txt` —
  EXACT Ramanujan-lift counts r = 2..5 via Sturm chains at u = 8
  (found all four June float counts wrong; round 2)

## Round 3 additions
- `pentagonal_mod.c` → `pentagonal_mod` — C+GMP p(n) mod n scanner
  (validated bin-for-bin against the Python 10⁶ run; 18× faster).
  Outputs: `pent_1e6_validate.txt`, `pent_4e6.txt`.
  ⚠️ **The N = 10⁷ run was killed at ~8.7 GB RSS.** Memory for the
  full-value pentagonal recurrence is Θ(N^{3/2}) bits ≈ 11–12 GB at 10⁷ —
  inherent, not a bug: every p(m) is re-used up to step m + g_max, so no
  value can be freed, and a *modular* rewrite cannot work because the
  target p(n) mod n has a different modulus for every n (a fixed-modulus
  run only yields p(n) mod M; covering all n ≤ N with prime-power runs
  costs ~ψ(N) ≈ N modulus-bits, ~10³× more arithmetic). To do 10⁷: run
  this binary on an otherwise-idle machine with ≥ 13 GB free, or switch
  to per-value Hardy–Ramanujan–Rademacher (FLINT `arith_number_of_partitions`).
- `paper3_numpy_ryser.py` → `paper3_output_n30.txt` — a(28), a(29), a(30)
  via block-vectorized modular Ryser + CRT (8×30-bit primes; validated
  at n = 15, 20, 23).
- `paper4_avgpm.py` — exact E[#PM of d-cover of K₄] formula: verification
  + growth-rate computation (rate → 16/9, refuting the √3 guess).
- `paper4_ramanujan_r6.py` → `paper4_output_ramanujan_r6.txt` — exact
  r = 6 Ramanujan count (270504000).

## Round 4 (three open questions)
- `verify_mod3_theorem.py` — verifies Paper 3 Theorem 3's engine: the
  permanent column-collision lemma (0/2000 random matrices) and the
  type-A threshold n ≥ 13. (Answers "is 3 | a(n) for n ≥ 13" — yes, proven.)

## Notes
- `_orbits/` holds pickled conjugacy-orbit data (regenerable; safe to delete).
- The Lean formalization lives in `../RamaLean/` (see ../LEAN_README.md).

## Round 6 (moonshot: papers 3 & 4 game-changers)
- `k4_recurrence_search.py` — proves K4 has NO C-finite (cycle-like) recurrence
  in d for its d-matching polynomials (negative result).
- `k4_coefficient_stability.py` — coefficient stability: [x^{4d-2k}]mu_d is a
  degree-k polynomial in d, lead 6^k/k!; c_1,c_2 proven, E[#triangles]=4.
- `growth_bounds.py` — Paper 3 Prop 3: rigorous liminf (a(n)/n!)^{1/n} >= e^L
  = 1.768; row-sum upper bound diverges, so finiteness of c is OPEN.

## Round 7 (general coefficient-stability theorem)
- `cycle_coefficient_stability.py` — verifies coeff stability on the infinite
  cycle family via exact mu_{d,C_n}=U_d(T_n(x/2)): deg_d(c_k)=k, lead |E|^k/k!.
- `general_coefficient_formulas.py` — explicit universal formulas c_1=|E|d,
  c_2=C(|E|d,2)-P*d (P=#2-paths), c_3 const=-#triangles; verified C_3..C_6 + K4.

## Round 8 (completing the coefficient theory)
- (in general_coefficient_formulas / this round) PROVEN general c_3 formula:
  c_3 = C(Ed,3) - P d(Ed-2) + (W+2S)d - t  (P=#2-paths, S=#claws,
  W=sum_edges(du-1)(dv-1), t=#triangles); verified C_3..C_6, K4, diamond.
- `diamond_dmatching.py` — d-matching polys of the diamond (K4-e) via lifts
  to the 6-cover (orbit-BFS reduction; NOTE Psi_r = mu_{r-1} off-by-one);
  confirms c_1,c_2,c_3 general formulas on a 3rd graph (S,P,W,t all nonzero).
- growth_bounds.py (block bound) — a naive sub-permutation lower bound gives
  0.81, WORSE than Jensen 1.768: recorded as a failed improvement.

## Round 9 (A': subleading coeff proven; B: standalone note)
- (verification in cycle_coefficient_stability / this round) PROVEN universal
  subleading coeff: [d^{k-1}] c_k = -(|E|^{k-2}/(k-2)!)(|E|/2 + P); verified
  k=2..5 on cycles, K4, diamond (E != P).
- ../paper4_note/note.tex -> note.pdf : standalone note "Coefficient stability
  of d-matching polynomials" (general theorem + explicit c_1,c_2,c_3 + top-two
  coeffs + topological constant term + K4 no-C-finite contrast).

## Round 10 (D: topological constant term)
- `topological_constant.py` — computes c_k(0) directly by matching-counting
  over covers. PROVES c_3(0)=-t (verified 6+ graphs). REFUTES simple c_4(0)
  formulas: c_4(0)=6,1,21,20,12,8 for C_3,C_4,diamond,bowtie,2-disj-tri,paw
  — depends on triangle overlaps & pendant edges (no simple (t,#C4) form).

## Round 11 (C: growth rate RESOLVED)
- `growth_rate_resolution.py` — Van der Waerden + Sinkhorn: rigorous per-n
  lower bound on (a(n)/n!)^{1/n} DIVERGES (exponent -> log 2). => c = infinity,
  rate (log n)^{log 2}; data fits to <1%. Resolves Paper 3's open question
  (overturns the earlier finite-constant guess).

## Round 12 (C': rigorous upper bound + c=infinity reduction)
- (in growth_rate_resolution.py, extended) RIGOROUS elementary upper bound:
  (a(n)/n!)^{1/n} <= e*exp((1/n)sum log f(i)), (1/n)sum log f(i) = log2*loglog n
  + O(1) via Mertens => (a(n)/n!)^{1/n} = O((log n)^{log2}). PROVEN.
  c=infinity reduced to scaling lemma prod(x_i y_i R_i)=e^{O(n)} (verified ~1.05).
  Clean recursion b(n) >= b(floor(n/p)) proven.

## Round 14 (C'': self-contained entropy lower bound)
- (verified in entropy-bound check) RIGOROUS self-contained lower bound:
  a(n)/n! >= (1/n^n) exp(sum w_ij log gcd + H(w)) for ANY doubly stochastic w
  (weighted AM-GM + Gurvits/VdW). Reduces c=infinity to: exhibit w_n with
  F(w_n)/n - log n -> infinity. Uniform w -> Jensen const 0.570; optimal
  (Sinkhorn) w -> diverges (0.81,1.03,1.22 at n=30,100,400). paper3_note Lemma.

## Round 15 (F: 3|a(n) machine-checked end-to-end)
- RamaLean/Paper3Congruence.lean: three_dvd_gcd_permanent proves 3|a(n) for
  n>=13 over ZMod 3 (permanent of gcd matrix = 0), standard axioms only, no
  sorry/native_decide. 3-cycle through cols 1,7,13 + Lemma A. Full Theorem 3.

## Round 16 (C''' prime-decomposition; A''' cycle c_4)
- growth_prime_decomposition.py: c=inf reduced to single-prime problems --
  a(n)>=perm(gcd_P) (monotone), entropy rate ADDITIVE over primes (~log2/p each),
  sum diverges (Mertens). Transparent route to unconditional c=inf.
- A''': exact c_4(C_n,d)=n^4/24 d^4 -3n^3/4 d^3 +107n^2/24 d^2 -35n/4 d (n>=5);
  confirms top-two universal, [d^2]/[d^1] graph-specific.

## Round 18 (C5 unconditional c_inf=infinity; 2-adic; Cleanup)
- growth_c5_construction.py: divisibility-block doubly-stochastic construction;
  c_inf=infinity UNCONDITIONAL. Verified rate=sum g_p numerically.
- Cleanup: p g_p = Psi(y)+O(1/p), liminf p g_p >= 2 ln phi - phi^-2 rigorous.
- 2-adic: v2(a(n))~v2(n!)~n (not v2(det)); linear bound open.

## Round 20 (cross-prime theta; 2-adic; v2 dips)
- ryser_mod2.c: a(n) mod 2^64 via Gray-code Ryser (uint64 auto-mod), reaches n=32.
  v2(a(n))-v2(n!): powers of 2 give +1,-3,-5,-5 at n=4,8,16,32 -> PLATEAU (bounded).
- theta (capacity exponent): Sinkhorn on gcd matrix n<=3000. (log2-theta_n) ~0.026
  flat; pre-asymptotic (loglog n~2); theta in [0.5805,log2] but exact value open.
- 2-adic v2>=cn: Smith expansion a(n)=sum prod phi(d_i) perm[d_i|j]; open.
