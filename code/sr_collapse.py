"""sr_collapse.py -- what hypothesis (ii) actually forces.

Three structure results, each PROVED in the docstring and then verified.

--------------------------------------------------------------------------
LEMMA 0 (restatement of (ii)).  Let the law of s be SR with pgf G of degree
<= b in each z_k, and let nu be its POLARISATION: the multiaffine SR measure
on n = qb slots, exchangeable inside each block B_k, with s_k = |S cap B_k|.
Then
        s_k ~ Bin(b,1/a) for every k   <==>   for every k the b indicator
        variables (X_i)_{i in B_k} are JOINTLY INDEPENDENT Bernoulli(1/a).

Proof.  (<=) is clear.  (=>) For an SR measure, |S cap B| is a sum of b
independent Bernoullis (Feder-Mihail / Borcea-Branden-Liggett), so its pgf
factors as prod_i (1 - t_i + t_i z); equality with ((a-1+z)/a)^b forces
t_1 = ... = t_b = 1/a because factorisation of a real polynomial into linear
factors is unique.  Hence E[C(s_k,m)] = C(b,m) a^{-m} for all m <= b, and by
block exchangeability E[C(s_k,m)] = C(b,m) E[X_{i_1}...X_{i_m}], so every
joint moment of the indicators inside a block equals a^{-m}.  For 0/1 random
variables the joint law is determined by these moments, and the product law
Bernoulli(1/a)^{otimes b} realises them.  QED

So (ii) says exactly: "inside each block, the slots are exactly independent
fair-1/a coins".  This is a rigidity statement, not a moment statement.

--------------------------------------------------------------------------
THEOREM 1 (the determinantal route is CLOSED -- route (a) of the plan cannot
produce a counterexample).  Let S ~ DPP(K) with K Hermitian, 0 <= K <= I, on
n = qb slots, and suppose (i) |S| = p a.s. and (ii) s_k ~ Bin(b,1/a).  Then K
is an orthogonal projection of rank p whose k-th diagonal b x b block is
(1/a) I_b; consequently, writing K = U^*U with U (p x n), UU^* = I_p, the
matrices  P_k := a U_k U_k^*  are rank-b orthogonal projections on C^p with
sum_k P_k = a I_p, and the law of s is EXACTLY the law of that projection
family.  I.e. every determinantal law satisfying (i)+(ii) is of matrix origin.

Proof.  |S| is a sum of independent Bernoulli(eigenvalues of K), so |S| = p
a.s. forces every eigenvalue into {0,1} and rank K = p: K is a rank-p
orthogonal projection.  s_k = |S cap B_k| is a sum of independent Bernoullis
with parameters the eigenvalues of the compression K[B_k,B_k]; by Lemma 0
those are all 1/a, and K[B_k,B_k] is Hermitian, so K[B_k,B_k] = (1/a) I_b.
Factor K = U^*U with U p x n and UU^* = I_p (possible exactly because K is a
rank-p projection).  Then U_k^*U_k = K[B_k,B_k] = (1/a)I_b, so (sqrt a U_k)
has orthonormal columns and P_k = a U_kU_k^* is a rank-b orthogonal
projection, and sum_k P_k = a UU^* = a I_p.  Finally DPP(K) = DPP(U^*U) is
the Naimark law of that family, so the two laws of s agree.  QED

--------------------------------------------------------------------------
THEOREM 2 (the "independent balls in bins" route is CLOSED).  Products of
linear forms are the other canonical source of real stable homogeneous
polynomials:  G(z) = prod_{r=1}^p ( sum_k c_{rk} z_k ),  c_{rk} >= 0,
sum_k c_{rk} = 1.  This is the law of p independent balls, ball r landing in
bin k with probability c_{rk}, and s_k = #balls in bin k.  Then (i) holds
automatically, and
        (ii) holds  <==>  c = (1/a) M with M a 0/1 matrix with all row sums
        a and all column sums b, i.e. M is the incidence matrix of an
        (a,b)-biregular bipartite graph
        <==>  the law is that of the COMMUTING projection family
              P_k = diag(1{r ~ k}).
Proof.  s_k = sum_r Bernoulli(c_{rk}), independent over r, so its pgf is
prod_r (1 - c_{rk} + c_{rk} z).  Equality with ((a-1+z)/a)^b forces exactly b
of the c_{rk} to equal 1/a and the rest to vanish (unique factorisation
again).  Row sums are 1, so each row has exactly a entries equal to 1/a.  QED

--------------------------------------------------------------------------
ROUTE (b) OF THE PLAN, resolved.  Conditioning a product measure on its total
DOES preserve strong Rayleigh (Borcea-Branden-Liggett), but it does NOT
preserve the marginals: conditioning n = qb independent Bernoulli(t) slots on
"total = p" gives, for every t, the UNIFORM p-subset, whose block counts are
HYPERGEOMETRIC(n,b,p), not Bin(b,1/a).  With p/n = 1/a the means agree but
        Var_hyp = (b/a)(1-1/a) (n-b)/(n-1)  <  b(a-1)/a^2 = Var_Bin ,
so conditioning makes the marginals STRICTLY LESS fluctuating than the
projection value -- the opposite direction from the scalar family, which is
strictly MORE fluctuating.  Both fail (ii); the projection value sits between
them.  The band is checked for the hypergeometric law below.
"""
import sys
import numpy as np
from math import comb
from itertools import combinations

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import (band, binom_pmf, naimark_slots, law_from_family,
                      graph_family, rand_proj_family, epoly,
                      real_stable_test, icosahedral_rank2)              # noqa
from frac_naimark import GRAPHS, degrees_ok                             # noqa


# ---------------------------------------------------------------- LEMMA 0
def within_block_independence(P, a, b, verbose=True):
    """Check E[prod_{i in T} X_i] = a^{-|T|} for every T inside a block."""
    q, p, _ = P.shape
    U = naimark_slots(P, a, b)
    K = U.conj().T @ U                       # the Naimark projection
    worst = 0.0
    for k in range(q):
        B = list(range(k * b, (k + 1) * b))
        for m in range(1, b + 1):
            for T in combinations(B, m):
                # for a DPP, E[prod X_i] = det K[T,T]
                v = float(np.real(np.linalg.det(K[np.ix_(T, T)])))
                worst = max(worst, abs(v - a ** (-m)))
    return worst


# ---------------------------------------------------------------- THM 1
def dpp_collapse_check(P, a, b):
    """Reconstruct the projection family from the DPP kernel alone and verify
    the reconstruction reproduces the same law."""
    q, p, _ = P.shape
    U = naimark_slots(P, a, b)
    K = U.conj().T @ U
    e_proj = float(np.abs(K @ K - K).max())
    e_rank = abs(float(np.real(np.trace(K))) - p)
    e_blocks = max(float(np.abs(K[k*b:(k+1)*b, k*b:(k+1)*b] - np.eye(b)/a).max())
                   for k in range(q))
    # reconstruct U from K by eigendecomposition, then P_k
    w, V = np.linalg.eigh(K)
    U2 = V[:, -p:].conj().T                  # p x n, U2 U2^* = I
    Prec = np.array([a * (U2[:, k*b:(k+1)*b] @ U2[:, k*b:(k+1)*b].conj().T)
                     for k in range(q)])
    e_sum = float(np.abs(Prec.sum(axis=0) - a * np.eye(p)).max())
    e_idem = max(float(np.abs(Prec[k] @ Prec[k] - Prec[k]).max()) for k in range(q))
    e_tr = max(abs(float(np.real(np.trace(Prec[k]))) - b) for k in range(q))
    # same law?
    W1, S1 = law_from_family(P, a, b)
    W2, S2 = law_from_family(np.real(Prec) if np.allclose(Prec.imag, 0) else Prec,
                             a, b)
    f1 = epoly(W1, S1, a, q)
    f2 = epoly(W2, S2, a, q)
    e_law = float(np.abs(f1 - f2).max() / max(1.0, np.abs(f1).max()))
    return dict(proj=e_proj, rank=e_rank, blocks=e_blocks, sum=e_sum,
                idem=e_idem, tr=e_tr, law=e_law)


# ---------------------------------------------------------------- THM 2
def balls_in_bins_law(C):
    """C: (p,q) row-stochastic.  Returns (W,S) for s = bin counts."""
    p, q = C.shape
    from itertools import product as iproduct
    key = {}
    for choice in iproduct(range(q), repeat=p):
        w = 1.0
        for r, k in enumerate(choice):
            w *= C[r, k]
        if w <= 0:
            continue
        s = [0] * q
        for k in choice:
            s[k] += 1
        t = tuple(s)
        key[t] = key.get(t, 0.0) + w
    S = np.array(list(key.keys()), dtype=int)
    W = np.array(list(key.values()), dtype=float)
    return W, S


def marg_err(W, S, q, a, b):
    tgt = binom_pmf(b, a)
    worst = 0.0
    for k in range(q):
        emp = np.zeros(b + 1)
        np.add.at(emp, S[:, k], W)
        worst = max(worst, float(np.abs(emp - tgt).max()))
    return worst


# ------------------------------------------------------------- ROUTE (b)
def hypergeom_block_law(n, b, p, q):
    """Uniform p-subset of [n], n = qb: exact law of the block-count vector,
    as (W,S) over compositions.  Enumerated by profile for speed."""
    from math import factorial
    key = {}

    def rec(k, left_slots, left_pts, cur, ways):
        if k == q:
            if left_pts == 0:
                key[tuple(cur)] = key.get(tuple(cur), 0) + ways
            return
        for j in range(0, min(b, left_pts) + 1):
            rec(k + 1, left_slots - b, left_pts - j, cur + [j],
                ways * comb(b, j))
    rec(0, n, p, [], 1)
    tot = comb(n, p)
    S = np.array(list(key.keys()), dtype=int)
    W = np.array([v / tot for v in key.values()], dtype=float)
    return W, S


def hyper_pmf(n, b, p):
    return np.array([comb(b, j) * comb(n - b, p - j) / comb(n, p)
                     if 0 <= p - j <= n - b else 0.0 for j in range(b + 1)])


# ------------------------------------------------------------ REGRESSIONS
def scalar_family_pgf_marginals(p, q, a, b):
    """A_k = (b/p) I_p: Poisson-binomial with p trials of parameter b/(pa)."""
    t = b / (p * a) * a  # eigenvalue alpha_i = b/p ; Bernoulli param alpha/a
    par = (b / p) / a
    pmf = np.zeros(p + 1)
    pmf[0] = 1.0
    for _ in range(p):
        pmf = np.convolve(pmf, [1 - par, par])[:p + 1]
    return pmf, par


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("LEMMA 0 -- inside a block the slots are EXACTLY iid Bernoulli(1/a)")
    print("   max over blocks and subsets T of | E prod_{i in T} X_i - a^-|T| |")
    print("=" * 78)
    for name, (adj, p, q, a, b) in GRAPHS.items():
        e = within_block_independence(graph_family(adj, p, q, a, b), a, b)
        print(f"   {name:22s} (p,q,a,b)=({p},{q},{a},{b})   err = {e:.3e}")
    P, p, q, a, b = icosahedral_rank2()
    print(f"   {'icosahedral':22s} (p,q,a,b)=({p},{q},{a},{b})   "
          f"err = {within_block_independence(P, a, b):.3e}")
    for (p, q, a, b) in [(6, 9, 3, 2), (6, 8, 4, 3), (5, 5, 3, 3)]:
        Pf, r = rand_proj_family(p, q, a, b, seed=3 * p + q)
        print(f"   {'random':22s} (p,q,a,b)=({p},{q},{a},{b})   "
              f"err = {within_block_independence(Pf, a, b):.3e}")
    print()

    print("=" * 78)
    print("THEOREM 1 -- DPP + (i) + (ii)  ==>  projection family  (route (a)")
    print("   of the plan is CLOSED: no determinantal counterexample exists)")
    print("=" * 78)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3), (5, 5, 3, 3)]:
        Pf, r = rand_proj_family(p, q, a, b, seed=17 * p + 5 * q)
        d = dpp_collapse_check(Pf, a, b)
        print(f"   ({p},{q},{a},{b}): K^2=K:{d['proj']:.1e}  tr K=p:{d['rank']:.1e}"
              f"  blocks=(1/a)I:{d['blocks']:.1e}")
        print(f"           reconstructed P_k: idempotent {d['idem']:.1e}, "
              f"trace b {d['tr']:.1e}, sum aI {d['sum']:.1e}, "
              f"SAME LAW {d['law']:.1e}")
    print()

    print("=" * 78)
    print("THEOREM 2 -- independent balls in bins + (i) + (ii)  ==>  the")
    print("   (a,b)-biregular bipartite design (a COMMUTING matrix family)")
    print("=" * 78)
    rng = np.random.default_rng(0)
    # (a) the biregular case reproduces the graph family exactly
    for name, (adj, p, q, a, b) in list(GRAPHS.items())[:4]:
        C = np.zeros((p, q))
        for i in range(p):
            for k in range(q):
                if (adj[i] >> k) & 1:
                    C[i, k] = 1.0 / a
        W, S = balls_in_bins_law(C)
        W2, S2 = law_from_family(graph_family(adj, p, q, a, b), a, b)
        f1, f2 = epoly(W, S, a, q), epoly(W2, S2, a, q)
        print(f"   {name:20s} biregular C -> same law as the design: "
              f"{np.abs(f1-f2).max()/max(1,np.abs(f2).max()):.2e}   "
              f"marginal err {marg_err(W,S,q,a,b):.1e}")
    # (b) any perturbation of C off {0,1/a} breaks (ii)
    print("   perturbing C away from the 0/(1/a) pattern breaks (ii):")
    adj, p, q, a, b = GRAPHS['S(K_4)']
    C0 = np.zeros((p, q))
    for i in range(p):
        for k in range(q):
            if (adj[i] >> k) & 1:
                C0[i, k] = 1.0 / a
    for eps in [0.0, 1e-3, 1e-2, 5e-2]:
        C = C0.copy()
        nz = np.argwhere(C0 > 0)
        C[nz[0][0], nz[0][1]] -= eps
        C[nz[1][0], nz[1][1]] += eps
        C = np.maximum(C, 0)
        C /= C.sum(axis=1, keepdims=True)
        W, S = balls_in_bins_law(C)
        print(f"      eps={eps:<7g} max|marginal - Bin(b,1/a)| = "
              f"{marg_err(W,S,q,a,b):.3e}")
    print()

    print("=" * 78)
    print("ROUTE (b) -- conditioning a product measure on its total.")
    print("   SR is preserved (BBL) but the marginals become HYPERGEOMETRIC,")
    print("   which is STRICTLY LESS fluctuating than Bin(b,1/a).")
    print("=" * 78)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (3, 4, 4, 3),
                         (6, 8, 4, 3), (5, 5, 3, 3), (4, 5, 5, 4)]:
        n = q * b
        W, S = hypergeom_block_law(n, b, p, q)
        hp = hyper_pmf(n, b, p)
        bp = binom_pmf(b, a)
        vh = float(sum(j * j * hp[j] for j in range(b + 1)) -
                   (sum(j * hp[j] for j in range(b + 1))) ** 2)
        vb = b * (a - 1) / a ** 2
        lo, hi = band(a, b)
        f = epoly(W, S, a, q)
        rts = np.roots(f)
        rr = np.sort(rts.real[np.abs(rts.real) > 1e-9])
        stab = real_stable_test(W, S, q, nsamp=120, seed=1)
        print(f"   ({p},{q},{a},{b})  n={n}: |hyper - Bin| = "
              f"{np.abs(hp-bp).max():.4f}   Var_hyp={vh:.5f} < Var_Bin={vb:.5f}"
              f"  (ratio (n-b)/(n-1) = {(n-b)/(n-1):.5f})")
        print(f"        SR probe {stab:.1e}; roots "
              f"{np.array2string(rr, precision=4)}  band [{lo:.4f},{hi:.4f}] "
              f" INSIDE={np.all(rr>=lo-1e-7) and np.all(rr<=hi+1e-7)}")
    print()

    print("=" * 78)
    print("MANDATORY REGRESSION 1 -- the scalar family A_k = (b/p) I")
    print("=" * 78)
    for (p, q, a, b) in [(4, 6, 3, 2), (6, 9, 3, 2), (6, 8, 4, 3)]:
        pmf, par = scalar_family_pgf_marginals(p, q, a, b)
        bp = binom_pmf(b, a)
        pad = np.zeros(len(pmf))
        pad[:len(bp)] = bp
        v_pb = p * par * (1 - par)
        print(f"   ({p},{q},{a},{b}): marginal of s_k is Poisson-binomial with "
              f"p={p} trials of parameter {par:.5f}")
        print(f"        support reaches {int((pmf>1e-14).sum())-1} > b={b};  "
              f"max|pmf - Bin(b,1/a)| = {np.abs(pmf-pad).max():.5f}")
        print(f"        Var = {v_pb:.6f} vs projection value "
              f"{b*(a-1)/a**2:.6f}  (excess {v_pb - b*(a-1)/a**2:+.6f}, "
              f"= (b/a^2)(1 - b/p) = {(b/a**2)*(1-b/p):+.6f}; "
              f"Poisson limit b/a^2 = {b/a**2:.6f})")
        print(f"        ==> hypothesis (ii) FAILS for the scalar family; that "
              f"is exactly what excludes it.")
