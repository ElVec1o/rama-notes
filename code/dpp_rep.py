"""dpp_rep.py -- the product/expectation representation, pinned down and verified.

SETUP.  P_1..P_q rank-b orthogonal projections on R^p (or C^p) with
sum_k P_k = a I_p.  Taking traces, p a = q b =: n.

NAIMARK SLOTS.  Write P_k = W_k W_k^*, W_k in R^{p x b}, W_k^* W_k = I_b.
Put U_k = W_k / sqrt(a) and U = [U_1 | ... | U_q] in R^{p x n}.  Then
U U^* = (1/a) sum_k P_k = I_p, and U_k^* U_k = (1/a) I_b.
Set  Pi = U^* U : a rank-p orthogonal projection on R^n whose k-th diagonal
b x b block is exactly (1/a) I_b.  Slots are indexed by (k,j), k in [q],
j in [b]; block B_k = {(k,1),..,(k,b)}.

THE LAW OF S.  S ~ DPP(Pi): the determinantal point process with the rank-p
projection kernel Pi.  Concretely  P(S = T) = det(Pi[T,T]) = |det U[:,T]|^2
for every T with |T| = p, and P(|S| = p) = 1 (Cauchy-Binet).
s_k(S) := |S cap B_k|.

THE IDENTITY (Theorem A, proved in the report; verified here):

    y^{q-p} * mu[P_1..P_q](y)  =  E_S prod_{k=1}^q ( y - a * s_k(S) ).

DETERMINISTIC / DISTRIBUTIONAL FACTS (all verified here):
    (F1)  sum_k s_k(S) = p  for EVERY realisation S.
    (F2)  0 <= s_k <= b.
    (F3)  s_k ~ Binomial(b, 1/a) EXACTLY, for every k.  (Not just mean b/a.)
          Hence E s_k = b/a, Var s_k = b(a-1)/a^2.
    (F4)  joint pgf:  E prod_k z_k^{s_k} = a^{-p} det( sum_k z_k P_k ).
          Homogeneous of degree p  <=>  (F1);  real stable  =>  strong Rayleigh
          => negatively associated.
    (F5)  coefficients:  mu(y) = sum_{j=0}^p (-1)^j a^j E[e_j(s)] y^{p-j},
          so the "matching numbers" are  m_j = a^j E[e_j(s_1..s_q)].
          In particular E[e_j(s)] = 0 for j > p (automatic from (F1)).

COMMUTING SPECIALISATION.  If P_k = diag(1_{N(k)}) for an (a,b)-biregular
bipartite graph G, then Pi is block diagonal w.r.t. the partition of slots by
their P-endpoint, each block being the rank-one projection (1/a) J_a.  So
    S = "each P-vertex independently picks one of its a incident edges,
         uniformly"  ,   s_k = # of P-neighbours of k that picked k.
This is verified too.
"""
import sys
import numpy as np
from itertools import combinations
from math import comb
from fractions import Fraction

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from mcp2 import mcp, restore_proj, rand_X, proj_from_X, resid          # noqa
from frac_naimark import GRAPHS, degrees_ok                              # noqa


# ---------------------------------------------------------------- utilities
def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def naimark_slots(P, a, b):
    """P: (q,p,p) rank-b projections summing to a I.  Return U (p x n) with
    U U^* = I and U_k^* U_k = (1/a) I_b, and Pi = U^* U."""
    q, p, _ = P.shape
    cols = []
    for k in range(q):
        w, V = np.linalg.eigh(P[k])
        cols.append(V[:, -b:] / np.sqrt(a))
    U = np.concatenate(cols, axis=1)
    return U, U.conj().T @ U


def dpp_data(U, p, q, b):
    """Enumerate the support of DPP(Pi).  Returns (weights, svec) with
    weights[t] = P(S = T_t) and svec[t] = (s_1..s_q)."""
    n = U.shape[1]
    idx = np.array(list(combinations(range(n), p)), dtype=int)
    sub = U[:, idx]                       # (p, N, p) -> need (N,p,p)
    sub = np.transpose(sub, (1, 0, 2))
    d = np.linalg.det(sub)
    w = np.abs(d) ** 2
    blocks = idx // b                     # (N,p)
    svec = np.zeros((len(idx), q), dtype=int)
    for j in range(p):
        np.add.at(svec, (np.arange(len(idx)), blocks[:, j]), 1)
    return w, svec, idx


def epoly_from_law(w, svec, a, q):
    """E prod_k (y - a s_k) as coeff list c[0..q], c[i] = coeff of y^{q-i}."""
    acc = np.zeros(q + 1)
    for wt, s in zip(w, svec):
        if wt == 0.0:
            continue
        poly = np.array([1.0])
        for sk in s:
            poly = np.convolve(poly, [1.0, -a * float(sk)])
        acc += wt * poly
    return acc


def epoly_fast(w, svec, a, q):
    """Same, grouped by the multiset of s (there are few distinct patterns)."""
    key = {}
    for wt, s in zip(w, svec):
        if wt <= 0:
            continue
        t = tuple(sorted(s.tolist()))
        key[t] = key.get(t, 0.0) + wt
    acc = np.zeros(q + 1)
    for t, wt in key.items():
        poly = np.array([1.0])
        for sk in t:
            poly = np.convolve(poly, [1.0, -a * float(sk)])
        acc += wt * poly
    return acc, key


def rand_proj_family(p, q, a, b, seed, complex_=False, tries=40):
    rng = np.random.default_rng(seed)
    best = None
    for _ in range(tries):
        X = rand_X(q, p, b, rng, complex_)
        A = proj_from_X(X)
        A, r = restore_proj(A, q, p, a, b, iters=4000, tol=1e-14)
        if best is None or r < best[1]:
            best = (A, r)
        if r < 1e-13:
            break
    return best


def noncommutativity(P):
    """max_{j<k} ||[P_j,P_k]|| ; 0 iff the family commutes."""
    q = P.shape[0]
    m = 0.0
    for j in range(q):
        for k in range(j + 1, q):
            C = P[j] @ P[k] - P[k] @ P[j]
            m = max(m, np.linalg.norm(C, 2))
    return m


# ---------------------------------------------------------------- one test
def check_family(name, P, a, b, verbose=True):
    q, p, _ = P.shape
    n = q * b
    assert p * a == n
    U, Pi = naimark_slots(P, a, b)

    # --- structural checks on the Naimark data
    e1 = np.abs(U @ U.conj().T - np.eye(p)).max()
    e2 = max(np.abs(Pi[k * b:(k + 1) * b, k * b:(k + 1) * b] - np.eye(b) / a).max()
             for k in range(q))

    w, svec, idx = dpp_data(U, p, q, b)
    mass = w.sum()

    # --- (F1) deterministic sum
    sums = svec.sum(axis=1)
    f1 = np.all(sums == p)
    # --- (F2) range
    f2 = svec.max() <= b and svec.min() >= 0

    # --- (F3) marginal law of s_k
    binom = np.array([comb(b, j) * (1.0 / a) ** j * (1 - 1.0 / a) ** (b - j)
                      for j in range(b + 1)])
    f3 = 0.0
    for k in range(q):
        emp = np.zeros(b + 1)
        np.add.at(emp, svec[:, k], w)
        f3 = max(f3, np.abs(emp - binom).max())

    # --- (F4) pgf identity at random z
    rng = np.random.default_rng(7)
    f4 = 0.0
    for _ in range(6):
        z = rng.uniform(0.3, 2.5, size=q)
        lhs = float(np.sum(w * np.prod(z[None, :] ** svec, axis=1)))
        M = np.tensordot(z, P, axes=(0, 0))
        rhs = float(np.real(np.linalg.det(M))) / a ** p
        f4 = max(f4, abs(lhs - rhs) / max(1.0, abs(rhs)))

    # --- the identity itself
    c_dpp, key = epoly_fast(w, svec, a, q)      # length q+1, index = q - power
    mu = mcp(P)                                  # length p+1, index = p - power
    c_mu = np.zeros(q + 1)
    c_mu[:p + 1] = mu                            # y^{q-p} * mu(y)
    scale = max(1.0, np.abs(c_mu).max())
    err = np.abs(c_dpp - c_mu).max() / scale

    # --- (F5) matching numbers m_j = a^j E e_j(s)
    mj = np.array([abs(c_mu[j]) for j in range(p + 1)])

    # --- roots + band
    rts = np.sort(np.roots(mu).real)
    imag = np.max(np.abs(np.roots(mu).imag)) if p else 0.0
    lo, hi = band(a, b)
    inside = bool(np.all(rts >= lo - 1e-8) and np.all(rts <= hi + 1e-8))

    # --- realisation statistics
    smax = svec.max(axis=1)
    emax = float(np.sum(w * smax))
    pexceed = float(np.sum(w * (a * smax > hi)))

    # --- pairwise covariance (negative correlation check)
    Es = (w[:, None] * svec).sum(axis=0)
    mincov, maxcov = 0.0, -np.inf
    for j in range(q):
        for k in range(j + 1, q):
            cv = float(np.sum(w * svec[:, j] * svec[:, k]) - Es[j] * Es[k])
            mincov = min(mincov, cv)
            maxcov = max(maxcov, cv)

    if verbose:
        print(f"--- {name}: p={p} q={q} (a,b)=({a},{b}) n={n}   "
              f"noncomm={noncommutativity(P):.3f}")
        print(f"    Naimark: |UU*-I|={e1:.2e}  |blocks-(1/a)I|={e2:.2e}  "
              f"total DPP mass={mass:.12f}")
        print(f"    IDENTITY  y^(q-p) mu(y) = E prod_k (y - a s_k) : "
              f"rel err {err:.3e}")
        print(f"    (F1) sum_k s_k = p always : {f1}   "
              f"(F2) 0<=s_k<=b : {f2}")
        print(f"    (F3) max |law(s_k) - Bin(b,1/a)| = {f3:.3e}")
        print(f"    (F4) pgf = a^-p det(sum z_k P_k) : rel err {f4:.3e}")
        print(f"    (F5) m_j = a^j E e_j(s) : {np.array2string(mj, precision=4)}")
        print(f"    roots {np.array2string(rts, precision=5)}  |Im|={imag:.1e}")
        print(f"    band [{lo:.5f},{hi:.5f}] inside={inside}   "
              f"E[max_k s_k]={emax:.4f}  P(a*max s_k > hi)={pexceed:.4f}")
        print(f"    cov(s_j,s_k) in [{mincov:.5f},{maxcov:.5f}]  "
              f"(negatively correlated: {maxcov <= 1e-12})")
    return dict(err=err, f1=f1, f2=f2, f3=f3, f4=f4, inside=inside,
                rts=rts, lo=lo, hi=hi, key=key, w=w, svec=svec, mj=mj,
                pexceed=pexceed, emax=emax, maxcov=maxcov)


def graph_family(adj, p, q, a, b):
    P = np.zeros((q, p, p))
    for k in range(q):
        for i in range(p):
            if (adj[i] >> k) & 1:
                P[k, i, i] = 1.0
    return P


def check_graph_ballsinbins(adj, p, q, a, b):
    """In the commuting case the DPP is: each P-vertex picks one incident edge
    uniformly and independently.  Verify E prod (y - a s_k) against that."""
    nbrs = [[k for k in range(q) if (adj[i] >> k) & 1] for i in range(p)]
    from itertools import product as iproduct
    acc = np.zeros(q + 1)
    tot = 0.0
    wt = 1.0 / a ** p
    for choice in iproduct(*nbrs):
        s = [0] * q
        for k in choice:
            s[k] += 1
        poly = np.array([1.0])
        for sk in s:
            poly = np.convolve(poly, [1.0, -a * float(sk)])
        acc += wt * poly
        tot += wt
    return acc, tot


if __name__ == '__main__':
    print("=" * 78)
    print("PART 1 -- commuting (graph) families")
    print("=" * 78)
    for name, (adj, p, q, a, b) in GRAPHS.items():
        assert degrees_ok(adj, p, q, a, b)
        P = graph_family(adj, p, q, a, b)
        r = check_family(name, P, a, b)
        cb, tot = check_graph_ballsinbins(adj, p, q, a, b)
        mu = mcp(P)
        c_mu = np.zeros(q + 1)
        c_mu[:p + 1] = mu
        e = np.abs(cb - c_mu).max() / max(1.0, np.abs(c_mu).max())
        print(f"    balls-in-bins model (each P-vertex picks 1 of its a edges):"
              f" rel err {e:.3e}  (mass {tot:.10f})")
        print()

    print("=" * 78)
    print("PART 2 -- genuinely NONCOMMUTING rank-b projection families")
    print("=" * 78)
    cases = [(4, 6, 3, 2, False), (3, 6, 4, 2, False), (4, 8, 4, 2, False),
             (5, 10, 4, 2, False), (6, 8, 4, 3, False), (4, 6, 3, 2, True),
             (6, 9, 3, 2, False)]
    for (p, q, a, b, cx) in cases:
        if p * a != q * b:
            print(f"skip {(p,q,a,b)}: pa != qb")
            continue
        P, res = rand_proj_family(p, q, a, b, seed=1000 + p * 31 + q * 7 + a,
                                  complex_=cx)
        tag = ("complex " if cx else "") + f"random ({p},{q},{a},{b})"
        print(f"[feasibility residual {res:.2e}]")
        check_family(tag, P, a, b)
        print()
