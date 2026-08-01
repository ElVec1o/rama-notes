"""sr_setup.py -- STEP 1 of the (SR-BAND) attack.

Verify, on real projection families, that the law of s = (s_1..s_q) satisfies
    (i)   sum_k s_k = p almost surely,
    (ii)  s_k ~ Binomial(b, 1/a) EXACTLY,
    (iii) G(z) = E prod_k z_k^{s_k} is homogeneous of degree p and REAL STABLE,
and that the roots of mu lie in the tree band.

Families covered
    * commuting (a,b)-biregular bipartite graph designs, incl. S(K_4) and the
      cube design (6,8,4,3);
    * a (6,9,3,2) noncommuting family;
    * the ICOSAHEDRAL rank-2 family: v_1..v_6 the 6 icosahedral diagonals in
      R^3 (sum v_k v_k^* = 2 I_3), P_k = I_3 - v_k v_k^*  -->  (p,q,a,b) =
      (3,6,4,2), genuinely noncommuting;
    * random tight fusion frames (noncommuting, several (p,q,a,b));
    * DIRECT SUMS  P_k = P_k^(1) (+) P_k^(2)  of two families with the same a
      and q -- these give new b = b_1+b_2 families and, on the measure side,
      the INDEPENDENT SUM  s = s^(1) + s^(2).  They are the reason
      Bin(b_1,1/a) * Bin(b_2,1/a) = Bin(b,1/a) matters.

REAL-STABILITY TEST (numerical, but sharp).  G is real stable iff for every
u in R^q and every v in R^q with v > 0 the univariate  t |-> G(u + t v)  has
only real roots.  We sample (u,v) and measure max |Im root|.  A single sample
with a genuinely complex root is a certificate of NON-stability; many clean
samples are strong evidence of stability.
"""
import sys
import numpy as np
from math import comb
from itertools import combinations

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from mcp2 import mcp, restore_proj, rand_X, proj_from_X                  # noqa
from frac_naimark import GRAPHS, degrees_ok                              # noqa


# ------------------------------------------------------------------ basics
def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def binom_pmf(b, a):
    return np.array([comb(b, j) * (1.0 / a) ** j * (1 - 1.0 / a) ** (b - j)
                     for j in range(b + 1)])


# ------------------------------------------------------ law from a family
def naimark_slots(P, a, b):
    q, p, _ = P.shape
    cols = []
    for k in range(q):
        w, V = np.linalg.eigh(P[k])
        cols.append(V[:, -b:] / np.sqrt(a))
    U = np.concatenate(cols, axis=1)
    return U


def law_from_family(P, a, b):
    """Returns (w, svec): the DPP law pushed to block counts, deduplicated."""
    q, p, _ = P.shape
    U = naimark_slots(P, a, b)
    n = q * b
    idx = np.array(list(combinations(range(n), p)), dtype=int)
    sub = np.transpose(U[:, idx], (1, 0, 2))
    w = np.abs(np.linalg.det(sub)) ** 2
    blocks = idx // b
    svec = np.zeros((len(idx), q), dtype=int)
    for j in range(p):
        np.add.at(svec, (np.arange(len(idx)), blocks[:, j]), 1)
    # merge identical s-vectors
    key = {}
    for wt, s in zip(w, svec):
        if wt <= 1e-15:
            continue
        t = tuple(s.tolist())
        key[t] = key.get(t, 0.0) + float(wt)
    S = np.array(list(key.keys()), dtype=int)
    W = np.array(list(key.values()), dtype=float)
    return W, S


# ------------------------------------------------------------- law checks
def check_law(W, S, p, q, a, b, nstab=400, seed=0, label=''):
    out = {}
    out['mass'] = float(W.sum())
    out['sum_ok'] = bool(np.all(S.sum(axis=1) == p))
    out['range_ok'] = bool(S.max() <= b and S.min() >= 0)
    tgt = binom_pmf(b, a)
    worst = 0.0
    for k in range(q):
        emp = np.zeros(b + 1)
        np.add.at(emp, S[:, k], W)
        worst = max(worst, float(np.abs(emp - tgt).max()))
    out['marg_err'] = worst
    out['stab'] = real_stable_test(W, S, q, nsamp=nstab, seed=seed)
    f = epoly(W, S, a, q)
    r = np.roots(f)
    out['maximag'] = float(np.abs(r.imag).max()) if len(r) else 0.0
    rr = np.sort(r.real)
    rr = rr[np.abs(rr) > 1e-9]          # drop the y^{q-p} factor
    out['roots'] = rr
    lo, hi = band(a, b)
    out['lo'], out['hi'] = lo, hi
    out['inside'] = bool(np.all(rr >= lo - 1e-7) and np.all(rr <= hi + 1e-7))
    out['margin_hi'] = float(hi - rr.max()) if len(rr) else np.inf
    out['margin_lo'] = float(rr.min() - lo) if len(rr) else np.inf
    return out


def epoly(W, S, a, q):
    """E prod_k (y - a s_k), coefficient list high->low degree."""
    acc = np.zeros(q + 1)
    seen = {}
    for wt, s in zip(W, S):
        t = tuple(sorted(s.tolist()))
        seen[t] = seen.get(t, 0.0) + wt
    for t, wt in seen.items():
        poly = np.array([1.0])
        for sk in t:
            poly = np.convolve(poly, [1.0, -a * float(sk)])
        acc += wt * poly
    return acc


def real_stable_test(W, S, q, nsamp=400, seed=0, ret_worst=False):
    """max over samples of max |Im| of the roots of t -> G(u + t v), v > 0.

    Uses the scaled variable  t  and a well-conditioned evaluation: for each
    sample we build the univariate polynomial exactly by convolution."""
    rng = np.random.default_rng(seed)
    worst = 0.0
    arg = None
    deg = int(S.sum(axis=1).max())
    for _ in range(nsamp):
        u = rng.normal(0, 1.0, size=q)
        v = rng.uniform(0.2, 2.0, size=q)
        acc = np.zeros(deg + 1)
        for wt, s in zip(W, S):
            poly = np.array([1.0])
            for k in range(q):
                for _rep in range(int(s[k])):
                    poly = np.convolve(poly, [v[k], u[k]])
            acc[deg + 1 - len(poly):] += wt * poly
        nz = np.argmax(np.abs(acc) > 1e-13 * max(1.0, np.abs(acc).max()))
        acc = acc[nz:]
        if len(acc) <= 1:
            continue
        r = np.roots(acc)
        m = float(np.abs(r.imag).max())
        # scale-free: compare to the spread of the real parts
        sc = max(1.0, float(np.abs(r.real).max()))
        if m / sc > worst:
            worst = m / sc
            arg = (u, v)
    return (worst, arg) if ret_worst else worst


# ------------------------------------------------------------- families
def graph_family(adj, p, q, a, b):
    P = np.zeros((q, p, p))
    for k in range(q):
        for i in range(p):
            if (adj[i] >> k) & 1:
                P[k, i, i] = 1.0
    return P


def icosahedral_rank2():
    """6 icosahedral diagonals in R^3; P_k = I - v_kv_k^*, sum = 4 I_3."""
    phi = (1 + np.sqrt(5)) / 2
    V = np.array([[0, 1, phi], [0, 1, -phi], [1, phi, 0], [1, -phi, 0],
                  [phi, 0, 1], [-phi, 0, 1]], dtype=float)
    V /= np.linalg.norm(V, axis=1, keepdims=True)
    P = np.array([np.eye(3) - np.outer(v, v) for v in V])
    return P, 3, 6, 4, 2


def rand_proj_family(p, q, a, b, seed, complex_=False, tries=60):
    rng = np.random.default_rng(seed)
    best = None
    for _ in range(tries):
        X = rand_X(q, p, b, rng, complex_)
        A = proj_from_X(X)
        A, r = restore_proj(A, q, p, a, b, iters=6000, tol=1e-14)
        if best is None or r < best[1]:
            best = (A, r)
        if r < 1e-13:
            break
    return best


def direct_sum(P1, P2):
    q, p1, _ = P1.shape
    q2, p2, _ = P2.shape
    assert q == q2
    P = np.zeros((q, p1 + p2, p1 + p2))
    P[:, :p1, :p1] = P1
    P[:, p1:, p1:] = P2
    return P


def rank1_tff(p, q, seed=0):
    """q unit vectors in R^p with sum v v^* = (q/p) I  (a = q/p integer)."""
    rng = np.random.default_rng(seed)
    a = q // p
    assert a * p == q
    X = rng.normal(size=(q, p, 1))
    A = proj_from_X(X)
    A, r = restore_proj(A, q, p, a, 1, iters=8000, tol=1e-14)
    return A, r


# ------------------------------------------------------------------- main
def report(name, P, a, b, nstab=250, seed=0):
    q, p, _ = P.shape
    W, S = law_from_family(P, a, b)
    o = check_law(W, S, p, q, a, b, nstab=nstab, seed=seed)
    lo, hi = o['lo'], o['hi']
    print(f"--- {name}: (p,q,a,b)=({p},{q},{a},{b})")
    print(f"    mass={o['mass']:.12f}  (i) sum=p:{o['sum_ok']}  0<=s<=b:"
          f"{o['range_ok']}  (ii) |marg-Bin| = {o['marg_err']:.2e}")
    print(f"    (iii) real-stability probe over {nstab} random lines: "
          f"max |Im|/scale = {o['stab']:.2e}")
    print(f"    roots {np.array2string(o['roots'], precision=5)}")
    print(f"    band [{lo:.5f},{hi:.5f}]  INSIDE={o['inside']}  "
          f"slack@hi={o['margin_hi']:.5f}  slack@lo={o['margin_lo']:.5f}")
    return o


if __name__ == '__main__':
    np.set_printoptions(linewidth=140)
    print("=" * 78)
    print("A.  commuting graph designs")
    print("=" * 78)
    for name, (adj, p, q, a, b) in GRAPHS.items():
        assert degrees_ok(adj, p, q, a, b)
        report(name, graph_family(adj, p, q, a, b), a, b, nstab=120)
    print()

    print("=" * 78)
    print("B.  icosahedral rank-2 family (noncommuting)")
    print("=" * 78)
    P, p, q, a, b = icosahedral_rank2()
    nc = max(np.linalg.norm(P[i] @ P[j] - P[j] @ P[i], 2)
             for i in range(6) for j in range(i + 1, 6))
    print(f"    noncommutativity max||[P_i,P_j]|| = {nc:.4f}")
    report("icosahedral (3,6,4,2)", P, a, b, nstab=250)
    print()

    print("=" * 78)
    print("C.  random tight fusion frames (noncommuting)")
    print("=" * 78)
    for (p, q, a, b) in [(6, 9, 3, 2), (4, 6, 3, 2), (6, 8, 4, 3), (5, 5, 3, 3)]:
        if p * a != q * b:
            print(f"  skip ({p},{q},{a},{b}): pa != qb")
            continue
        P, r = rand_proj_family(p, q, a, b, seed=97 * p + 13 * q + a)
        print(f"  [feasibility residual {r:.2e}]")
        report(f"random ({p},{q},{a},{b})", P, a, b, nstab=150)
    print()

    print("=" * 78)
    print("D.  DIRECT SUMS  (same a, same q; b = b_1 + b_2) -- new b>=3 data")
    print("=" * 78)
    # a = 3, q = 6:  b_1 = 2 (p_1 = 4)  (+)  b_2 = 1 (p_2 = 2)   ->  b = 3, p = 6
    P1, r1 = rand_proj_family(4, 6, 3, 2, seed=11)
    P2, r2 = rank1_tff(2, 6, seed=5)
    print(f"  [residuals {r1:.1e} {r2:.1e}]")
    report("dsum (4,6,3,2)+(2,6,3,1) = (6,6,3,3)", direct_sum(P1, P2), 3, 3,
           nstab=200)
    # a = 4, q = 8:  b_1 = 2 (p_1 = 4)  (+)  b_2 = 1 (p_2 = 2)  ->  b = 3, p = 6
    P1, r1 = rand_proj_family(4, 8, 4, 2, seed=21)
    P2, r2 = rank1_tff(2, 8, seed=7)
    print(f"  [residuals {r1:.1e} {r2:.1e}]")
    report("dsum (4,8,4,2)+(2,8,4,1) = (6,8,4,3)", direct_sum(P1, P2), 4, 3,
           nstab=200)
    # a = 4, q = 8: b_1 = b_2 = 2  ->  b = 4, p = 8   (a = b = 4, band [0,12])
    P1, r1 = rand_proj_family(4, 8, 4, 2, seed=31)
    P2, r2 = rand_proj_family(4, 8, 4, 2, seed=41)
    print(f"  [residuals {r1:.1e} {r2:.1e}]")
    report("dsum (4,8,4,2)+(4,8,4,2) = (8,8,4,4)", direct_sum(P1, P2), 4, 4,
           nstab=120)
