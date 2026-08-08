"""Which hypothesis does the band really need?

All classes live on the slot set [n] = [q] x [b], n = pa = qb, with the
"transversal" alternating sum

    N_K(y) = sum_{T transversal} (-a)^{|T|} det(K[T,T]) y^{q-|T|}.

  (G)  K = graph kernel  (1/a)*[same P-endpoint]          <-> biregular graph
  (P)  K rank-p orthogonal projection, blocks (1/a)I_b    <-> P_k rank-b proj,
                                                              sum P_k = a I
  (C)  0 <= K <= I,                blocks (1/a)I_b        <-> determinantal
                                                              measure with the
                                                              same 1-point and
                                                              within-block
                                                              2-point marginals
  (D)  K rank-p projection, diag(K) = 1/a, blocks free    <-> A_k PSD, rank<=b,
                                                              tr = b, sum = a I

(G) subset (P) subset (C), and (P) subset (D).  Real-rootedness of N_K holds on
all of them (mixed char poly of PSD matrices, MSS).  The question is the BAND.
"""
import sys
import numpy as np
from fractions import Fraction
from itertools import combinations, product
from frac_naimark import det_frac, sub, N_transversal, GRAPHS, graph_kernel


def band(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


# ------------------------------------------------------------- N_K, float
def transversals(q, b):
    """yield lists of slot indices, at most one per block."""
    def rec(k, cur):
        if k == q:
            yield cur
            return
        yield from rec(k + 1, cur)
        for j in range(b):
            yield from rec(k + 1, cur + [k * b + j])
    yield from rec(0, [])


_TCACHE = {}


def _tgroups(q, b):
    """transversal index sets grouped by size, as integer arrays."""
    key = (q, b)
    if key not in _TCACHE:
        bym = {}
        for T in transversals(q, b):
            bym.setdefault(len(T), []).append(T)
        _TCACHE[key] = {m: np.array(v, dtype=int) for m, v in bym.items()}
    return _TCACHE[key]


def N_K(Kmat, q, b, a):
    """coeff array high->low (length q+1) for np.roots."""
    acc = np.zeros(q + 1)
    for m, idx in _tgroups(q, b).items():
        if m == 0:
            acc[0] += 1.0
            continue
        blocks = Kmat[idx[:, :, None], idx[:, None, :]]      # (N, m, m)
        acc[m] += ((-a) ** m) * np.linalg.det(blocks).sum()
    return acc            # acc[m] multiplies y^{q-m}


def roots_report(c, a, b, tol=1e-8):
    r = np.roots(c)
    im = np.max(np.abs(r.imag)) if len(r) else 0.0
    rr = np.sort(r.real)
    nz = rr[np.abs(rr) > tol]
    lo, hi = band(a, b)
    return rr, nz, im, (nz.min() - lo if len(nz) else np.inf), \
        (hi - nz.max() if len(nz) else np.inf)


# ------------------------------------------------------ class (C) sampling
def proj_psd_contraction(M):
    w, V = np.linalg.eigh(0.5 * (M + M.T))
    return (V * np.clip(w, 0.0, 1.0)) @ V.T


def set_blocks(M, q, b, a):
    M = M.copy()
    for k in range(q):
        M[k * b:(k + 1) * b, k * b:(k + 1) * b] = np.eye(b) / a
    return M


def feasible_C(M, q, b, a, iters=400):
    """alternating projections onto {0<=K<=I} and {blocks = (1/a)I_b}."""
    for _ in range(iters):
        M = set_blocks(proj_psd_contraction(M), q, b, a)
    return M


def resid_C(M, q, b, a):
    w = np.linalg.eigvalsh(0.5 * (M + M.T))
    r1 = max(0.0, -w.min(), w.max() - 1.0)
    r2 = max(np.abs(M[k * b:(k + 1) * b, k * b:(k + 1) * b] - np.eye(b) / a).max()
             for k in range(q))
    return max(r1, r2)


# ------------------------------------------------------ class (D) sampling
def flat_projection(n, p, a, rng, iters=3000):
    """rank-p orthogonal projection on R^n with all diagonal entries 1/a."""
    U = rng.standard_normal((n, p))
    U, _ = np.linalg.qr(U)
    for _ in range(iters):
        nrm = np.linalg.norm(U, axis=1, keepdims=True)
        U = U * (1.0 / np.sqrt(a)) / np.maximum(nrm, 1e-300)
        U, _ = np.linalg.qr(U)
    return U @ U.T


# =====================================================================
def test_uniform_kernel():
    print("=" * 76)
    print("TEST 1.  K = (1/a) I_n  is in class (C):  0<=K<=I, blocks (1/a)I_b,")
    print("         tr K = n/a = p.  Its DPP = independent Bernoulli(1/a) slots.")
    print("         det(K[T,T]) = a^{-|T|} and there are C(q,m) b^m transversals")
    print("         of size m, so  N_K(y) = sum_m (-1)^m C(q,m) b^m y^{q-m}")
    print("                              = (y-b)^q,  ALL roots equal b.")
    print("         Band violated as soon as (sqrt(a-1)-sqrt(b-1))^2 > b, i.e.")
    print("         a - 2 > 2 sqrt((a-1)(b-1))   [b=2: a>=7;  b=3: a>=11].")
    print()
    from math import comb
    for (p, q, a, b) in [(2, 7, 7, 2), (2, 8, 8, 2), (4, 6, 3, 2)]:
        n = q * b
        assert p * a == q * b
        Kx = [[Fraction(1, a) if i == j else Fraction(0) for j in range(n)]
              for i in range(n)]
        c = N_transversal(Kx, q, b, a, exact=True)     # c[j] = coeff of y^j
        tgt = [Fraction((-b) ** (q - j) * comb(q, j)) for j in range(q + 1)]
        lo, hi = band(a, b)
        print(f"  p={p} q={q} (a,b)=({a},{b}):  N_K == (y-b)^q ? {c == tgt}"
              f"   root = {b}   band = [{lo:.6f}, {hi:.6f}]"
              f"   {'VIOLATES lower edge' if b < lo - 1e-12 else 'inside'}")
    print("  general (a,b) with a-2 > 2sqrt((a-1)(b-1)), symbolic check of the")
    print("  coefficient identity only (no det needed):")
    for (a, b, q) in [(7, 2, 7), (8, 2, 12), (11, 3, 11), (12, 3, 8)]:
        lo, hi = band(a, b)
        print(f"    (a,b)=({a},{b}) q={q}: root b={b} vs lower edge {lo:.6f}"
              f"  -> {'VIOLATION by %.4f' % (lo - b) if b < lo else 'inside'}")


def test_bridge(rng, cases):
    """N_K(y) = y^{q-r} mu[A_1..A_q](y),  A_k = a C^T Delta_k C,  K = C C^T.
    This is what makes real-rootedness on ALL of class (C) a theorem (MSS:
    mixed char polys of PSD matrices are real rooted) -- no normalisation
    sum A_k = a I is needed for real-rootedness, only for the band."""
    from mcp2 import mcp
    print("=" * 76)
    print("TEST 1b.  bridge identity N_K = y^{q-r} mu[a C^T Delta_k C]")
    for (p, q, a, b) in cases:
        n = q * b
        M = rng.standard_normal((n, n))
        Kc = feasible_C(0.3 * (M + M.T) + np.eye(n) / a, q, b, a, iters=300)
        if resid_C(Kc, q, b, a) > 1e-9:
            print(f"  p={p} q={q} (a,b)=({a},{b}): infeasible sample, skipped")
            continue
        w, V = np.linalg.eigh(Kc)
        keep = w > 1e-12
        r = int(keep.sum())
        C = (V[:, keep] * np.sqrt(w[keep]))          # n x r,  K = C C^T
        A = np.zeros((q, r, r))
        for k in range(q):
            Ck = C[k * b:(k + 1) * b, :]
            A[k] = a * (Ck.T @ Ck)
        c1 = N_K(Kc, q, b, a)                        # length q+1, high->low
        c2 = mcp(A)                                  # length r+1, high->low
        # y^{r-q} N_K(y) == mu[A](y)   (equivalently N_K = y^{q-r} mu[A])
        if r >= q:
            c1f = np.concatenate([c1, np.zeros(r - q)])
            c2f = c2
        else:
            c1f, c2f = c1, np.concatenate([c2, np.zeros(q - r)])
        c1, c2f = c1f, c2f
        sc = max(1.0, np.abs(c1).max())
        rts = np.roots(c1)
        print(f"  p={p} q={q} (a,b)=({a},{b}) rank K={r}: max coeff diff "
              f"{np.abs(c1 - c2f).max()/sc:.2e}   max|Im root| "
              f"{np.abs(rts.imag).max():.2e}   sum A_k = a I ? "
              f"{np.abs(A.sum(0) - a*np.eye(r)).max():.3f}")


def test_class_C_search(cases, rng, nrand=25, nstep=250):
    print("=" * 76)
    print("TEST 2.  minimise the smallest nonzero root of N_K over class (C)")
    print("         (convex set), by projected random search, starting from")
    print("         graph kernels, their mixtures, and random feasible points.")
    for (p, q, a, b) in cases:
        n = q * b
        lo, hi = band(a, b)
        # reference: graph kernels
        best = None
        starts = []
        adjs = list(all_biregular(p, q, a, b, cap=400))
        for adj in adjs[:40]:
            Kx, _ = graph_kernel(adj, p, q, a, b)
            starts.append(np.array([[float(x) for x in row] for row in Kx]))
        gmin = min(roots_report(N_K(Kk, q, b, a), a, b)[1].min()
                   for Kk in starts) if starts else np.nan
        for i in range(min(6, len(starts))):
            for j in range(i + 1, min(6, len(starts))):
                starts.append(0.5 * (starts[i] + starts[j]))
        for _ in range(nrand):
            M = rng.standard_normal((n, n))
            starts.append(feasible_C(0.5 * (M + M.T) * 0.3 + np.eye(n) / a,
                                     q, b, a, iters=200))
        worst = np.inf
        wK = None
        for K0 in starts:
            Kc = feasible_C(K0, q, b, a, iters=120)
            if resid_C(Kc, q, b, a) > 1e-7:
                continue
            _, nz, im, ml, mh = roots_report(N_K(Kc, q, b, a), a, b)
            v = nz.min() if len(nz) else np.inf
            if v < worst:
                worst, wK = v, Kc
        # local search
        eps = 0.25
        for step in range(nstep):
            H = rng.standard_normal((n, n))
            H = 0.5 * (H + H.T)
            Kc = feasible_C(wK + eps * H, q, b, a, iters=120)
            if resid_C(Kc, q, b, a) > 1e-7:
                continue
            _, nz, im, ml, mh = roots_report(N_K(Kc, q, b, a), a, b)
            v = nz.min() if len(nz) else np.inf
            if v < worst - 1e-12:
                worst, wK = v, Kc
            else:
                eps *= 0.995
        rr, nz, im, ml, mh = roots_report(N_K(wK, q, b, a), a, b)
        print(f"  p={p} q={q} (a,b)=({a},{b}) band=[{lo:.4f},{hi:.4f}]  "
              f"graphs min-root {gmin:.6f} | class(C) best min-root {worst:.6f} "
              f"({'VIOLATION' if worst < lo - 1e-9 else 'inside'})  "
              f"max|Im| {im:.1e}  rank {np.linalg.matrix_rank(wK, tol=1e-9)}")
        sys.stdout.flush()


def all_biregular(p, q, a, b, cap=200):
    """all (a,b)-biregular bipartite graphs on labelled parts, up to cap."""
    out = []
    cols = [c for c in combinations(range(p), b)]

    def rec(k, adj, degP):
        if len(out) >= cap:
            return
        if k == q:
            out.append(list(adj))
            return
        rem = q - k
        for c in cols:
            ok = True
            for i in c:
                if degP[i] + 1 > a:
                    ok = False
                    break
            if not ok:
                continue
            d2 = list(degP)
            for i in c:
                d2[i] += 1
            if any(a - d2[i] > rem - 1 for i in range(p)):
                continue
            for i in c:
                adj[i] |= 1 << k
            rec(k + 1, adj, d2)
            for i in c:
                adj[i] &= ~(1 << k)
    rec(0, [0] * p, [0] * p)
    return out


def test_class_D(cases, rng, ntry=40):
    print("=" * 76)
    print("TEST 3.  class (D): rank-p projection, diag = 1/a, blocks FREE")
    print("         (equivalently A_k PSD, rank<=b, tr A_k = b, sum A_k = a I;")
    print("          the block condition is exactly idempotency of each A_k).")
    for (p, q, a, b) in cases:
        n = q * b
        lo, hi = band(a, b)
        worst_lo, worst_hi, wim = np.inf, np.inf, 0.0
        for _ in range(ntry):
            Pi = flat_projection(n, p, a, rng)
            dmax = np.abs(np.diag(Pi) - 1.0 / a).max()
            if dmax > 1e-9:
                continue
            c = N_K(Pi, q, b, a)
            rr, nz, im, ml, mh = roots_report(c, a, b)
            worst_lo, worst_hi = min(worst_lo, ml), min(worst_hi, mh)
            wim = max(wim, im)
        print(f"  p={p} q={q} (a,b)=({a},{b}) band=[{lo:.4f},{hi:.4f}]  "
              f"worst lower margin {worst_lo:+.6f}  worst upper margin "
              f"{worst_hi:+.6f}  max|Im| {wim:.1e}"
              f"   {'VIOLATION' if min(worst_lo, worst_hi) < -1e-9 else 'inside'}")
        sys.stdout.flush()


if __name__ == '__main__':
    rng = np.random.default_rng(20260731)
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', '1'):
        test_uniform_kernel()
        test_bridge(rng, [(4, 6, 3, 2), (3, 6, 4, 2)])
    if which in ('all', '2'):
        test_class_C_search([(4, 6, 3, 2), (3, 6, 4, 2), (4, 8, 4, 2)], rng)
    if which in ('all', '3'):
        test_class_D([(4, 6, 3, 2), (3, 6, 4, 2), (4, 8, 4, 2), (6, 9, 3, 2)], rng)
