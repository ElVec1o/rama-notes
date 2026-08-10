r"""hl_planes.py -- HEILMANN-LIEB FOR PLANES.

CLEAN REFORMULATION of the target.  A family of rank-<=2 PSD matrices A_k on R^m
is, as far as F_A and Adj(A) are concerned, the same thing as a family of PLANES
V_k = range(A_k) with WEIGHTS c_k = e_2(A_k):  replacing A_k by sqrt(c_k) P_{V_k}
changes neither omega_k = b_{k1}^b_{k2} (up to nothing: omega_k = sqrt(c_k) w_k
with w_k the unit bivector of V_k) nor Theta_k = c_k P_{V_k}.  So

    CLASS  P(a) :  planes V_1..V_q in R^m, weights c_k >= 0,  sum_k c_k P_{V_k} <= a I
    POLY        :  F(x) = sum_{T} (-1)^{|T|} (prod_{k in T} c_k) ||w_T||^2 x^{m-2|T|}
    TARGET      :  all roots of F in [-2 sqrt(a), 2 sqrt(a)].

Graph case: V_k = span(e_u,e_v) for the edge k, c_k = its weight; then
sum c_k P_{V_k} = diag(weighted degrees) and ||w_T||^2 = 1 iff T is a matching,
so F = the weighted matching polynomial and the target is the weighted
Heilmann-Lieb bound 2 sqrt(D) -- which is SHARP (weighted K_m).

Everything here is computed from the list of m x 2 blocks B_k with
A_k = B_k B_k^T,  omega_k = column1 ^ column2.
"""
import numpy as np
from itertools import combinations

# --------------------------------------------------------------------------
#  F_A from the blocks
# --------------------------------------------------------------------------


def M_coeffs(Bs, m):
    """M_r = sum_{|T|=r} ||^_{k in T} omega_k||^2 = sum_{|T|=r} det Gram(cols of T).
    Returns array M[0..rmax], rmax = m//2."""
    q = len(Bs)
    rmax = min(m // 2, q)
    M = np.zeros(rmax + 1)
    M[0] = 1.0
    for r in range(1, rmax + 1):
        tot = 0.0
        for T in combinations(range(q), r):
            C = np.hstack([Bs[k] for k in T])          # m x 2r
            Gm = C.T @ C
            s, ld = np.linalg.slogdet(Gm)
            if s > 0:
                tot += np.exp(ld)
        M[r] = tot
    return M


def F_dense(Bs, m):
    """coefficients of F_A(x) high->low, length m+1."""
    M = M_coeffs(Bs, m)
    out = np.zeros(m + 1)
    for r, v in enumerate(M):
        out[2 * r] = ((-1) ** r) * v
    return out


def Theta_of(B):
    """Theta_k = e_2(A_k) * P_{range A_k}; also equals the matrix of
    v |-> ||iota_v omega_k||^2.

    Callers pass either an (m,2) array or a list of two columns, so coerce: hl_Wspec.py builds
    its families as lists and crashed here on B.shape, which made a script the note cites
    unrunnable.
    """
    B = np.asarray(B, dtype=float)
    if B.ndim == 1:
        B = B.reshape(-1, 1)
    m = B.shape[0]
    # omega = b1 ^ b2 ;  M_omega v = <v,b1>b2 - <v,b2>b1  ->  Gram form
    b1, b2 = B[:, 0], B[:, 1]
    n1, n2, ip = b1 @ b1, b2 @ b2, b1 @ b2
    # M = n2 b1 b1^T + n1 b2 b2^T - ip (b1 b2^T + b2 b1^T)
    return (n2 * np.outer(b1, b1) + n1 * np.outer(b2, b2)
            - ip * (np.outer(b1, b2) + np.outer(b2, b1)))


def Adj(Bs):
    return sum(Theta_of(B) for B in Bs)


def ortho_complement(vs, m):
    V = np.array(vs).T if len(vs) else np.zeros((m, 0))
    Qf, _ = np.linalg.qr(np.hstack([V, np.eye(m)]))
    return Qf[:, len(vs):].T                            # (m-|vs|) x m


def compress(Bs, Q):
    return [Q @ B for B in Bs]


def f_vec(B, e):
    b1, b2 = B[:, 0], B[:, 1]
    return (e @ b1) * b2 - (e @ b2) * b1


# --------------------------------------------------------------------------
#  the vertex recursion and its overlap term
# --------------------------------------------------------------------------
def recursion(Bs, m, e, tol=1e-13):
    """F_A = x F_{A'} - sum_k theta_k F_{A''_k} - X_e.
    Returns dict with dense coefficient arrays (all length m+1)."""
    Q = ortho_complement([e], m)
    Ac = compress(Bs, Q)
    fs = [f_vec(B, e) for B in Bs]
    th = np.array([float(f @ f) for f in fs])
    Phi = sum(np.outer(f, f) for f in fs)
    FA = F_dense(Bs, m)
    FAc = F_dense(Ac, m - 1)
    xFAc = np.concatenate([FAc, [0.0]])
    acc = np.zeros(m + 1)
    rho = np.full(len(Bs), np.nan)
    for k in range(len(Bs)):
        if th[k] < tol:
            continue
        fh = fs[k] / np.sqrt(th[k])
        rho[k] = float(fh @ Phi @ fh)
        Q2 = ortho_complement([e, fh], m)
        acc[2:] += th[k] * F_dense(compress(Bs, Q2), m - 2)
    X = xFAc - acc - FA
    return dict(FA=FA, xFAc=xFAc, acc=acc, X=X, th=th, rho=rho, Phi=Phi,
                FAc=FAc, fs=fs)


def C_list(X, m):
    """X_e = sum_{r>=2} (-1)^{r-1} C_r x^{m-2r}  ->  C_r for r=2..m//2."""
    return np.array([((-1) ** (r - 1)) * X[2 * r] for r in range(2, m // 2 + 1)])


# --------------------------------------------------------------------------
#  families
# --------------------------------------------------------------------------
def graph_blocks(edges, m, weights=None):
    Bs = []
    for i, (u, v) in enumerate(edges):
        w = 1.0 if weights is None else weights[i]
        B = np.zeros((m, 2))
        B[u, 0] = w ** 0.25
        B[v, 1] = w ** 0.25
        Bs.append(B)
    return Bs


def Kn_edges(n):
    return list(combinations(range(n), 2))


def cube_edges():
    e = []
    for x in range(8):
        for b in range(3):
            y = x ^ (1 << b)
            if x < y:
                e.append((x, y))
    return e


def petersen_edges():
    out = [(i, (i + 1) % 5) for i in range(5)]
    inn = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    spk = [(i, 5 + i) for i in range(5)]
    return out + inn + spk


def blocks_from_projection_family(Ps, a):
    """P_k rank-2 orthogonal projections, sum P_k = a I  ->  blocks."""
    Bs = []
    for P in Ps:
        w, V = np.linalg.eigh(P)
        Bs.append(V[:, -2:])
    return Bs


def random_projection_family(m, a, seed=0, iters=6000, tol=1e-14):
    """alternating projections on R^(2q): rank-m projection with 2x2 diagonal
    blocks I_2/a.  Returns list of m x 2 blocks (orthonormal columns)."""
    rng = np.random.default_rng(seed)
    assert (m * a) % 2 == 0
    q = m * a // 2
    n = 2 * q
    X = rng.standard_normal((n, n))
    Pi = X + X.T
    err = 1.0
    for _ in range(iters):
        w, V = np.linalg.eigh(Pi)
        Pi = V[:, -m:] @ V[:, -m:].T
        err = 0.0
        for k in range(q):
            Bk = Pi[2 * k:2 * k + 2, 2 * k:2 * k + 2]
            err = max(err, np.abs(Bk - np.eye(2) / a).max())
            Pi[2 * k:2 * k + 2, 2 * k:2 * k + 2] = np.eye(2) / a
        if err < tol:
            break
    w, V = np.linalg.eigh(Pi)
    U = V[:, -m:].T * np.sqrt(a)        # m x n, block k columns span range P_k
    Bs = []
    for k in range(q):
        Ck = U[:, 2 * k:2 * k + 2]
        Qc, _ = np.linalg.qr(Ck)
        Bs.append(Qc)
    return Bs, err


def random_plane_family(m, a, q=None, seed=0, jitter=0.35, tries=200):
    """Non-projection plane family with sum_k c_k P_{V_k} = a I EXACTLY.

    Start from a genuine rank-2 projection family (c == 1), rotate every plane
    by a random amount, then correct the weights by the minimum-norm solution of
    the linear system sum_k c_k P_{V_k} = a I.  Generically noncommuting and
    with c_k != 1, so NOT a projection family."""
    rng = np.random.default_rng(seed)
    idx = [(i, j) for i in range(m) for j in range(i, m)]
    b = np.array([a if i == j else 0.0 for (i, j) in idx])
    if q is None:
        q = 3 * (m * (m + 1) // 2)
    for _ in range(tries):
        Us = []
        for _k in range(q):
            Z = rng.standard_normal((m, 2))
            Qz, _ = np.linalg.qr(Z)
            Us.append(Qz)
        qq = len(Us)
        A = np.zeros((len(idx), qq))
        for k in range(qq):
            P = Us[k] @ Us[k].T
            for t, (i, j) in enumerate(idx):
                A[t, k] = P[i, j] * (1.0 if i == j else np.sqrt(2.0))
        c0 = np.full(qq, a * m / (2.0 * qq))
        dc, *_ = np.linalg.lstsq(A, b - A @ c0, rcond=None)
        c = c0 + dc
        if c.min() <= 1e-6:
            continue
        res = float(np.abs(A @ c - b).max())
        if res > 1e-9:
            continue
        Bs = [Us[k] * c[k] ** 0.25 for k in range(qq)]
        return Bs, res
    return None, np.inf


# --------------------------------------------------------------------------
if __name__ == '__main__':
    np.set_printoptions(precision=5, suppress=True)
    rng = np.random.default_rng(0)

    def report(name, Bs, m, a, ntrial=8):
        FA = F_dense(Bs, m)
        rts = np.roots(FA)
        maxim = np.abs(rts.imag).max()
        mr = rts.real.max()
        Adm = Adj(Bs)
        adev = np.abs(Adm - a * np.eye(m)).max()
        # sign of X_e over random e, on x >= 2 sqrt(a)
        xs = 2 * np.sqrt(a) * np.array([1.0, 1.02, 1.1, 1.5, 2.5, 5.0])
        worstX = -np.inf
        Cmin = np.inf
        Yroot = -np.inf
        Yreal = True
        for tr in range(ntrial):
            e = np.zeros(m)
            if tr == 0:
                e[0] = 1.0
            else:
                e = rng.standard_normal(m)
            e /= np.linalg.norm(e)
            R = recursion(Bs, m, e)
            X, FAc = R['X'], R['FAc']
            for x in xs:
                den = abs(np.polyval(FAc, x))
                worstX = max(worstX, np.polyval(X, x) / max(den, 1e-300))
            Cs = C_list(X, m)
            if len(Cs):
                Cmin = min(Cmin, Cs.min())
            Y = -X
            nz = np.abs(Y) > 1e-11 * max(1.0, np.abs(Y).max())
            if nz.any():
                Yp = Y[np.argmax(nz):]
                if len(Yp) > 1:
                    rr = np.roots(Yp)
                    Yreal = Yreal and (np.abs(rr.imag).max()
                                       < 1e-6 * max(1.0, np.abs(rr).max()))
                    Yroot = max(Yroot, rr.real.max())
        print(f"{name:22s} m={m:3d} a={a:5.2f} q={len(Bs):3d} |Adj-aI|={adev:8.1e} "
              f"| maxroot={mr:8.4f} 2sqa={2*np.sqrt(a):7.4f} "
              f"{'OK ' if mr <= 2*np.sqrt(a)+1e-9 else 'BAND VIOLATION'} "
              f"| imag={maxim:7.1e} | worst X/F'={worstX:11.3e} "
              f"minC_r={Cmin:11.3e} Yreal={str(Yreal):5s} maxrootY={Yroot:8.4f}")
        return mr

    print("=" * 150)
    print("PROJECTION FAMILIES (Adj = a I)")
    print("=" * 150)
    for nm, ed, m, a in [('K_4', Kn_edges(4), 4, 3), ('K_{3,3}',
                         [(i, 3 + j) for i in range(3) for j in range(3)], 6, 3),
                        ('cube Q_3', cube_edges(), 8, 3),
                        ('Petersen', petersen_edges(), 10, 3)]:
        report(nm, graph_blocks(ed, m), m, a)
    for m, a, sd in [(4, 3, 1), (4, 3, 2), (6, 3, 5), (6, 3, 6), (4, 5, 7),
                     (8, 3, 9)]:
        Bs, err = random_projection_family(m, a, seed=sd)
        if err > 1e-11:
            print(f"  [skip random {m}/{a} seed {sd}: residual {err:.1e}]")
            continue
        report(f'randproj m{m} a{a} s{sd}', Bs, m, a)

    print()
    print("=" * 150)
    print("WEIGHTED GRAPHS with Adj = a I  (NOT projections)")
    print("=" * 150)
    for m, a in [(6, 3), (8, 3), (10, 3), (12, 3)]:
        lam = a / (m - 1)
        report(f'weighted K_{m}', graph_blocks(Kn_edges(m), m,
                                               [lam] * (m * (m - 1) // 2)), m, a)

    print()
    print("=" * 150)
    print("RANDOM PLANE FAMILIES with Adj = a I  (noncommuting, NOT projections)")
    print("=" * 150)
    for m, a, q, sd in [(4, 3, 12, 1), (4, 3, 14, 2), (5, 3, 18, 3),
                        (6, 3, 24, 4), (6, 2, 24, 5)]:
        Bs, res = random_plane_family(m, a, q, seed=sd)
        if Bs is None:
            print(f"  [no feasible plane family m={m} a={a} q={q}]")
            continue
        report(f'randplane m{m} a{a} s{sd}', Bs, m, a)
