r"""Upper-edge contract C-upper: infrastructure + Step-1 validation.

Objects.  A kernel-with-blocks is (K, blocks, a): K an n x n PSD contraction,
blocks a list of disjoint index lists (sizes b_k <= b), diagonal blocks
K[blk,blk] <= (1/a) I.  The transversal polynomial (q = len(blocks), empty
blocks allowed and counted):

    N_K(y) = sum_{T transversal} (-a)^{|T|} det K[T,T] y^{q-|T|}.

Verified identities (slot e in block k, K^{(e)} = K - K[:,e]K[e,:]/K_ee):

    (slot)   N_K = N_{K \ e} - a K_ee N_{K^{(e)} \ blk k}
    (block)  N_K = y N_{K \ blk k} - a sum_{e in blk k} K_ee N_{K^{(e)} \ blk k}
    (border) a N_{M + w w^T} = (a - y) N_M + N_{M~0},
             M~0 = [[0, w^T], [w, M]] with the new slot 0 as its own block.

Tree fixed point (this normalisation).  On the (a,b)-biregular tree the
P-branch ratio A and Q-branch ratio R satisfy A = y - (a-1)/R,
R = 1 - (b-1)/A, hence

    A^2 - (y - a + b) A + (b-1) y = 0,

real roots exactly for y outside [(s-t)^2, (s+t)^2], s = sqrt(a-1),
t = sqrt(b-1).  For y > (s+t)^2 put A+ = larger root, Lambda(y) = y / A+.
Graph shadow of the recursion ratios:
    B_k := N_K / N_{K \ blk k} = y - a sum_e K_ee S_e ,
    S_e := N_{K^{(e)} \ blk k} / N_{K \ blk k}      ( = y / A_i  on graphs ).
Tree values: S = y/A in [1, Lambda], B = y - a tau Lambda at the full tree
(tau = tr K[blk]).  Conjectured invariant (INV), tested in upper_inv.py:
    B_k in [y - a tau_k Lambda(y), y - a tau_k],   S_e in [1, Lambda(y)].
"""
import sys
from fractions import Fraction
from itertools import product
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from frac_naimark import (det_frac, sub, nu_coeffs, graph_kernel,
                          subdivision_K4, cube_design, K as Kmn)
from tff import build_tff, random_biregular, graph_to_projections, commutativity
from naimark_form import naimark_pi


# ----------------------------------------------------------- N coefficients
def tgroup_arrays(blocks):
    """transversal index tuples grouped by size m >= 1."""
    opts = [[None] + list(bk) for bk in blocks]
    bym = {}
    for choice in product(*opts):
        T = [x for x in choice if x is not None]
        if T:
            bym.setdefault(len(T), []).append(T)
    return {m: np.array(v, dtype=int) for m, v in bym.items()}


def N_coeffs(K, blocks, a):
    """float coeffs, c[m] = coefficient of y^{q-m} (high -> low), c[0] = 1."""
    q = len(blocks)
    c = np.zeros(q + 1)
    c[0] = 1.0
    for m, idx in tgroup_arrays(blocks).items():
        mats = K[idx[:, :, None], idx[:, None, :]]
        c[m] = ((-a) ** m) * np.linalg.det(mats).sum()
    return c


def N_coeffs_frac(K, blocks, a):
    """exact version; K = list of lists of Fractions."""
    q = len(blocks)
    c = [Fraction(0)] * (q + 1)
    c[0] = Fraction(1)
    for m, idx in tgroup_arrays(blocks).items():
        tot = Fraction(0)
        for T in idx.tolist():
            tot += det_frac(sub(K, T))
        c[m] = Fraction((-a) ** m) * tot
    return c


def polyval_high(c, y):
    v = 0.0
    for x in c:
        v = v * y + x
    return v


def top_root(c, tol=1e-9):
    r = np.roots(c)
    rr = r.real[np.abs(r.imag) < 1e-6 * max(1.0, np.abs(r).max())]
    return rr.max() if len(rr) else -np.inf, np.abs(r.imag).max()


# ----------------------------------------------------------- kernel surgery
def schur_np(K, e):
    col = K[:, e].copy()
    return K - np.outer(col, col) / K[e, e]


def schur_frac(K, e):
    n = len(K)
    ce = K[e][e]
    return [[K[i][j] - K[i][e] * K[e][j] / ce for j in range(n)]
            for i in range(n)]


def del_slot(blocks, e):
    return [[x for x in bk if x != e] for bk in blocks]


def del_block(blocks, k):
    return [bk for j, bk in enumerate(blocks) if j != k]


def thin_block(blocks, k, e):
    return [([e] if j == k else bk) for j, bk in enumerate(blocks)]


def border_w(M, w):
    """M~0 = [[0, w^T],[w, M]] and the shifted block list gets [[0]] prepended
    by the caller."""
    n = M.shape[0]
    out = np.zeros((n + 1, n + 1))
    out[1:, 1:] = M
    out[0, 1:] = w
    out[1:, 0] = w
    return out


# ----------------------------------------------------------- class checking
def class_report(K, blocks, a):
    """(min eig, max eig, max block eig - 1/a)  for K in K(a, b)."""
    w = np.linalg.eigvalsh(0.5 * (K + K.T))
    worst = -np.inf
    for bk in blocks:
        if bk:
            wb = np.linalg.eigvalsh(K[np.ix_(bk, bk)])
            worst = max(worst, wb.max() - 1.0 / a)
    return w.min(), w.max(), worst


# ----------------------------------------------------------- tree quantities
def band_edges(a, b):
    s, t = np.sqrt(a - 1.0), np.sqrt(b - 1.0)
    return (s - t) ** 2, (s + t) ** 2


def A_plus(y, a, b):
    d = (y - a + b) ** 2 - 4.0 * (b - 1) * y
    return 0.5 * ((y - a + b) + np.sqrt(d))


def A_minus(y, a, b):
    d = (y - a + b) ** 2 - 4.0 * (b - 1) * y
    return 0.5 * ((y - a + b) - np.sqrt(d))


def Lambda(y, a, b):
    return y / A_plus(y, a, b)


def tree_AR_sequence(y, a, b, depth):
    """finite-tree cavity values: A_0 = y (P-leaf), R_h = 1 - (b-1)/A_h,
    A_{h+1} = y - (a-1)/R_h.  Works for Fractions and floats."""
    one = y / y
    A = [y]
    R = [one - (b - 1) / y]
    for _ in range(depth):
        A.append(y - (a - 1) / R[-1])
        R.append(one - (b - 1) / A[-1])
    return A, R


# ----------------------------------------------------------- tree graphs
def biregular_tree(a, b, plevels):
    """(a,b)-biregular tree truncated so it stays small: root Q-vertex with b
    P-children; each P-vertex has a-1 Q-children for `plevels` rounds; last
    Q-generation are leaves.  Returns (adj, p, q) with adj[i] = bitmask over Q.
    plevels = 1: root + b P's + b(a-1) Q-leaves."""
    adjrows = []          # per P-vertex bitmask
    qcount = 1            # Q-vertex 0 = root
    pend = []             # P-vertices to expand: (index, parent q)
    for _ in range(b):
        adjrows.append(1 << 0)
        pend.append(len(adjrows) - 1)
    for lev in range(plevels - 1):
        newpend = []
        for i in pend:
            for _ in range(a - 1):
                kq = qcount
                qcount += 1
                adjrows[i] |= 1 << kq
                for _ in range(b - 1):
                    adjrows.append(1 << kq)
                    newpend.append(len(adjrows) - 1)
        pend = newpend
    # close: give each pending P-vertex its a-1 leaf Q-children
    for i in pend:
        for _ in range(a - 1):
            adjrows[i] |= 1 << qcount
            qcount += 1
    return adjrows, len(adjrows), qcount


# ----------------------------------------------------------- the kernel zoo
def frac_to_np(K):
    return np.array([[float(x) for x in row] for row in K])


def uniform_blocks(q, b):
    return [list(range(k * b, (k + 1) * b)) for k in range(q)]


def icosahedral_family():
    """6 rank-2 projections on R^3 summing to 4 I  (complements of the
    icosahedron's 6 diagonal lines)."""
    phi = 0.5 * (1 + np.sqrt(5.0))
    us = [(0, 1, phi), (0, 1, -phi), (1, phi, 0),
          (1, -phi, 0), (phi, 0, 1), (-phi, 0, 1)]
    A = np.zeros((6, 3, 3))
    for k, u in enumerate(us):
        u = np.array(u, float)
        A[k] = np.eye(3) - np.outer(u, u) / (u @ u)
    return A


def rotated_pairs_family(m, rng):
    """2m rank-2 projections on R^4: m rotated complementary pairs,
    sum = m I_4.  (p,q,a,b) = (4, 2m, m, 2)."""
    A = np.zeros((2 * m, 4, 4))
    P0 = np.diag([1.0, 1.0, 0.0, 0.0])
    for j in range(m):
        X = rng.standard_normal((4, 4))
        Q, _ = np.linalg.qr(X)
        A[2 * j] = Q @ P0 @ Q.T
        A[2 * j + 1] = np.eye(4) - A[2 * j]
    return A


def proj_psd_contraction(M):
    w, V = np.linalg.eigh(0.5 * (M + M.T))
    return (V * np.clip(w, 0.0, 1.0)) @ V.T


def project_blocks_leq(M, blocks, a):
    """project each diagonal block onto {B <= (1/a) I} (eigenvalue clip up)."""
    M = M.copy()
    for bk in blocks:
        if not bk:
            continue
        B = M[np.ix_(bk, bk)]
        w, V = np.linalg.eigh(0.5 * (B + B.T))
        M[np.ix_(bk, bk)] = (V * np.minimum(w, 1.0 / a)) @ V.T
    return M


def feasible_Kclass(M, blocks, a, iters=400):
    for _ in range(iters):
        M = project_blocks_leq(proj_psd_contraction(M), blocks, a)
    return M


def kclass_residual(M, blocks, a):
    lo, hi, blk = class_report(M, blocks, a)
    return max(0.0, -lo, hi - 1.0, blk)


def set_blocks_eq(M, blocks, a):
    M = M.copy()
    for bk in blocks:
        M[np.ix_(bk, bk)] = np.eye(len(bk)) / a
    return M


def feasible_C(M, blocks, a, iters=400):
    for _ in range(iters):
        M = set_blocks_eq(proj_psd_contraction(M), blocks, a)
    return M


def build_zoo(rng, heavy=True):
    """list of dicts: name, K (np), blocks, a, b, kind, exactK (Fractions or
    None), p (target rank for Naimark kernels, else None)."""
    zoo = []

    def add(name, K, blocks, a, b, kind, exactK=None, p=None):
        zoo.append(dict(name=name, K=K, blocks=blocks, a=a, b=b, kind=kind,
                        exactK=exactK, p=p))

    # --- graphs (exact kernels)
    adj, p, q, a, b = subdivision_K4()
    KF, _ = graph_kernel(adj, p, q, a, b)
    add('S(K_4) graph (3,2)', frac_to_np(KF), uniform_blocks(q, b), a, b,
        'graph', exactK=KF, p=p)
    adj, p, q, a, b = Kmn(2, 5)
    KF, _ = graph_kernel(adj, p, q, a, b)
    add('K_{2,5} graph (5,2)', frac_to_np(KF), uniform_blocks(q, b), a, b,
        'graph', exactK=KF, p=p)
    adj = random_biregular(4, 6, 3, 2, rng)
    KF, _ = graph_kernel(adj, 4, 6, 3, 2)
    add('random biregular (3,2) p=4 q=6', frac_to_np(KF), uniform_blocks(6, 2),
        3, 2, 'graph', exactK=KF, p=4)
    adj, p, q, a, b = cube_design()
    KF, _ = graph_kernel(adj, p, q, a, b)
    add('cube design graph (4,3)', frac_to_np(KF), uniform_blocks(q, b), a, b,
        'graph', exactK=KF, p=p)

    # --- noncommutative Naimark kernels, b = 2
    A = icosahedral_family()
    add('icosahedral complements (3,6,4,2)', naimark_pi(A, 4, 2),
        uniform_blocks(6, 2), 4, 2, 'naimark', p=3)
    A = rotated_pairs_family(3, rng)
    add('rotated pairs (4,6,3,2)', naimark_pi(A, 3, 2),
        uniform_blocks(6, 2), 3, 2, 'naimark', p=4)
    A, res = build_tff(4, 8, 4, 2, rng)
    if res < 1e-10:
        add('random TFF (4,8,4,2)', naimark_pi(A, 4, 2),
            uniform_blocks(8, 2), 4, 2, 'naimark', p=4)
    A, res = build_tff(6, 9, 3, 2, rng)
    if res < 1e-10:
        add('random TFF (6,9,3,2)', naimark_pi(A, 3, 2),
            uniform_blocks(9, 2), 3, 2, 'naimark', p=6)
    if heavy:
        A, res = build_tff(6, 8, 4, 3, rng)
        if res < 1e-10:
            add('random TFF (6,8,4,3) b=3', naimark_pi(A, 4, 3),
                uniform_blocks(8, 3), 4, 3, 'naimark', p=6)

    # --- class (C): contraction, blocks exactly (1/a) I_2
    for (q, a) in [(6, 3), (8, 4)]:
        n = 2 * q
        blocks = uniform_blocks(q, 2)
        M = rng.standard_normal((n, n))
        Kc = feasible_C(0.3 * (M + M.T) + np.eye(n) / a, blocks, a)
        if kclass_residual(Kc, blocks, a) < 1e-8:
            add(f'class C random ({a},2) q={q}', Kc, blocks, a, 2, 'classC')

    # --- class K(a,b) proper: blocks strictly below (1/a) I, mixed sizes
    n = 11
    blocks = [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10]]
    M = rng.standard_normal((n, n))
    Kk = feasible_Kclass(0.4 * (M + M.T) + 0.2 * np.eye(n), blocks, 3)
    add('class K mixed sizes (3,2) q=6', Kk, blocks, 3, 2, 'classK')
    # scaled graph kernel (rational, strict blocks)
    adj, p, q, a, b = subdivision_K4()
    KF, _ = graph_kernel(adj, p, q, a, b)
    KFs = [[Fraction(2, 3) * x for x in row] for row in KF]
    add('(2/3) S(K_4) kernel (3,2)', frac_to_np(KFs), uniform_blocks(q, b),
        a, b, 'classK', exactK=KFs)
    return zoo


# ----------------------------------------------------------- validations
def validate_naimark(zoo):
    print('=' * 78)
    print('V1. N_K == y^{q-p} nu_G for graph kernels (exact), Naimark kernels')
    print('    are projections with blocks (1/a) I (float residuals)')
    from frac_naimark import GRAPHS
    for name, (adj, p, q, a, b) in [('S(K_4)', subdivision_K4()),
                                    ('K_{2,5}', Kmn(2, 5))]:
        KF, _ = graph_kernel(adj, p, q, a, b)
        c = N_coeffs_frac(KF, uniform_blocks(q, b), a)
        nu = nu_coeffs(adj, p, q)          # c[j] = coeff of y^j, length p+1
        tgt = [Fraction(0)] * (q + 1)      # high -> low, index m = y^{q-m}
        for j, co in enumerate(nu):        # y^{q-p} nu: coeff of y^{j + q - p}
            tgt[q - (j + q - p)] = Fraction(co)
        print(f"   {name}: exact match {c == tgt}")
    for z in zoo:
        if z['kind'] != 'naimark':
            continue
        K, blocks, a = z['K'], z['blocks'], z['a']
        n = K.shape[0]
        w = np.linalg.eigvalsh(K)
        projres = np.abs(K @ K - K).max()
        lo, hi, blk = class_report(K, blocks, a)
        rk = int((w > 0.5).sum())
        print(f"   {z['name']}: rank {rk} (want {z['p']})  proj residual "
              f"{projres:.1e}  block residual {max(blk, 0):.1e}")


def validate_recursion(zoo, rng):
    print('=' * 78)
    print('V2. slot and block identities on every zoo member (float),')
    print('    plus exact on S(K_4) and on the scaled kernel')
    for z in zoo:
        K, blocks, a = z['K'], z['blocks'], z['a']
        q = len(blocks)
        N = N_coeffs(K, blocks, a)
        k0 = next(j for j, bk in enumerate(blocks) if bk)
        e = blocks[k0][0]
        # slot identity
        rhs = N_coeffs(K, del_slot(blocks, e), a).copy()
        Ke = schur_np(K, e)
        t2 = N_coeffs(Ke, del_block(blocks, k0), a)
        rhs[1:] -= a * K[e, e] * t2
        err_slot = np.abs(N - rhs).max() / max(1.0, np.abs(N).max())
        # block identity
        rhs2 = np.zeros(q + 1)
        Nc = N_coeffs(K, del_block(blocks, k0), a)
        rhs2[:q] += Nc
        for e2 in blocks[k0]:
            rhs2[1:] -= a * K[e2, e2] * N_coeffs(schur_np(K, e2),
                                                 del_block(blocks, k0), a)
        err_blk = np.abs(N - rhs2).max() / max(1.0, np.abs(N).max())
        # Schur complement stays in class
        lo, hi, blk = class_report(schur_np(K, e), del_block(blocks, k0), a)
        ok = (lo > -1e-9) and (hi < 1 + 1e-9) and (blk < 1e-9)
        print(f"   {z['name']}: slot {err_slot:.1e}  block {err_blk:.1e}  "
              f"Schur-in-class {ok}")
    # exact slot identity on S(K_4)
    for z in zoo:
        if z['exactK'] is None or 'S(K_4)' not in z['name']:
            continue
        KF, blocks, a = z['exactK'], z['blocks'], z['a']
        q = len(blocks)
        N = N_coeffs_frac(KF, blocks, a)
        e = blocks[0][0]
        rhs = N_coeffs_frac(KF, del_slot(blocks, e), a)
        KeF = schur_frac(KF, e)
        t2 = N_coeffs_frac(KeF, del_block(blocks, 0), a)
        ce = KF[e][e]
        rhs = [rhs[m] - (Fraction(a) * ce * t2[m - 1] if m >= 1 else 0)
               for m in range(q + 1)]
        print(f"   {z['name']}: EXACT slot identity {N == rhs}")


def validate_border(zoo, rng):
    print('=' * 78)
    print('V3. border identity a N_{M + ww^T} = (a - y) N_M + N_{M~0}')
    for z in zoo[:6]:
        K, blocks, a = z['K'], z['blocks'], z['a']
        n = K.shape[0]
        w = 0.3 * rng.standard_normal(n)
        M = K
        Mw = M + np.outer(w, w)
        NM = N_coeffs(M, blocks, a)
        NMw = N_coeffs(Mw, blocks, a)
        M0 = border_w(M, w)
        blocks0 = [[0]] + [[x + 1 for x in bk] for bk in blocks]
        NM0 = N_coeffs(M0, blocks0, a)
        q = len(blocks)
        # a NMw  vs  a*NM - y*NM + NM0   (degree q+1, high->low)
        lhs = np.concatenate([[0.0], a * NMw])
        rhs = np.concatenate([[0.0], a * NM]) + NM0
        rhs -= np.concatenate([NM, [0.0]])           # -y * NM
        err = np.abs(lhs - rhs).max() / max(1.0, np.abs(lhs).max())
        print(f"   {z['name']}: border identity err {err:.1e}")


def validate_tree(rng):
    print('=' * 78)
    print('V4. tree normalisation: kernel B ratios == scalar cavity recursion')
    print('    (exact, Fraction arithmetic, y rational), and A_h -> A+')
    for (a, b, plevels, y) in [(3, 2, 1, Fraction(6)), (3, 2, 2, Fraction(6)),
                               (4, 2, 1, Fraction(8)), (4, 3, 1, Fraction(9))]:
        adj, p, q = biregular_tree(a, b, plevels)
        KF, _ = graph_kernel_any(adj, p, q, a)
        blocks = blocks_from_adj(adj, p, q)
        N = N_coeffs_frac(KF, blocks, a)
        Nroot = N_coeffs_frac(KF, del_block(blocks, 0), a)
        Bk = evalf(N, y) / evalf(Nroot, y)
        # scalar prediction: root block has b P-children, each a full
        # P-branch of height plevels-? -- compute via recursion on the tree
        Aval = tree_A_exact(adj, p, q, a, y)
        pred = y - sum(y / Aval[i] for i in range(p) if (adj[i] >> 0) & 1)
        match = (Bk == pred)
        # numeric fixed point
        yf = float(y)
        Ah, Rh = tree_AR_sequence(yf, a, b, 60)
        print(f"   (a,b)=({a},{b}) plevels={plevels} p={p} q={q}: "
              f"B_root == y - sum y/A_i : {match}   "
              f"A_60={Ah[-1]:.8f} vs A+={A_plus(yf, a, b):.8f}")


def blocks_from_adj(adj, p, q):
    slots = []
    for k in range(q):
        nb = [i for i in range(p) if (adj[i] >> k) & 1]
        slots += [(k, i) for i in nb]
    blocks = [[] for _ in range(q)]
    for x, (k, i) in enumerate(slots):
        blocks[k].append(x)
    return blocks


def graph_kernel_any(adj, p, q, a):
    """graph kernel for arbitrary bipartite adj (degrees need not be
    regular): K[(k,i),(k',i')] = (1/a) [i = i']."""
    slots = []
    for k in range(q):
        nb = [i for i in range(p) if (adj[i] >> k) & 1]
        slots += [(k, i) for i in nb]
    n = len(slots)
    K = [[Fraction(1, a) if slots[x][1] == slots[y][1] else Fraction(0)
          for y in range(n)] for x in range(n)]
    return K, slots


def tree_A_exact(adj, p, q, a, y):
    """A_i = nu_{H}/nu_{H-i} for the branch hanging at P-vertex i in the tree
    with the root Q-vertex 0 removed; exact via matching polynomials of the
    subtree.  Uses recursion A_i = y - sum_{k child} y / B_k, B_k = block
    ratio... implemented directly by nu on vertex sets (tree is small)."""
    # children structure: root q-vertex 0; P-vertex i's q-children = its
    # neighbours other than parent.  Work recursively with nu ratios.
    import functools

    qadj = [[i for i in range(p) if (adj[i] >> k) & 1] for k in range(q)]
    padj = [[k for k in range(q) if (adj[i] >> k) & 1] for i in range(p)]

    def A_of(i, parent_q):
        val = y
        for k in padj[i]:
            if k == parent_q:
                continue
            s = 0 * y
            for j in qadj[k]:
                if j != i:
                    s += 1 / A_of(j, k)
            val -= 1 / (1 - s)
        return val

    return {i: A_of(i, 0) for i in range(p) if (adj[i] >> 0) & 1}


def evalf(c, y):
    v = 0 * y
    for x in c:
        v = v * y + x
    return v


def validate_roots(zoo):
    print('=' * 78)
    print('V5. top roots of the zoo vs the upper edge (C-upper sanity)')
    for z in zoo:
        K, blocks, a, b = z['K'], z['blocks'], z['a'], z['b']
        c = N_coeffs(K, blocks, a)
        tr, im = top_root(c)
        lo, hi = band_edges(a, b)
        print(f"   {z['name']}: top root {tr:.6f}  edge {hi:.6f}  "
              f"margin {hi - tr:+.6f}  max|Im| {im:.1e}"
              f"{'   *** ABOVE EDGE ***' if tr > hi + 1e-8 else ''}")


if __name__ == '__main__':
    rng = np.random.default_rng(20260801)
    zoo = build_zoo(rng)
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', '1'):
        validate_naimark(zoo)
    if which in ('all', '2'):
        validate_recursion(zoo, rng)
    if which in ('all', '3'):
        validate_border(zoo, rng)
    if which in ('all', '4'):
        validate_tree(rng)
    if which in ('all', '5'):
        validate_roots(zoo)
