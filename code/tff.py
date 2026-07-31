"""Generation of families A_1..A_q of rank-b PSD matrices on R^p with
sum_k A_k = a I  (requires q*b = p*a), in three classes:

  CLASS P  : exact rank-b orthogonal projections (tight fusion frames)
  CLASS G   : the diagonal 0/1 ones = biregular bipartite graphs
  CLASS PSD : rank-b PSD, sum = aI, but not projections
              (A_k = a S^{-1/2} Q_k S^{-1/2},  S = sum Q_k)

All routines act on a (q,p,p) numpy array and use batched linear algebra.
"""
import numpy as np


# ----------------------------------------------------------------------
def rand_stiefel(p, b, rng):
    X = rng.standard_normal((p, b))
    Q, R = np.linalg.qr(X)
    return Q * np.sign(np.diag(R))


def rand_projections(q, p, b, rng):
    X = rng.standard_normal((q, p, b))
    Q, _ = np.linalg.qr(X)
    return Q @ np.swapaxes(Q, 1, 2)


def proj_rank_b(A, b):
    """Batched nearest rank-b orthogonal projection (A is (q,p,p) or (p,p))."""
    single = (A.ndim == 2)
    if single:
        A = A[None]
    A = 0.5 * (A + np.swapaxes(A, 1, 2))
    w, V = np.linalg.eigh(A)
    U = V[:, :, -b:]
    out = U @ np.swapaxes(U, 1, 2)
    return out[0] if single else out


def tff_residual(A, a):
    p = A.shape[1]
    r1 = np.linalg.norm(A.sum(axis=0) - a * np.eye(p))
    r2 = np.max(np.linalg.norm(A @ A - A, axis=(1, 2)))
    return max(r1, r2)


def restore(A, q, p, a, b, iters=800, tol=1e-14):
    """Alternating projections onto {rank-b projections} and {sum = aI}."""
    I = np.eye(p)
    for it in range(iters):
        corr = (a * I - A.sum(axis=0)) / q
        A = proj_rank_b(A + corr, b)
        if it % 25 == 24:
            if tff_residual(A, a) < tol:
                break
    return A, tff_residual(A, a)


def build_tff(p, q, a, b, rng, iters=800, tol=1e-14):
    assert q * b == p * a
    A = rand_projections(q, p, b, rng)
    return restore(A, q, p, a, b, iters, tol)


def build_psd_family(p, q, a, b, rng, A=None):
    """rank-b PSD, sum = aI, generally NOT projections."""
    if A is None:
        A = rand_projections(q, p, b, rng)
    S = A.sum(axis=0)
    w, V = np.linalg.eigh(S)
    Sm = V @ np.diag(w ** -0.5) @ V.T
    return a * (Sm @ A @ Sm)


# ----------------------------------------------------------------------
# biregular bipartite graphs (diagonal class)
# ----------------------------------------------------------------------
def random_biregular(p, q, a, b, rng, tries=6000):
    """Random (a,b)-biregular bipartite graph via configuration model +
    rejection on simplicity."""
    assert q * b == p * a
    stubsP = np.repeat(np.arange(p), a)
    for _ in range(tries):
        perm = rng.permutation(q * b)
        stubsQ = np.repeat(np.arange(q), b)[perm]
        seen = set(zip(stubsP.tolist(), stubsQ.tolist()))
        if len(seen) == q * b:
            adj = [0] * p
            for i, k in seen:
                adj[i] |= 1 << k
            return adj
    return None


def graph_to_projections(adj, p, q):
    B = np.zeros((q, p, p))
    for k in range(q):
        for i in range(p):
            if (adj[i] >> k) & 1:
                B[k, i, i] = 1.0
    return B


def commutativity(A):
    """max_{j<k} ||[A_j,A_k]||_F / ||A_j|| ||A_k||  -- 0 iff simultaneously
    diagonalisable (i.e. the family is a graph family up to rotation)."""
    q = A.shape[0]
    worst = 0.0
    for j in range(q):
        for k in range(j + 1, q):
            C = A[j] @ A[k] - A[k] @ A[j]
            worst = max(worst, np.linalg.norm(C))
    return worst
