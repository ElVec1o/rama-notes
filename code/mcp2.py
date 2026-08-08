"""Mixed characteristic polynomial, complex-Hermitian capable + generic family
parametrisations for the search."""
import numpy as np
from math import comb
from mixed_char_poly import _popcounts


def mcp(A):
    """A: (q,p,p) real symmetric or complex Hermitian. Returns c[0..p] real,
    mu(y) = sum_m c[m] y^(p-m)."""
    A = np.asarray(A)
    q, p, _ = A.shape
    N = 1 << q
    S = np.zeros((N, p, p), dtype=A.dtype)
    for mask in range(1, N):
        lb = mask & (-mask)
        S[mask] = S[mask ^ lb] + A[lb.bit_length() - 1]
    eig = np.linalg.eigvalsh(S)
    E = np.zeros((N, p + 1))
    E[:, 0] = 1.0
    for j in range(p):
        lam = eig[:, j][:, None]
        E[:, 1:] = E[:, 1:] + lam * E[:, :-1]
    pc = _popcounts(q)
    Sr = np.zeros((q + 1, p + 1))
    for m in range(p + 1):
        Sr[:, m] = np.bincount(pc, weights=E[:, m], minlength=q + 1)
    mu = np.zeros(p + 1)
    for r in range(q + 1):
        sgn = -1.0 if (r & 1) else 1.0
        for m in range(r, p + 1):
            mu[m] += sgn * comb(q - r, m - r) * Sr[r, m]
    return mu


def roots(A):
    return np.sort(np.roots(mcp(A)).real)


# ---------------------------------------------------------------- families
def _isqrt_sym(S):
    w, V = np.linalg.eigh(S)
    return (V * (w ** -0.5)) @ V.conj().T


def psd_from_X(X, a):
    """FULL parametrisation of {rank-b PSD, sum = aI}: X is (q,p,b) arbitrary,
    A_k = a S^{-1/2} X_k X_k^* S^{-1/2},  S = sum X_k X_k^*.
    Surjective: if {A_k} is feasible then X_k = a^{-1/2}(a factor of A_k) works."""
    G = X @ np.swapaxes(X.conj(), 1, 2)
    Sm = _isqrt_sym(G.sum(axis=0))
    return a * (Sm @ G @ Sm)


def proj_from_X(X):
    """rank-b orthogonal projections from (q,p,b) X via QR."""
    Q, _ = np.linalg.qr(X)
    return Q @ np.swapaxes(Q.conj(), 1, 2)


def restore_proj(A, q, p, a, b, iters=600, tol=1e-14):
    I = np.eye(p)
    for it in range(iters):
        M = A + (a * I - A.sum(axis=0)) / q
        M = 0.5 * (M + np.swapaxes(M.conj(), 1, 2))
        w, V = np.linalg.eigh(M)
        U = V[:, :, -b:]
        A = U @ np.swapaxes(U.conj(), 1, 2)
        if it % 25 == 24:
            if resid(A, a) < tol:
                break
    return A, resid(A, a)


def resid(A, a):
    p = A.shape[1]
    r1 = np.linalg.norm(A.sum(axis=0) - a * np.eye(p))
    r2 = np.max(np.abs(A @ A - A))
    return max(r1, r2)


def rand_X(q, p, b, rng, complex_=False):
    X = rng.standard_normal((q, p, b))
    if complex_:
        X = X + 1j * rng.standard_normal((q, p, b))
    return X
