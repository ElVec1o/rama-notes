"""A second, INDEPENDENT algorithm for mu[P_1..P_q] in the projection case,
via the Naimark dilation.  Serves both as a cross-check and as a clean
restatement of Conjecture X.

Setup.  P_k = V_k V_k^T, V_k p x b with V_k^T V_k = I_b, sum_k P_k = a I_p.
Put U = [V_1^T; ...; V_q^T]/sqrt(a)  (an n x p isometry, n = qb = pa) and
Pi = U U^T, the rank-p orthogonal projection on R^n whose q diagonal b x b
blocks all equal (1/a) I_b.  Then, using det(yI_p + U^T D U) =
y^(p-n) det(y I_n + D Pi) with D = blockdiag(a z_k I_b),

    mu(y) = sum_{T} (-a)^{|T|} y^{p-|T|} det(Pi[T,T]),

the sum over subsets T of [n] = [q] x [b] meeting each block at most once
("transversals").  In the graph case Pi = (1/a)*[same vertex] and
det(Pi[T,T]) = a^{-|T|} * [T is a matching], recovering nu_G exactly.

So CONJECTURE X (projection case) is equivalent to:

  Let Pi be a rank-p orthogonal projection on R^(pa) whose q = pa/b diagonal
  b x b blocks all equal (1/a) I_b.  Then every root of
      sum_T (-a)^{|T|} y^{p-|T|} det(Pi[T,T])   (T transversal)
  lies in [(sqrt(a-1)-sqrt(b-1))^2, (sqrt(a-1)+sqrt(b-1))^2].
"""
import numpy as np
from itertools import combinations, product
from mcp2 import mcp
from mixed_char_poly import band
from tff import build_tff, random_biregular, graph_to_projections


def naimark_pi(A, a, b):
    """A: (q,p,p) rank-b projections summing to aI -> Pi (n x n), n = q*b."""
    q, p, _ = A.shape
    U = np.zeros((q * b, p))
    for k in range(q):
        w, V = np.linalg.eigh(A[k])
        Vk = V[:, -b:]                       # p x b, orthonormal columns
        U[k * b:(k + 1) * b, :] = Vk.T / np.sqrt(a)
    return U @ U.T


def mu_from_pi(Pi, p, q, b, a):
    """mu(y) = sum over transversals T of (-a)^|T| y^(p-|T|) det(Pi[T,T])."""
    c = np.zeros(p + 1)
    c[0] = 1.0
    for m in range(1, p + 1):
        tot = 0.0
        for blocks in combinations(range(q), m):
            for choice in product(range(b), repeat=m):
                T = [blocks[i] * b + choice[i] for i in range(m)]
                tot += np.linalg.det(Pi[np.ix_(T, T)])
        c[m] = ((-a) ** m) * tot
    return c


if __name__ == '__main__':
    rng = np.random.default_rng(1234)
    print("cross-check: subset formula vs Naimark/transversal formula")
    for (p, q, a, b) in [(4, 6, 3, 2), (3, 6, 4, 2), (6, 9, 3, 2), (6, 8, 4, 3),
                         (4, 8, 4, 2)]:
        # random tight fusion frame
        A, res = build_tff(p, q, a, b, rng)
        Pi = naimark_pi(A, a, b)
        blk = max(np.linalg.norm(Pi[k*b:(k+1)*b, k*b:(k+1)*b] - np.eye(b)/a)
                  for k in range(q))
        c1, c2 = mcp(A), mu_from_pi(Pi, p, q, b, a)
        e1 = np.max(np.abs(c1 - c2)) / np.max(np.abs(c1))
        # graph
        adj = random_biregular(p, q, a, b, rng)
        G = graph_to_projections(adj, p, q)
        PiG = naimark_pi(G, a, b)
        c3, c4 = mcp(G), mu_from_pi(PiG, p, q, b, a)
        e2 = np.max(np.abs(c3 - c4)) / np.max(np.abs(c3))
        print(f"  p={p} q={q} (a,b)=({a},{b}): feas={res:.1e}  "
              f"Pi rank={np.linalg.matrix_rank(Pi)} (want {p})  "
              f"diag-block err={blk:.1e}  relerr TFF={e1:.2e}  relerr graph={e2:.2e}")
