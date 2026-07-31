"""ineq2_class.py -- is there an inductively closed class of kernels on which
INEQ-2 could be proved by a Heilmann-Lieb style induction?

THE OBJECT.  For a Hermitian PSD kernel K on 2q slots split into q blocks of size 2,
put   E_r(K) = sum_{|T|=r} det K[B_T]   and

    N_K(x) = sum_r (-1)^r a^{2r} E_r(K) x^{-2r} ,      equivalently
    n_K(u) = sum_r (-1)^r a^{2r} E_r(K) u^{q-r}  with u = x^2.

For K = Pi (the Naimark kernel of a rank-2 tight fusion frame) we proved
N_Pi(x) = mu(x+a)/x^p, so INEQ-2 <=> N_Pi(x) > 0 for x > 2 sqrt(a-1).

THE RECURSION (exact, from the Schur complement / block cofactor expansion):

    E_r(K) = E_r(K \\ k) + det(K[B_k]) E_{r-1}(K / B_k)
    N_K(x) = N_{K\\k}(x) - a^2 det(K[B_k]) x^{-2} N_{K/B_k}(x).

This is EXACTLY the Heilmann-Lieb edge recursion m_r(G) = m_r(G-e) + m_{r-1}(G-u-v).

THE CLASS.   C_a := { K : 0 <= K <= I,  K[B_j,B_j] <= (1/a) I_2  for every j }.
  * every Naimark kernel Pi of a rank-2 family with sum P_k = aI lies in C_a
    (blocks are exactly (1/a)I_2);
  * C_a is CLOSED under both operations: deleting a block (principal submatrix)
    and Schur-complementing a block (K/B_k <= K\\k, so blocks only shrink);
  * on C_a one still has a^2 det K[B_k] <= 1 and (from K^2 <= K)
    sum_{j != k} ||K[B_j,B_k]||_F^2 <= 2q(a-1)/a^2, hence the same M_2 bound.
  * PARAMETRISATION (exact and surjective):  K = Z*Z with ||Z||_op <= 1 and
    ||Z_j||_op <= 1/sqrt(a) for each 2-column block Z_j.  Projections are the
    case ZZ* = I_p and Z_j*Z_j = (1/a)I.

QUESTION.  is  sup{ largest root of n_K : K in C_a }  equal to  4(a-1)  (=(2sqrt(a-1))^2,
i.e. INEQ-2 would follow by induction on q), or larger?  This file answers it.
"""
import sys
import numpy as np
from itertools import combinations

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')


def E_all(K, q):
    """E_r(K) for r = 0..q."""
    E = np.zeros(q + 1)
    E[0] = 1.0
    for r in range(1, q + 1):
        tot = 0.0
        for T in combinations(range(q), r):
            idx = [2 * k + j for k in T for j in (0, 1)]
            tot += np.linalg.det(K[np.ix_(idx, idx)]).real
        E[r] = tot
    return E


def umax(K, q, a):
    """largest real root of n_K(u) = sum_r (-1)^r a^{2r} E_r u^{q-r}   (u = x^2)."""
    E = E_all(K, q)
    co = np.array([(-1.0) ** r * a ** (2 * r) * E[r] for r in range(q + 1)])
    rr = np.roots(co)
    rr = rr[np.abs(rr.imag) < 1e-7].real
    return float(rr.max()) if len(rr) else 0.0


def feasible(Z, a, iters=60):
    """project Z onto {||Z||<=1, ||Z_j||<=1/sqrt(a)} (alternating, converges)."""
    r = 1.0 / np.sqrt(a)
    for _ in range(iters):
        for j in range(Z.shape[1] // 2):
            B = Z[:, 2 * j:2 * j + 2]
            s = np.linalg.norm(B, 2)
            if s > r:
                Z[:, 2 * j:2 * j + 2] = B * (r / s)
        s = np.linalg.norm(Z, 2)
        if s > 1:
            Z = Z / s
        else:
            break
    return Z


def check_feasible(K, a, q, tol=1e-8):
    w = np.linalg.eigvalsh(K)
    ok1 = w.min() > -tol and w.max() < 1 + tol
    ok2 = all(np.linalg.eigvalsh(K[2 * j:2 * j + 2, 2 * j:2 * j + 2]).max()
              < 1.0 / a + tol for j in range(q))
    return ok1 and ok2


def seeds(q, a, rng):
    """good starting points inside C_a: Naimark kernels of projection families,
    of graphs with min degree >= a, and random feasible Z."""
    from mcp2 import restore_proj, rand_X, proj_from_X
    from dpp_rep import naimark_slots
    out = []
    for p in range(2, 2 * q + 1):
        if p * a != 2 * q:
            continue
        for sd in range(3):
            X = rand_X(q, p, 2, rng)
            P, res = restore_proj(proj_from_X(X), q, p, a, 2, iters=5000, tol=1e-14)
            if res < 1e-11:
                out.append(naimark_slots(P, a, 2)[1])
    for _ in range(4):
        Z = feasible(rng.standard_normal((2 * q, 2 * q)), a)
        out.append(Z.conj().T @ Z)
    return out


def climb(K0, q, a, rng, steps=1500, eps0=0.25):
    """hill-climb u_max inside C_a starting from K0, moving in the Z-factor."""
    w, V = np.linalg.eigh(K0)
    w = np.clip(w, 0, None)
    Z = (V * np.sqrt(w)).conj().T          # K0 = Z*Z
    Z = feasible(Z, a)
    K = Z.conj().T @ Z
    cur, eps = umax(K, q, a), eps0
    for t in range(steps):
        Zc = feasible(Z + eps * rng.standard_normal(Z.shape), a)
        Kc = Zc.conj().T @ Zc
        v = umax(Kc, q, a)
        if v > cur:
            cur, Z, K = v, Zc, Kc
        else:
            eps *= 0.997
        if eps < 1e-5:
            break
    return cur, K


def search(q, a, rng, steps=900, restarts=6, m=None):
    """maximise the largest root of n_K over K in C_a."""
    m = 2 * q if m is None else m
    best, bestK = -1.0, None
    for _ in range(restarts):
        Z = feasible(rng.standard_normal((m, 2 * q)), a)
        K = Z.conj().T @ Z
        cur = umax(K, q, a)
        eps = 0.5
        for t in range(steps):
            Zc = feasible(Z + eps * rng.standard_normal(Z.shape), a)
            Kc = Zc.conj().T @ Zc
            v = umax(Kc, q, a)
            if v > cur:
                cur, Z, K = v, Zc, Kc
            else:
                eps *= 0.995
            if eps < 1e-5:
                break
        if cur > best:
            best, bestK = cur, K
    return best, bestK


def reachable_test(a, p, q, rng, trials=200):
    """Take a genuine projection kernel Pi and apply random sequences of
    (delete block) / (Schur-complement block); check the root bound survives."""
    from mcp2 import restore_proj, rand_X, proj_from_X
    from dpp_rep import naimark_slots
    worst = -1.0
    for _ in range(6):
        X = rand_X(q, p, 2, rng)
        P, res = restore_proj(proj_from_X(X), q, p, a, 2, iters=4000, tol=1e-14)
        if res > 1e-11:
            continue
        U, Pi = naimark_slots(P, a, 2)
        for _ in range(trials):
            K, blocks = Pi.copy(), list(range(q))
            while len(blocks) > 1:
                k = int(rng.integers(len(blocks)))
                idx = [2 * k, 2 * k + 1]
                rest = [i for i in range(2 * len(blocks)) if i not in idx]
                if rng.random() < 0.5:
                    K = K[np.ix_(rest, rest)]
                else:
                    A = K[np.ix_(idx, idx)]
                    if abs(np.linalg.det(A)) < 1e-12:
                        K = K[np.ix_(rest, rest)]
                    else:
                        K = (K[np.ix_(rest, rest)]
                             - K[np.ix_(rest, idx)] @ np.linalg.solve(A, K[np.ix_(idx, rest)]))
                blocks.pop(k)
                qq = len(blocks)
                if not check_feasible(K, a, qq):
                    print("      *** class NOT closed (numerical) at q =", qq)
                worst = max(worst, umax(K, qq, a))
    return worst


def focused(q, a, rng, steps=1500):
    best, bestsrc = -1.0, ''
    for i, K0 in enumerate(seeds(q, a, rng)):
        u0 = umax(K0, q, a)
        u1, _ = climb(K0, q, a, rng, steps=steps)
        if u1 > best:
            best, bestsrc = u1, f'seed#{i} (u0={u0:.4f})'
    return best, bestsrc


def graph_kernel_deg(adj, pv):
    """Naimark kernel of a graph with degrees d_v: block j = edge (u,v),
    K[B_j] = diag(1/d_u, 1/d_v).  Slots (edge, endpoint)."""
    edges = [(u, v) for u in range(pv) for v in range(u + 1, pv)
             if (adj[u] >> v) & 1]
    q = len(edges)
    d = [bin(adj[u]).count('1') for u in range(pv)]
    U = np.zeros((pv, 2 * q))
    for k, (u, v) in enumerate(edges):
        U[u, 2 * k] = 1.0 / np.sqrt(d[u])
        U[v, 2 * k + 1] = 1.0 / np.sqrt(d[v])
    return U.T @ U, q, edges, d


if __name__ == '__main__':
    import networkx as nx
    rng = np.random.default_rng(31415)

    print("=" * 92)
    print("T1  CLOSURE.  C_a = {0<=K<=I, K[B_j]<=(1/a)I} is closed under the two")
    print("    recursion moves.  Start from a real projection kernel Pi and apply random")
    print("    sequences of (delete block)/(Schur complement); check feasibility and the")
    print("    root bound u_max <= 4(a-1) at every step.")
    print("=" * 92)
    for (p, q, a) in [(4, 6, 3), (6, 9, 3), (4, 8, 4), (6, 12, 4)]:
        w = reachable_test(a, p, q, rng, trials=40)
        print(f"  (p,q,a)=({p},{q},{a})  worst u_max over reachable kernels = {w:.6f}   "
              f"4(a-1) = {4*(a-1)}   {'OK' if w <= 4*(a-1)+1e-6 else '*** EXCEEDS'}",
              flush=True)

    print()
    print("=" * 92)
    print("T2  CALIBRATION on the COMMUTATIVE part of C_a.  The kernel of a d-regular")
    print("    graph lies in C_a exactly when d >= a, and then (exactly)")
    print("        u_max = (a^2/d^2) * (largest root of the matching polynomial)^2")
    print("               <= 4 a^2 (d-1)/d^2,  maximised over d>=a at d=a, value 4(a-1).")
    print("    So sup over the commutative part of C_a is EXACTLY 4(a-1): C_a is")
    print("    calibrated, neither too large nor too small, on graphs.")
    print("=" * 92)
    from ineq2_moments import matching_numbers
    print(f"  {'a':>3} {'d':>3} {'p':>4} {'graph':>18} {'u_max':>11} "
          f"{'4a^2(d-1)/d^2':>14} {'4(a-1)':>8}")
    for a in (3, 4):
        for d in range(a, a + 4):
            for pv in range(d + 1, 13):
                if (pv * d) % 2 or pv <= d or pv * d // 2 > 12:
                    continue
                try:
                    G = nx.random_regular_graph(d, pv, seed=7)
                except Exception:
                    continue
                adj = [0] * pv
                for u, v in G.edges():
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
                K, q, edges, degs = graph_kernel_deg(adj, pv)
                u = umax(K, q, a)
                M = matching_numbers(tuple(adj), pv)
                co = np.zeros(pv + 1)
                for r, m in enumerate(M):
                    co[2 * r] = (-1) ** r * float(m)
                xm = np.sort(np.roots(co).real)[-1]
                pred = (a ** 2 / d ** 2) * xm ** 2
                assert abs(u - pred) < 1e-6 * max(1, abs(u)), (u, pred)
                print(f"  {a:>3} {d:>3} {pv:>4} {'random '+str(d)+'-reg (q='+str(q)+')':>18} "
                      f"{u:>11.6f} {4*a**2*(d-1)/d**2:>14.6f} {4*(a-1):>8}", flush=True)
        print()

    print("=" * 92)
    print("T3  random search inside C_a (unstructured), as a sanity check that nothing")
    print("    cheap violates u_max <= 4(a-1).")
    print("=" * 92)
    for (q, a) in [(4, 3), (6, 3), (8, 3), (6, 4), (8, 4)]:
        u, _ = search(q, a, rng, steps=600, restarts=6)
        print(f"  a={a} q={q}:  best random-search u_max = {u:.6f}  vs 4(a-1) = {4*(a-1)}"
              f"   {'OK' if u <= 4*(a-1)+1e-6 else '*** EXCEEDS'}", flush=True)
