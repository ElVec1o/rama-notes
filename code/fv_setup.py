r"""fv_setup.py -- FRACTIONAL VERTEX SYSTEMS.  Builders + step 1 + step 2.

Objects
-------
family : q rank-2 orthogonal projections P_k on R^p, sum_k P_k = a I_p, 2q = pa.
U      : p x 2q, rows orthonormal (U U^T = I_p), block k = W_k/sqrt(a).
Pi     : U^T U, rank-p orthogonal projection on R^(2q), diagonal 2x2 blocks I_2/a.

CENTRAL OBSERVATION (verified below).  The rows u_1..u_p of U are an orthonormal
basis of range(Pi), and EVERY orthonormal basis of range(Pi) is the set of rows
of O U for some O in O(p).  So

    { fractional vertex systems }  ==  { orthonormal bases of R^p },

and "deleting vertex i" = compressing the whole family to e_i^perp.

Canonical choice: maximise  Phi(basis) = sum_{i,k} <e_i,P_k e_i>^2   (equivalently
minimise sum_k ||offdiag P_k||_F^2 = 2q - Phi).  Phi <= p a always, with equality
iff all <e_i,P_k e_i> in {0,1} iff the P_k are simultaneously diagonal.
"""
import numpy as np
from itertools import combinations

# ---------------------------------------------------------------- families


def family_from_graph(edges, p):
    """P_k = diag(indicator of endpoints of edge k).  Commuting."""
    Ps = []
    for (u, v) in edges:
        P = np.zeros((p, p))
        P[u, u] = 1.0
        P[v, v] = 1.0
        Ps.append(P)
    return np.array(Ps)


def K4():
    return family_from_graph(list(combinations(range(4), 2)), 4), 4, 3


def K33():
    e = [(i, 3 + j) for i in range(3) for j in range(3)]
    return family_from_graph(e, 6), 6, 3


def cube():
    e = []
    for x in range(8):
        for b in range(3):
            y = x ^ (1 << b)
            if x < y:
                e.append((x, y))
    return family_from_graph(e, 8), 8, 3


def petersen():
    out = [(i, (i + 1) % 5) for i in range(5)]
    inn = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    spk = [(i, 5 + i) for i in range(5)]
    return family_from_graph(out + inn + spk, 10), 10, 3


# -------------------------------------------------- circulant (noncommuting)
def circulant_Pi(n, S):
    """Pi = (1/n) sum_{f in S} real rank-<=2 Fourier projector; circulant."""
    idx = np.arange(n)
    D = idx[:, None] - idx[None, :]
    Pi = np.zeros((n, n))
    for f in S:
        Pi += np.cos(2 * np.pi * f * D / n)
    return Pi / n


def family_circulant(n, a, S, pairing='half'):
    """Slots paired as (k, k+q) [pairing='half'].  Requires sum_{f in S}(-1)^f=0
    so that the 2x2 diagonal blocks are exactly I_2/a."""
    q = n // 2
    p = n // a
    assert len(S) == p and p * a == n
    Pi = circulant_Pi(n, S)
    if pairing == 'half':
        order = []
        for k in range(q):
            order += [k, k + q]
    else:
        order = list(range(n))
    perm = np.array(order)
    Pi = Pi[np.ix_(perm, perm)]
    w, V = np.linalg.eigh(Pi)
    U = V[:, -p:].T                      # p x n, rows orthonormal
    Ps = np.array([a * U[:, 2 * k:2 * k + 2] @ U[:, 2 * k:2 * k + 2].T
                   for k in range(q)])
    return Ps, p, a, Pi, U


def family_random(p, a, seed=0, iters=4000):
    """Alternating projections: rank-p projection on R^(2q) with 2x2 diagonal
    blocks I_2/a.  Generically noncommuting."""
    rng = np.random.default_rng(seed)
    assert (p * a) % 2 == 0
    q = p * a // 2
    n = 2 * q
    X = rng.standard_normal((n, n))
    Pi = X + X.T
    for _ in range(iters):
        w, V = np.linalg.eigh(Pi)
        Pi = V[:, -p:] @ V[:, -p:].T                  # nearest rank-p projection
        err = 0.0
        for k in range(q):
            B = Pi[2 * k:2 * k + 2, 2 * k:2 * k + 2]
            err = max(err, np.abs(B - np.eye(2) / a).max())
            Pi[2 * k:2 * k + 2, 2 * k:2 * k + 2] = np.eye(2) / a   # affine proj
        if err < 1e-13:
            break
    w, V = np.linalg.eigh(Pi)
    U = V[:, -p:].T
    Ps = np.array([a * U[:, 2 * k:2 * k + 2] @ U[:, 2 * k:2 * k + 2].T
                   for k in range(q)])
    return Ps, p, a, Pi, U, err


# ------------------------------------------------------------ Pi from family
def naimark(Ps, a):
    q, p, _ = Ps.shape
    U = np.zeros((p, 2 * q))
    for k in range(q):
        w, V = np.linalg.eigh(Ps[k])
        U[:, 2 * k:2 * k + 2] = V[:, -2:] / np.sqrt(a)
    return U, U.T @ U


def check_family(Ps, p, a):
    q = Ps.shape[0]
    d = dict(
        proj=max(np.abs(P @ P - P).max() for P in Ps),
        rank2=max(abs(np.trace(P) - 2) for P in Ps),
        sum=np.abs(sum(Ps) - a * np.eye(p)).max(),
        comm=max(np.abs(Ps[j] @ Ps[k] - Ps[k] @ Ps[j]).max()
                 for j in range(q) for k in range(j)),
    )
    return d


# --------------------------------------------- step 1: the vertex partition
def vertex_partition_report(Ps, p, a, U):
    """In a basis where the P_k are diagonal, u_i (row i of U) has support of
    size a inside the a blocks containing i, and Pi restricted to that support
    is (1/a) J_a.  Test both statements directly."""
    q = Ps.shape[0]
    Pi = U.T @ U
    supp = [np.where(np.abs(U[i]) > 1e-9)[0] for i in range(p)]
    sizes = [len(s) for s in supp]
    disjoint = len(set(np.concatenate(supp))) == sum(sizes)
    Jerr = np.nan
    if disjoint and set(sizes) == {a}:
        Jerr = 0.0
        offm = 0.0
        for s in supp:
            Jerr = max(Jerr, np.abs(np.abs(Pi[np.ix_(s, s)]) -
                                    np.ones((a, a)) / a).max())
        # off-block Frobenius mass
        M = Pi.copy()
        for s in supp:
            M[np.ix_(s, s)] = 0.0
        offm = np.linalg.norm(M)
        return dict(sizes=sizes, disjoint=disjoint, Jerr=Jerr, offmass=offm)
    return dict(sizes=sizes, disjoint=disjoint, Jerr=Jerr, offmass=None)


# ------------------------------- step 2: canonical fractional vertex system
def Phi(Ps, O):
    """sum_{i,k} <o_i, P_k o_i>^2 where o_i = columns of O."""
    d = np.einsum('ji,kjl,li->ik', O, Ps, O)      # d[i,k] = <o_i,P_k o_i>
    return float((d ** 2).sum()), d


def joint_diagonalise(Ps, p, a, seed=0, restarts=6, iters=3000, tol=1e-12):
    """Maximise Phi over O(p) by Jacobi sweeps (exact 2x2 maximisation by
    golden-free brute force over the rotation angle) -- returns best Phi, O."""
    rng = np.random.default_rng(seed)
    best = (-1.0, None)
    thetas = np.linspace(0, np.pi, 721)
    for r in range(restarts):
        if r == 0:
            O = np.eye(p)
        else:
            X = rng.standard_normal((p, p))
            O = np.linalg.qr(X)[0]
        cur, _ = Phi(Ps, O)
        for it in range(iters):
            improved = False
            for i in range(p):
                for j in range(i + 1, p):
                    vals = []
                    for th in thetas:
                        R = np.eye(p)
                        c, s = np.cos(th), np.sin(th)
                        R[i, i] = c
                        R[j, j] = c
                        R[i, j] = -s
                        R[j, i] = s
                        vals.append(Phi(Ps, O @ R)[0])
                    m = int(np.argmax(vals))
                    if vals[m] > cur + 1e-14:
                        th = thetas[m]
                        c, s = np.cos(th), np.sin(th)
                        R = np.eye(p)
                        R[i, i] = c
                        R[j, j] = c
                        R[i, j] = -s
                        R[j, i] = s
                        O = O @ R
                        cur = vals[m]
                        improved = True
            if not improved:
                break
        if cur > best[0]:
            best = (cur, O.copy())
    return best


def commutator_lower_bound(Ps):
    """Rigorous: if P_k = D_k + E_k with D_k diagonal then
       ||[P_j,P_k]||_F <= 2(||E_j||_F+||E_k||_F) + 2||E_j||_F ||E_k||_F,
    and ||E||_F <= sqrt(2).  Hence  max_j ||E_j||_F >= C / (4 + 2*sqrt(2))
    with C = max_{j,k} ||[P_j,P_k]||_F."""
    q = Ps.shape[0]
    C = max(np.linalg.norm(Ps[j] @ Ps[k] - Ps[k] @ Ps[j])
            for j in range(q) for k in range(j))
    return C, C / (4 + 2 * np.sqrt(2))


if __name__ == '__main__':
    np.set_printoptions(precision=5, suppress=True)
    cases = []
    for nm, f in [('K_4', K4), ('K_{3,3}', K33), ('cube Q_3', cube),
                  ('Petersen', petersen)]:
        Ps, p, a = f()
        cases.append((nm, Ps, p, a))
    for nm, (n, a, S) in [('circ n=12,a=3', (12, 3, [1, 11, 2, 10])),
                          ('circ n=16,a=4', (16, 4, [1, 15, 2, 14])),
                          ('circ n=20,a=5', (20, 5, [1, 19, 2, 18]))]:
        Ps, p, a, Pi, U = family_circulant(n, a, S)
        cases.append((nm, Ps, p, a))
    for seed in (1, 2):
        Ps, p, a, Pi, U, err = family_random(4, 3, seed=seed)
        cases.append((f'rand p=4,a=3 s{seed}', Ps, p, a))
    Ps, p, a, Pi, U, err = family_random(4, 4, seed=3)
    cases.append(('rand p=4,a=4 s3', Ps, p, a))

    print(f"{'family':18s} {'p':>2s} {'a':>2s} {'q':>3s}  "
          f"{'proj':>8s} {'sum':>8s} {'comm':>8s} | "
          f"{'disj':>5s} {'Jerr':>8s} | {'Phi':>9s} {'pa':>4s} "
          f"{'deficit':>9s} {'||[.,.]||':>9s} {'lb':>7s}")
    for nm, Ps, p, a in cases:
        q = Ps.shape[0]
        d = check_family(Ps, p, a)
        U, Pi = naimark(Ps, a)
        vp = vertex_partition_report(Ps, p, a, U)
        ph, O = joint_diagonalise(Ps, p, a, restarts=4)
        C, lb = commutator_lower_bound(Ps)
        print(f"{nm:18s} {p:2d} {a:2d} {q:3d}  {d['proj']:8.1e} {d['sum']:8.1e} "
              f"{d['comm']:8.1e} | {str(vp['disjoint']):>5s} "
              f"{vp['Jerr']:8.1e} | {ph:9.5f} {p*a:4d} {p*a-ph:9.5f} "
              f"{C:9.4f} {lb:7.4f}")
