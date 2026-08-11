"""The vertex matrix W(x) explicitly, and what a moment bound on its spectrum buys.

Target (M):   W(2 sqrt a) + F_A(2 sqrt a) . I  >=  0
for every weighted 2-plane family (c_k, V_k) on R^m with Adj(A) = a I; this is
equivalent to the band [a - 2 sqrt a, a + 2 sqrt a] for the mixed characteristic
polynomial, which beats Marchenko-Pastur for every a and is asymptotically sharp.

Everything here rests on one closed form.  For a decomposable 2r-vector
omega_T = c_1 ^ ... ^ c_{2r} with C the m x 2r matrix of its factors and
G = C^T C, the matrix of v |-> ||iota_v omega_T||^2 is

        M_{omega_T} = C adj(G) C^T                                        (*)

since <omega_{^j}, omega_{^l}> is the (l,j) cofactor of G.  At r = 1 this
reproduces Theta_k = e_2(A_k) P_{range A_k}, and taking traces gives
tr M_{omega_T} = 2r ||omega_T||^2, hence tr W = m F_A - x F_A', the identity
hl_theory.py verifies independently.

Usage:  python3 hl_Wspec.py
Deterministic: all seeds fixed.
"""
import math
from itertools import combinations

import numpy as np

import hl_planes as hp
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode

SEEDS = (0, 1, 2, 3, 4)


# ---------------------------------------------------------------------------
#  W(x)
# ---------------------------------------------------------------------------
def M_omega(C):
    """(*) the matrix of v |-> ||iota_v (c_1 ^ ... ^ c_k)||^2 for C = [c_1|...|c_k]."""
    G = C.T @ C
    k = G.shape[0]
    if k == 1:
        return np.outer(C[:, 0], C[:, 0])
    # adj(G) by cofactors; k is small (<= 2*rmax) so this is cheap and exact-ish
    adj = np.empty((k, k))
    for i in range(k):
        for j in range(k):
            minor = np.delete(np.delete(G, j, axis=0), i, axis=1)
            adj[i, j] = ((-1) ** (i + j)) * np.linalg.det(minor)
    return C @ adj @ C.T


def Theta_levels(Bs, m):
    """Theta^(r) = sum_{|T|=r} M_{omega_T}, r = 1 .. m//2.  Each is PSD."""
    q = len(Bs)
    rmax = min(m // 2, q)
    out = []
    for r in range(1, rmax + 1):
        S = np.zeros((m, m))
        for T in combinations(range(q), r):
            S += M_omega(np.hstack([Bs[k] for k in T]))
        out.append(S)
    return out


def W_at(Th, m, x):
    """W(x) = sum_{r>=1} (-1)^r Theta^(r) x^{m-2r}."""
    return sum(((-1) ** r) * Th[r - 1] * x ** (m - 2 * r)
               for r in range(1, len(Th) + 1))


def F_at(Bs, m, x):
    return float(np.polyval(hp.F_dense(Bs, m), x))


# ---------------------------------------------------------------------------
#  checks
# ---------------------------------------------------------------------------
def check_identity(Bs, m, Th, x):
    """<e, W(x) e> = F_A(x) - x F_{A^(e)}(x) for every unit e, and tr W = m F - x F'."""
    W = W_at(Th, m, x)
    FA = hp.F_dense(Bs, m)
    worst = 0.0
    rng = np.random.default_rng(7)
    for _ in range(4):
        e = rng.normal(size=m)
        e /= np.linalg.norm(e)
        Q = hp.ortho_complement([e], m)
        rhs = np.polyval(FA, x) - x * np.polyval(hp.F_dense(hp.compress(Bs, Q), m - 1), x)
        worst = max(worst, abs(e @ W @ e - rhs))
    tr_err = abs(np.trace(W) - (m * np.polyval(FA, x)
                                - x * np.polyval(np.polyder(FA), x)))
    return worst, tr_err


def moment_bound(W):
    """Two-moment lower bound on the least eigenvalue of a symmetric matrix:
    lam_min >= tr W / n - sqrt((n-1)/n) sqrt(tr W^2 - (tr W)^2 / n)."""
    n = W.shape[0]
    t1 = np.trace(W)
    t2 = np.trace(W @ W)
    var = max(t2 - t1 * t1 / n, 0.0)
    return t1 / n - math.sqrt((n - 1) / n) * math.sqrt(var)


# ---------------------------------------------------------------------------
def report(name, Bs, m):
    a = np.trace(hp.Adj(Bs)) / m
    off = np.linalg.norm(hp.Adj(Bs) - a * np.eye(m))
    x = 2 * math.sqrt(a)
    Th = Theta_levels(Bs, m)
    idw, idt = check_identity(Bs, m, Th, x)
    W = W_at(Th, m, x)
    FA = F_at(Bs, m, x)
    lam = np.linalg.eigvalsh(W)[0]
    mb = moment_bound(W)
    roots = np.sort(np.roots(hp.F_dense(Bs, m)).real)
    print(f"{name:26} m={m:2} q={len(Bs):3} a={a:6.3f} tight={off:8.1e} "
          f"id={max(idw, idt):7.1e}")
    print(f"{'':26} F_A(2sqrt a)={FA:12.4g}  lam_min(W)={lam:12.4g}  "
          f"(M) slack={lam + FA:11.4g}  {'OK' if lam + FA >= -1e-8 else 'FAIL'}")
    print(f"{'':26} band |root|<= {2*math.sqrt(a):.4f}, observed {abs(roots).max():.4f}"
          f"   two-moment bound on lam_min = {mb:.4g}"
          f"  -> {'suffices' if mb + FA >= 0 else 'insufficient'}")
    return lam + FA >= -1e-8, mb + FA >= 0


def main():
    print("=" * 96)
    print("W(x) built from (*), checked against the two identities of hl_theory.py")
    print("=" * 96)
    ok_all, mom_ok = True, []

    # weighted K_p: the family that approaches 2 sqrt a from below -- the regression
    for p in quickmode.few((4, 5, 6)):
        edges = hp.Kn_edges(p)
        lam = 1.0                     # Adj = lam (p-1) I for unit-weight K_p blocks
        Bs = hp.graph_blocks(edges, p, weights=[lam] * len(edges))
        ok, mo = report(f"weighted K_{p}", Bs, p)
        ok_all &= ok
        mom_ok.append((f"K_{p}", mo))

    for name, edges, m in (("S(K_4) cube-ish", hp.cube_edges(), 8),
                           ("Petersen", hp.petersen_edges(), 10)):
        Bs = hp.graph_blocks(edges, m)
        ok, mo = report(name, Bs, m)
        ok_all &= ok
        mom_ok.append((name, mo))

    for s in SEEDS:
        fam, res = hp.random_plane_family(6, 3.0, seed=s)
        if fam is None or res > 1e-9:
            continue
        ok, mo = report(f"random plane family s={s}", fam, 6)
        ok_all &= ok
        mom_ok.append((f"rand{s}", mo))

    print()
    print("(M) held in every case:", ok_all)
    print("two-moment bound sufficient in:",
          [n for n, v in mom_ok if v], "/ insufficient in:",
          [n for n, v in mom_ok if not v])


if __name__ == "__main__":
    main()
