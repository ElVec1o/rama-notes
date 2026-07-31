r"""Heilmann-Lieb deletion/contraction for FRACTIONAL weights, and why the
induction cannot reach the lower edge.

PART A.  The recursion transfers verbatim.  For any PSD contraction K and any
slot e in block k, with K^{(e)} := K - K e e^T K / K_ee  (the Schur complement
= the DPP conditioned on e in S; for a projection it is again a projection, of
rank one less, vanishing on e):

    N_K(y)  =  N_{K \ e}(y)  -  a K_ee N_{K^{(e)} \ block k}(y)          (slot)
    N_K(y)  =  y N_{K \ block k}(y)
                     - a sum_{e in block k} K_ee N_{K^{(e)} \ block k}(y) (block)

For a graph kernel K_ee = 1/a and this is exactly
    nu_G = nu_{G-k} - sum_{i in N(k)} nu_{G-k-i}.
Both identities are checked below to machine precision on class (P) and class
(C) kernels.  So the "deletion-contraction" half of Heilmann-Lieb survives the
passage to fractional weights, unchanged.

PART B.  It does not help, and already fails for GRAPHS.  The recursion only
ever produces induced subgraphs H = G[P',Q'], and the statement being proved,
"smallest root of nu_H >= (s-t)^2", is FALSE for them: roots interlace
DOWNWARDS under vertex deletion, and as soon as |Q'| < |P'| one has nu_H(0)=0,
i.e. smallest root 0.  Below: the first depth at which the induction hypothesis
dies, versus the largest root, which IS inherited (that is why the same
machinery proves the upper edge).
"""
import sys
import numpy as np
from itertools import combinations
from frac_naimark import GRAPHS, graph_kernel, nu_coeffs, matching_counts
from frac_classes import feasible_C, resid_C, band


# ------------------------------------------------------------------ PART A
def N_blocks(Kmat, blocks, a):
    """N(y) = sum_{T transversal wrt `blocks`} (-a)^{|T|} det(K[T,T]) y^{q-|T|}
    returned as coeff array high->low of length q+1."""
    q = len(blocks)
    acc = np.zeros(q + 1)

    def rec(k, T):
        if k == q:
            m = len(T)
            d = 1.0 if m == 0 else np.linalg.det(Kmat[np.ix_(T, T)])
            acc[m] += ((-a) ** m) * d
            return
        rec(k + 1, T)
        for e in blocks[k]:
            rec(k + 1, T + [e])
    rec(0, [])
    return acc


def schur(Kmat, e):
    """K^{(e)} = K - K e e^T K / K_ee  (defined on the whole index set; its
    e-row and e-column vanish)."""
    col = Kmat[:, e]
    return Kmat - np.outer(col, col) / Kmat[e, e]


def drop(idx, S):
    """index list with the entries of S removed (S = set of matrix indices)."""
    return [i for i in idx if i not in S]


def part_A(rng):
    print("=" * 78)
    print("PART A.  deletion / contraction for fractional weights")
    for (p, q, a, b, cls) in [(4, 6, 3, 2, 'P'), (3, 6, 4, 2, 'P'),
                              (4, 6, 3, 2, 'C'), (4, 8, 4, 2, 'C')]:
        n = q * b
        if cls == 'P':
            from tff import build_tff
            from naimark_form import naimark_pi
            A, res = build_tff(p, q, a, b, rng)
            if res > 1e-10:
                continue
            Kmat = naimark_pi(A, a, b)
        else:
            M = rng.standard_normal((n, n))
            Kmat = feasible_C(0.3 * (M + M.T) + np.eye(n) / a, q, b, a, iters=300)
            if resid_C(Kmat, q, b, a) > 1e-9:
                continue
        blocks = [list(range(k * b, (k + 1) * b)) for k in range(q)]
        N = N_blocks(Kmat, blocks, a)
        # --- slot identity at e = first slot of block 0
        k0, e = 0, blocks[0][0]
        bl_del = [drop(bk, {e}) for bk in blocks]
        rhs = np.zeros(q + 1)
        rhs += N_blocks(Kmat, bl_del, a)
        Ke = schur(Kmat, e)
        bl_c = [bk for j, bk in enumerate(blocks) if j != k0]
        t2 = N_blocks(Ke, bl_c, a)
        rhs[1:] -= a * Kmat[e, e] * t2                      # degree q-1
        err_slot = np.abs(N - rhs).max() / max(1.0, np.abs(N).max())
        # --- block identity at block k0
        rhs2 = np.zeros(q + 1)
        rhs2[:q] += N_blocks(Kmat, bl_c, a)                 # times y
        for e2 in blocks[k0]:
            rhs2[1:] -= a * Kmat[e2, e2] * N_blocks(schur(Kmat, e2), bl_c, a)
        err_blk = np.abs(N - rhs2).max() / max(1.0, np.abs(N).max())
        # is the Schur complement still a legal kernel?
        w = np.linalg.eigvalsh(0.5 * (Ke + Ke.T))
        print(f"  class ({cls}) p={p} q={q} (a,b)=({a},{b}): slot identity err "
              f"{err_slot:.2e}   block identity err {err_blk:.2e}   "
              f"spec(K^(e)) in [{w.min():.2e},{w.max():.6f}]  "
              f"diag(K^(e)) max {np.diag(Ke).max():.6f} (was {1/a:.6f})")
        sys.stdout.flush()


# ------------------------------------------------------------------ PART B
def nu_of_sub(adj, P, Q):
    """nu of the induced subgraph on P (list of P-vertices) and Q (list of
    Q-vertices); returns coeff list low->high in y, degree |P|."""
    pp = len(P)
    qq = len(Q)
    sub = []
    for i in P:
        m = 0
        for t, k in enumerate(Q):
            if (adj[i] >> k) & 1:
                m |= 1 << t
        sub.append(m)
    mcount = matching_counts(sub, pp, qq)
    c = [0] * (pp + 1)
    for i in range(pp + 1):
        c[pp - i] = (-1) ** i * mcount[i]
    return c


def minroot(c):
    if len(c) == 1:
        return np.inf
    r = np.roots(c[::-1])
    return float(np.sort(r.real)[0])


def maxroot(c):
    if len(c) == 1:
        return -np.inf
    r = np.roots(c[::-1])
    return float(np.sort(r.real)[-1])


def reachable(adj, p, q, P, Q):
    """(P,Q) is reachable by the recursion iff the deleted P-vertices can be
    matched injectively into the deleted Q-vertices."""
    dP = [i for i in range(p) if i not in P]
    dQ = [k for k in range(q) if k not in Q]
    if len(dP) > len(dQ):
        return False
    # Hopcroft-Karp-lite (Kuhn) matching
    match = {}

    def try_k(i, seen):
        for k in dQ:
            if (adj[i] >> k) & 1 and k not in seen:
                seen.add(k)
                if k not in match or try_k(match[k], seen):
                    match[k] = i
                    return True
        return False
    for i in dP:
        if not try_k(i, set()):
            return False
    return True


def part_B():
    print("=" * 78)
    print("PART B.  the induction hypothesis is not inherited by the minors")
    for name, (adj, p, q, a, b) in GRAPHS.items():
        if p + q > 15:
            continue
        lo, hi = band(a, b)
        c0 = nu_coeffs(adj, p, q)
        r0lo, r0hi = minroot(c0), maxroot(c0)
        first_fail, first_zero = None, None
        worst_hi = -np.inf
        nreach = 0
        for np_ in range(p, -1, -1):
            for P in combinations(range(p), np_):
                for nq in range(q, -1, -1):
                    for Q in combinations(range(q), nq):
                        if not reachable(adj, p, q, set(P), set(Q)):
                            continue
                        nreach += 1
                        depth = (q - nq)
                        c = nu_of_sub(adj, list(P), list(Q))
                        ml, mh = minroot(c), maxroot(c)
                        worst_hi = max(worst_hi, mh)
                        if ml < lo - 1e-9 and (first_fail is None
                                               or depth < first_fail[0]):
                            first_fail = (depth, len(P), len(Q), ml)
                        if abs(ml) < 1e-9 and (first_zero is None
                                               or depth < first_zero[0]):
                            first_zero = (depth, len(P), len(Q))
        print(f"  {name}: p={p} q={q} (a,b)=({a},{b}) band=[{lo:.4f},{hi:.4f}]"
              f"  nu_G roots in [{r0lo:.6f},{r0hi:.6f}]")
        print(f"      reachable minors: {nreach}")
        if first_fail:
            d, pp, qq, ml = first_fail
            print(f"      LOWER edge first fails at depth {d} "
                  f"(minor with |P'|={pp},|Q'|={qq}): smallest root {ml:.6f} "
                  f"< {lo:.6f}")
        if first_zero:
            d, pp, qq = first_zero
            print(f"      smallest root hits 0 at depth {d} "
                  f"(|P'|={pp},|Q'|={qq}: no P'-saturating matching)")
        print(f"      UPPER edge over ALL minors: max largest-root "
              f"{worst_hi:.6f} <= {r0hi:.6f} (inherited: "
              f"{worst_hi <= r0hi + 1e-9})")
        sys.stdout.flush()


if __name__ == '__main__':
    rng = np.random.default_rng(4242)
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', 'A'):
        part_A(rng)
    if which in ('all', 'B'):
        part_B()
