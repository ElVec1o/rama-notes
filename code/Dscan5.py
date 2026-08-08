"""Dscan5.py -- (A) EXACT noncommuting families, (B) the certificate audit.

(A) EXACT RATIONAL NONCOMMUTING TIGHT FUSION FRAMES.
    In R^4 the 16 vectors (+-1,+-1,+-1,+-1)/2 are RATIONAL unit vectors; two of
    them are orthogonal iff their sign patterns differ in exactly two places.
    sum over all 16 of v v^T = 4 I.  Delete an orthonormal quadruple (sum = I)
    and pair the remaining 12 into 6 orthogonal pairs: each pair gives a rank-2
    rational projection and the six sum to 3 I.  (p,q,a,b) = (4,6,3,2), exactly
    rational, genuinely noncommuting.  Same trick in R^9 with entries +-1/3
    gives b = 3.

(B) CERTIFICATE AUDIT.  For each family and each j, rho_j = mu deconv
    psi_0^{box j}; real-rootedness is now decided EXACTLY (Sturm) instead of by
    a float |Im| < 1e-7 test, and only then is the MSS/free lower bound applied.
"""
from fractions import Fraction
from itertools import combinations, product
import sys

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from Dclaim import (boxp, boxp_pow, deconv, poly_from_roots, psi0,            # noqa
                    is_real_rooted_exact, maximag_float, mu_multilinear_exact,
                    _det)
from Dscan3 import tstar, rr_at, alternation_certificate                       # noqa
from mcp2 import mcp                                                           # noqa


# ------------------------------------------------------- (A) exact families
def hadamard_vectors(p):
    """all (+-1)^p / sqrt(p) -- rational iff p is a perfect square."""
    r = int(round(p ** 0.5))
    assert r * r == p
    out = []
    for s in product((1, -1), repeat=p):
        out.append(tuple(Fraction(x, r) for x in s))
    return out


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


PYTH = [(Fraction(3, 5), Fraction(4, 5)), (Fraction(5, 13), Fraction(12, 13)),
        (Fraction(8, 17), Fraction(15, 17)), (Fraction(7, 25), Fraction(24, 25)),
        (Fraction(20, 29), Fraction(21, 29)), (Fraction(9, 41), Fraction(40, 41))]


def rational_orthogonal(p, rng, nrot=None):
    """product of Givens rotations with Pythagorean (c,s) -- exactly orthogonal
    with rational entries."""
    R = [[Fraction(int(i == j)) for j in range(p)] for i in range(p)]
    if nrot is None:
        nrot = 3 * p
    for _ in range(nrot):
        i, j = rng.choice(p, size=2, replace=False)
        i, j = int(i), int(j)
        c, s = PYTH[int(rng.integers(len(PYTH)))]
        if rng.integers(2):
            s = -s
        for col in range(p):
            ri, rj = R[i][col], R[j][col]
            R[i][col] = c * ri - s * rj
            R[j][col] = s * ri + c * rj
    return R


def check_orthogonal(R, p):
    for i in range(p):
        for j in range(p):
            s = sum(R[i][k] * R[j][k] for k in range(p))
            if s != (1 if i == j else 0):
                return False
    return True


def givens_ncfam(p, b, a, seed):
    """a rational orthogonal frames; class i = { R_i Pi_t R_i^T }, Pi_t the
    coordinate block projections.  Each class sums to I, so sum_k P_k = a I.
    Exactly rational, exactly a tight fusion frame, genuinely noncommuting."""
    rng = np.random.default_rng(seed)
    Ps = []
    for i in range(a):
        R = [[Fraction(int(x == y)) for y in range(p)] for x in range(p)] \
            if i == 0 else rational_orthogonal(p, rng)
        assert check_orthogonal(R, p)
        cols = [[R[r][c] for r in range(p)] for c in range(p)]   # columns of R
        for t in range(p // b):
            Ps.append(proj_from_onb(cols[t * b:(t + 1) * b], p))
    return Ps


def newton_margin(rho, p, err):
    """Newton's inequalities  P_k^2 >= P_{k-1} P_{k+1},  P_k = e_k / C(p,k).
    Returns (min normalised slack, certified_not_real_rooted).
    err = absolute coefficient error bound on rho."""
    from math import comb
    e = [Fraction(rho[k]) * (-1) ** k for k in range(p + 1)]
    P = [float(e[k]) / comb(p, k) for k in range(p + 1)]
    dP = [err / comb(p, k) for k in range(p + 1)]
    worst = np.inf
    bad = False
    for k in range(1, p):
        val = P[k] ** 2 - P[k - 1] * P[k + 1]
        sens = (2 * abs(P[k]) * dP[k] + abs(P[k - 1]) * dP[k + 1]
                + abs(P[k + 1]) * dP[k - 1])
        if val < -sens:
            bad = True
        worst = min(worst, val / max(sens, 1e-300))
    return worst, bad


def deconv_amplification(f, p):
    """max_k sum_j |(M^{-1})_{kj}| for M = the box_p-by-f matrix: turns a
    coefficient error eps on mu into an error <= eps * amp on rho."""
    from Dclaim import boxp_matrix
    M = boxp_matrix(f, p)
    Inv = [[Fraction(0)] * (p + 1) for _ in range(p + 1)]
    for c in range(p + 1):
        for k in range(p + 1):
            s = Fraction(int(k == c))
            for j in range(k):
                s -= M[k][j] * Inv[j][c]
            Inv[k][c] = s
    return max(sum(abs(Inv[k][j]) for j in range(p + 1)) for k in range(p + 1))


def build_exact_ncfam(p, b, a, seed, tries=4000):
    """q = p a / b blocks of b mutually orthogonal +-1/sqrt(p) vectors, with
    sum_k P_k = a I.  Built by deleting (p - a? ) -- see construction below."""
    V = hadamard_vectors(p)
    n = len(V)                                  # 2^p
    # sum over ALL of v v^T = (2^p / p) I
    tot = Fraction(n, p)
    assert tot == n // p
    # We need a sub-multiset summing to a I.  Take a disjoint orthonormal
    # bases (each sums to I); pairing inside each basis gives the blocks.
    rng = np.random.default_rng(seed)
    used = set()
    blocks = []
    for _ in range(a):
        base = []
        for _ in range(tries):
            cand = V[int(rng.integers(n))]
            if cand in used:
                continue
            if all(dot(cand, u) == 0 for u in base):
                base.append(cand)
                if len(base) == p:
                    break
        if len(base) != p:
            return None
        for u in base:
            used.add(u)
            used.add(tuple(-x for x in u))       # avoid +-v duplicates
        rng.shuffle(base)
        for t in range(p // b):
            blocks.append(base[t * b:(t + 1) * b])
    return blocks


def proj_from_onb(vs, p):
    P = [[Fraction(0)] * p for _ in range(p)]
    for v in vs:
        for i in range(p):
            for j in range(p):
                P[i][j] += v[i] * v[j]
    return P


def noncommuting(Ps, p):
    for A in Ps:
        for B in Ps:
            for i in range(p):
                for j in range(p):
                    s = sum(A[i][k] * B[k][j] - B[i][k] * A[k][j] for k in range(p))
                    if s != 0:
                        return True
    return False


def sum_is_aI(Ps, p, a):
    for i in range(p):
        for j in range(p):
            s = sum(P[i][j] for P in Ps)
            if s != (a if i == j else 0):
                return False
    return True


def has_parallel_class_proj(Ps, p, b, a):
    """subsets G with sum_{k in G} P_k = I_p (exact)."""
    q = len(Ps)
    m = p // b
    for G in combinations(range(q), m):
        ok = True
        for i in range(p):
            for j in range(p):
                s = sum(Ps[k][i][j] for k in G)
                if s != (1 if i == j else 0):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True, G
    return False, None


def run_A():
    print("=" * 126)
    print("(A) EXACT RATIONAL NONCOMMUTING tight fusion frames "
          "(Givens/Pythagorean rotations; sum_k P_k = a I holds EXACTLY)")
    print("    Every family here HAS the orthogonal parallel-class partition by "
          "construction.")
    print("=" * 126)
    print("%-22s %3s %3s %3s %3s | %-7s %-7s | %-7s %-8s %-8s %-9s %-8s" %
          ("family", "p", "q", "a", "b", "noncomm", "par.cl", "(D)", "#real",
           "max|Im|", "Newton", "mu route"))
    for (p, b, a, seed) in [(4, 2, 3, 1), (4, 2, 3, 7), (4, 2, 4, 3),
                            (6, 2, 3, 5), (6, 2, 3, 9), (6, 3, 3, 2),
                            (8, 2, 3, 4), (8, 2, 3, 6), (8, 4, 3, 8),
                            (10, 2, 3, 12), (9, 3, 3, 13), (12, 3, 3, 14),
                            (12, 2, 3, 15)]:
        Ps = givens_ncfam(p, b, a, seed)
        q = len(Ps)
        assert sum_is_aI(Ps, p, a), "sum != aI"
        nc = noncommuting(Ps, p)
        Pnp = np.array([[[float(x) for x in row] for row in P] for P in Ps])
        if p <= 4:
            mu = mu_multilinear_exact(Ps, p)
            dev = max(abs(float(mu[i]) - mcp(Pnp)[i]) for i in range(p + 1))
            route, eps = "EXACT (dev %.0e)" % dev, Fraction(0)
        else:
            ref = mcp(Pnp)
            mu = [Fraction(x).limit_denominator(10 ** 12) for x in ref]
            route, eps = "float mcp", 1e-9 * max(1.0, max(abs(x) for x in ref))
        pc = (True, None) if True else None      # by construction
        rho = deconv(mu, psi0(p, b), p)
        assert boxp(psi0(p, b), rho, p) == [Fraction(x) for x in mu]
        rr, nreal, nsq = is_real_rooted_exact(rho)
        mi, _ = maximag_float(rho)
        amp = float(deconv_amplification(psi0(p, b), p))
        nm, bad = newton_margin(rho, p, float(eps) * amp)
        print("  %-22s %3d %3d %3d %3d | %-7s %-7s | %-7s %d/%-6d %.2e %9.2e %s"
              % ('NC givens s%d' % seed, p, q, a, b, nc, True, rr, nreal, nsq,
                 mi, nm, route + ("  CERT-NOT-RR" if bad else "")))
        sys.stdout.flush()
    print("  ('Newton' = min normalised slack in Newton's inequalities; "
          "negative and |.|>1 certifies NOT real-rooted robustly)")
    print()


# --------------------------------------------------- (B) certificate audit
def Kfun(roots, w, iters=40):
    r = np.asarray(roots, dtype=float)
    if w < 0:
        x = r.min() - max(1.0, 1.0 / abs(w))
        lo, hi = -np.inf, r.min()
    else:
        x = r.max() + max(1.0, 1.0 / abs(w))
        lo, hi = r.max(), np.inf
    for _ in range(iters):
        g = np.mean(1.0 / (x - r))
        if g > w:
            lo = max(lo, x)
        else:
            hi = min(hi, x)
        gp = -np.mean(1.0 / (x - r) ** 2)
        xn = x - (g - w) / gp
        if not (lo < xn < hi) or not np.isfinite(xn):
            xn = 0.5 * (lo + hi) if np.isfinite(lo) and np.isfinite(hi) else \
                (x - 1.0 if w < 0 else x + 1.0)
        if abs(xn - x) < 1e-14 * max(1.0, abs(x)):
            x = xn
            break
        x = xn
    return x


def free_edge(root_lists, side='min', ngrid=260):
    m = len(root_lists)
    ws = -np.exp(np.linspace(np.log(1e-6), np.log(3e3), ngrid))
    if side == 'max':
        ws = -ws
    best = None
    for w in ws:
        try:
            v = sum(Kfun(r, w) for r in root_lists) - (m - 1) / w
        except Exception:
            continue
        if best is None or (side == 'min' and v > best) or \
           (side == 'max' and v < best):
            best = v
    return best


def audit_certificate(fams):
    print("=" * 122)
    print("(B) CERTIFICATE AUDIT: which j give a REAL-ROOTED rho_j = mu deconv "
          "psi_0^{box j}?  (Sturm-exact)")
    print("    then: does the free/MSS lower bound from that splitting reach the "
          "tree edge (sqrt(a-1)-sqrt(b-1))^2 ?")
    print("=" * 122)
    print("%-26s %-13s | %-14s %-6s | %-10s %-10s %-10s %-6s" %
          ("family", "(p,q,a,b)", "J = {j: rr}", "j=1?", "cert lo",
           "true lmin", "tree lo", "reach"))
    nfam = nJ = nreach = nD = 0
    for name, p, q, a, b, mu in fams:
        if p % b:
            continue
        nfam += 1
        J = []
        for j in range(1, a + 1):
            f = boxp_pow(psi0(p, b), p, j)
            rho = deconv(mu, f, p)
            if is_real_rooted_exact(rho)[0]:
                J.append(j)
        nD += int(1 in J)
        lo_band = (np.sqrt(a - 1.0) - np.sqrt(b - 1.0)) ** 2
        true_lo = float(np.min(np.roots([float(x) for x in mu]).real))
        best = None
        for j in J:
            f = boxp_pow(psi0(p, b), p, j)
            rho = deconv(mu, f, p)
            rts = np.sort(np.roots([float(x) for x in rho]).real)
            chi = [0.0] * (p - p // b) + [float(b)] * (p // b)
            cand = free_edge([chi] * j + [list(rts)], 'min')
            if best is None or cand > best[1]:
                best = (j, cand)
        if J:
            nJ += 1
        reach = bool(best is not None and best[1] >= lo_band - 1e-9)
        nreach += int(reach)
        print("  %-26s (%2d,%2d,%d,%d) | %-14s %-6s | %-10s %10.6f %10.6f %-6s"
              % (name, p, q, a, b, str(J), 1 in J,
                 ("%.6f" % best[1]) if best else "none",
                 true_lo, lo_band, reach))
        sys.stdout.flush()
    print("  ---> %d families; rho_1 real-rooted (claim D) in %d; SOME j works in "
          "%d; certificate reaches the tree edge in %d" % (nfam, nD, nJ, nreach))
    print()


def build_audit_families():
    from Dscan import (mu_from_blocks, edges_to_blocks, complete_graph,
                       complete_bipartite, hypercube, petersen, cycle_prism,
                       moebius_ladder, gp, circulant, check_biregular)
    from Dscan3 import designs
    out = []
    for nm, E, p in [('K_4', *complete_graph(4)),
                     ('K_{3,3}', *complete_bipartite(3)),
                     ('prism', *cycle_prism(3)),
                     ('Q_3 cube', *hypercube(3)),
                     ('Wagner M_4', *moebius_ladder(4)),
                     ('Petersen', *petersen()),
                     ('C_5xK_2', *cycle_prism(5)),
                     ('Moebius M_5', *moebius_ladder(5)),
                     ('C_6xK_2', *cycle_prism(6)),
                     ('Moebius M_6', *moebius_ladder(6)),
                     ('GP(6,2)', *gp(6, 2)),
                     ('GP(7,2)', *gp(7, 2)),
                     ('K_{4,4}', *complete_bipartite(4)),
                     ('K_6', *complete_graph(6)),
                     ('circ(8,[1,2])', *circulant(8, [1, 2])),
                     ('circ(10,[1,2])', *circulant(10, [1, 2])),
                     ('circ(12,[1,2])', *circulant(12, [1, 2])),
                     ('K_8', *complete_graph(8)),
                     ('K_{5,5}', *complete_bipartite(5))]:
        blocks = edges_to_blocks(E)
        q = len(blocks)
        if (2 * q) % p or p % 2:
            continue
        a = 2 * q // p
        if not check_biregular(blocks, p, a, 2):
            continue
        out.append((nm, p, q, a, 2, mu_from_blocks(blocks, p)))
    for name, blocks, p, q, a, b in designs():
        blocks = [tuple(sorted(B)) for B in blocks]
        if not check_biregular(blocks, p, a, b) or p % b or p > 12:
            continue
        out.append((name, p, q, a, b, mu_from_blocks(blocks, p)))
    return out


if __name__ == '__main__':
    w = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if w in ('all', 'A'):
        run_A()
    if w in ('all', 'B'):
        audit_certificate(build_audit_families())
