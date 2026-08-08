"""ff_L2.py -- genuine families: hypothesis (D), the forced moments, and (L).

(D)   mu = psi_0 box_p rho   with rho REAL-ROOTED,
      psi_0(x) = x^{p - p/b} (x - b)^{p/b}.

This file (i) rebuilds the deconvolution independently and self-tests it,
(ii) settles (D) on the families in question, (iii) checks the forced first
three cumulants of rho, (iv) evaluates (L).
"""
import sys
from fractions import Fraction
from itertools import combinations, product

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
import ff_L as X                                                               # noqa
from frac_naimark import GRAPHS, nu_coeffs                                     # noqa


# -------------------------------------------------------- subdivision graphs
def subdivision(edges, n):
    """S(G) for a d-regular G on n vertices: P = vertices (a = d),
    Q = edges (b = 2).  adj[i] = bitmask of incident edges."""
    adj = [0] * n
    for k, (u, v) in enumerate(edges):
        adj[u] |= 1 << k
        adj[v] |= 1 << k
    deg = [bin(x).count('1') for x in adj]
    assert len(set(deg)) == 1, deg
    return adj, n, len(edges), deg[0], 2


def cube_Q3():
    V = list(product((0, 1), repeat=3))
    idx = {v: i for i, v in enumerate(V)}
    E = []
    for v in V:
        for c in range(3):
            w = list(v); w[c] ^= 1; w = tuple(w)
            if idx[v] < idx[w]:
                E.append((idx[v], idx[w]))
    return subdivision(E, 8)


def petersen():
    # outer C5 0..4, inner pentagram 5..9, spokes i--i+5
    E = [(i, (i + 1) % 5) for i in range(5)]
    E += [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    E += [(i, i + 5) for i in range(5)]
    return subdivision(E, 10)


def K33():
    E = [(i, 3 + j) for i in range(3) for j in range(3)]
    return subdivision(E, 6)


def K4():
    return subdivision(list(combinations(range(4), 2)), 4)


def heawood_cubic():
    # Heawood graph: 14 vertices, 3-regular, bipartite
    E = []
    for i in range(14):
        E.append((i, (i + 1) % 14))
    for i in range(0, 14, 2):
        E.append((i, (i + 5) % 14))
    E = sorted(set(tuple(sorted(e)) for e in E))
    return subdivision(E, 14)


def K5_sub():
    """K_5 is 4-regular on 5 vertices -> a=4, b=2, p=5, q=10."""
    return subdivision(list(combinations(range(5), 2)), 5)


def mu_of_graph(adj, p, q):
    c = nu_coeffs(adj, p, q)
    return [Fraction((-1) ** m * c[p - m]) for m in range(p + 1)]


# ------------------------------------------------------------ deconvolution
def psi0(p, b):
    """signed-e of  x^{p - p/b} (x - b)^{p/b}   (requires b | p)."""
    assert p % b == 0, (p, b)
    m = p // b
    return F.signed_e_from_roots([Fraction(0)] * (p - m) + [Fraction(b)] * m)


def deconv(e, f, d):
    """unique rho with e = f box_d rho, via cumulant subtraction (exact)."""
    ke, kf = F.kappa(e, d, d), F.kappa(f, d, d)
    kr = [Fraction(0)] + [ke[n] - kf[n] for n in range(1, d + 1)]
    return F.poly_from_kappa(kr, d)


def selftest_deconv():
    print("=" * 88)
    print("[A] deconvolution self-tests (round-trip, identity, shift)")
    print("=" * 88)
    rng = np.random.default_rng(7)
    worst_rt = 0.0
    for _ in range(20):
        d = int(rng.integers(3, 9))
        r1 = [Fraction(int(rng.integers(-40, 40)), 7) for _ in range(d)]
        r2 = [Fraction(int(rng.integers(-40, 40)), 5) for _ in range(d)]
        e1, e2 = F.signed_e_from_roots(r1), F.signed_e_from_roots(r2)
        c = F.boxp(e1, e2, d)
        back = deconv(c, e2, d)
        worst_rt = max(worst_rt, max(abs(float(back[i] - e1[i]))
                                     for i in range(d + 1)))
    print("   round-trip  (f box g) deconv g == f  : max |err| = %.3e" % worst_rt)
    # identity element x^d
    d = 6
    r1 = [Fraction(i) for i in range(d)]
    e1 = F.signed_e_from_roots(r1)
    idp = F.signed_e_from_roots([Fraction(0)] * d)
    print("   identity    f deconv x^d == f       : exact =",
          deconv(e1, idp, d) == e1)
    # shift additivity: (x-c)^d box f == f(x-c)
    c = Fraction(3, 2)
    sh = F.signed_e_from_roots([c] * d)
    lhs = F.boxp(e1, sh, d)
    rhs = F.signed_e_from_roots([x + c for x in r1])
    print("   shift       (x-c)^d box f == f(.-c) : exact =", lhs == rhs)
    print()


# ---------------------------------------------------------------- families
def families():
    out = []
    for nm, g in [('S(K_4)      p=4 ', K4()), ('S(K_{3,3})  p=6 ', K33()),
                  ('S(Q_3)      p=8 ', cube_Q3()),
                  ('S(Petersen) p=10', petersen()),
                  ('S(Heawood)  p=14', heawood_cubic())]:
        adj, p, q, a, b = g
        if p % b == 0:
            out.append((nm, p, q, a, b, mu_of_graph(adj, p, q)))
    for nm, (adj, p, q, a, b) in GRAPHS.items():
        if p % b == 0:
            out.append(('G ' + nm, p, q, a, b, mu_of_graph(adj, p, q)))
    return out


def report():
    print("=" * 118)
    print("[B] hypothesis (D), the forced moments of rho, and claim (L)")
    print("    psi_0(x) = x^(p - p/b) (x - b)^(p/b);  rho := mu deconv_p psi_0")
    print("=" * 118)
    hdr = ("%-18s %-11s %-9s %-30s %-9s %-9s %-9s" %
           ("family", "(p,q,a,b)", "rho r.r.?", "moments(rho) m1/mu2/mu3 err",
            "min rho", "L(mu_rho)", "tree lo"))
    print(hdr)
    for nm, p, q, a, b, e in families():
        f = psi0(p, b)
        rho = deconv(e, f, p)
        # exactness of the factorisation
        chk = F.boxp(f, rho, p)
        err = max(abs(float(chk[i] - e[i])) for i in range(p + 1))
        r = np.roots(F.poly_from_signed_e(rho, p))
        sc = max(1.0, float(np.max(np.abs(r))))
        im = float(np.max(np.abs(r.imag))) / sc
        rr = im < 1e-7
        m1t, m2t, m3t = X.forced_moments(a, b)
        if rr:
            rts = np.sort(r.real)
            m1, m2, m3 = X.moments_of(rts)
            L = X.L_roots(rts, b)
            mn = rts.min()
            mtxt = "%.1e/%.1e/%.1e" % (abs(m1 - m1t), abs(m2 - m2t), abs(m3 - m3t))
            print("  %-17s (%d,%d,%d,%d)%s %-9s %-30s %9.5f %9.5f %9.5f  (L)=%s"
                  % (nm, p, q, a, b, ' ' * max(0, 11 - len("(%d,%d,%d,%d)" % (p, q, a, b))),
                     "YES", mtxt, mn, L, X.tree_band(a, b)[0],
                     L >= X.tree_band(a, b)[0] - 1e-9))
        else:
            # cumulants still make sense; report them from the exact kappa
            k = F.kappa(rho, p, 3)
            k2t = (a - 1) * Fraction(p * (b - 1), p - 1)
            k3t = (a - 1) * Fraction(p * p * (b - 1) * (b - 2), (p - 1) * (p - 2))
            ok = (k[1] == a - 1 and k[2] == k2t and k[3] == k3t)
            print("  %-17s (%d,%d,%d,%d)%s %-9s forced kappa_1..3 exact=%s"
                  "   max|Im|/scale = %.3e   [refactor err %.1e]"
                  % (nm, p, q, a, b, ' ' * max(0, 11 - len("(%d,%d,%d,%d)" % (p, q, a, b))),
                     "NO", ok, im, err))
    print()


def check_forced_cumulants():
    print("=" * 88)
    print("[C] the forced cumulants of rho, EXACT, on every family")
    print("=" * 88)
    allok = True
    for nm, p, q, a, b, e in families():
        rho = deconv(e, psi0(p, b), p)
        k = F.kappa(rho, p, 3)
        k1t = Fraction(a - 1)
        k2t = (a - 1) * Fraction(p * (b - 1), p - 1)
        k3t = (a - 1) * Fraction(p * p * (b - 1) * (b - 2), (p - 1) * (p - 2))
        ok = (k[1] == k1t and k[2] == k2t and k[3] == k3t)
        allok &= ok
        print("  %-17s (%d,%d,%d,%d)  kappa_1,2,3 = %s   forced=%s"
              % (nm, p, q, a, b, [str(x) for x in k[1:4]], ok))
    print("  ALL forced (exact rational identity):", allok)
    print()


def check_dictionary():
    """kappa_1 = m1, kappa_2 = d/(d-1) mu2, kappa_3 = d^2/((d-1)(d-2)) mu3."""
    print("=" * 88)
    print("[D] cumulant <-> moment dictionary for root measures")
    print("=" * 88)
    rng = np.random.default_rng(3)
    worst = 0.0
    for _ in range(60):
        d = int(rng.integers(4, 12))
        r = [Fraction(int(rng.integers(-50, 50)), 3) for _ in range(d)]
        e = F.signed_e_from_roots(r)
        k = F.kappa(e, d, 3)
        rr = np.array([float(x) for x in r])
        m1, m2, m3 = X.moments_of(rr)
        pred = [m1, d / (d - 1) * m2, d ** 2 / ((d - 1) * (d - 2)) * m3]
        for i in range(3):
            worst = max(worst, abs(float(k[i + 1]) - pred[i]) /
                        max(1.0, abs(pred[i])))
    print("   max relative discrepancy over 60 random real-rooted polys: %.3e"
          % worst)
    print("   => forced kappa  <=>  m1 = a-1, mu2 = (a-1)(b-1),"
          " mu3 = (a-1)(b-1)(b-2)")
    print()


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', 'A'):
        selftest_deconv()
    if which in ('all', 'D'):
        check_dictionary()
    if which in ('all', 'C'):
        check_forced_cumulants()
    if which in ('all', 'B'):
        report()
