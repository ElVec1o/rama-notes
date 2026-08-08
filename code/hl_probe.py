r"""hl_probe.py -- fast, progressive probe of the decisive questions.

Q1  Is the TARGET band [-2 sqrt a, 2 sqrt a] true (and is F real-rooted) for the
    plane class P(a) = { planes V_k, weights c_k >= 0, sum_k c_k P_{V_k} <= a I }?
Q2  Is the overlap Y_e = -X_e >= 0 on x >= 2 sqrt a for Adj = aI families?
Q3  What happens to Y_e under COMPRESSION (Adj != aI)?  Sign, and does the
    induction hypothesis  F_A >= (x - <e,Adj e>/t) F_{A^(e)}  still hold?
"""
import sys
import numpy as np
import hl_planes as H

np.set_printoptions(precision=5, suppress=True)


def hermite_maxroot(m, lam):
    """largest root of the weighted-K_m matching polynomial = largest eigenvalue
    of the Jacobi matrix with off-diagonal sqrt(k*lam), k=1..m-1."""
    from scipy.linalg import eigh_tridiagonal
    off = np.sqrt(np.arange(1, m) * lam)
    w = eigh_tridiagonal(np.zeros(m), off, select='i',
                         select_range=(m - 1, m - 1), eigvals_only=True)
    return float(w[-1])


def band_probe(name, Bs, m, a):
    F = H.F_dense(Bs, m)
    r = np.roots(F)
    Adm = H.Adj(Bs)
    adev = float(np.abs(Adm - a * np.eye(m)).max())
    print(f"  {name:24s} m={m:3d} q={len(Bs):3d} a={a:4.1f} "
          f"|Adj-aI|={adev:8.1e} | max|Im|={np.abs(r.imag).max():8.1e} "
          f"maxRe={r.real.max():8.4f} max|.|={np.abs(r).max():8.4f} "
          f"2sqrt(a)={2*np.sqrt(a):7.4f}  "
          f"{'ok' if np.abs(r).max() <= 2*np.sqrt(a)+1e-8 else '<<< VIOLATION'}")
    sys.stdout.flush()
    return float(np.abs(r).max())


def overlap_probe(name, Bs, m, a, ntrial=6, seed=0, opt=True):
    """worst (over e, over x >= 2 sqrt a) value of  X_e/F_{A'} = -Y_e/F_{A'}.
    positive => the overlap has the BAD sign (breaks the cavity induction)."""
    rng = np.random.default_rng(seed)
    xs = 2 * np.sqrt(a) * np.array([1.0, 1.01, 1.05, 1.2, 1.6, 3.0])

    def worst_at(v):
        e = v / np.linalg.norm(v)
        R = H.recursion(Bs, m, e)
        X, FAc = R['X'], R['FAc']
        return max(np.polyval(X, x) / np.polyval(FAc, x) for x in xs), R

    best, bR, be = -np.inf, None, None
    for tr in range(ntrial):
        e = np.eye(m)[tr % m] if tr < m else rng.standard_normal(m)
        v, R = worst_at(e)
        if v > best:
            best, bR, be = v, R, e / np.linalg.norm(e)
    if opt:
        try:
            from scipy.optimize import minimize
            res = minimize(lambda v: -worst_at(v)[0], be, method='Nelder-Mead',
                           options=dict(maxiter=300, xatol=1e-7, fatol=1e-11))
            best = max(best, -res.fun)
        except Exception:
            pass
    Cs = H.C_list(bR['X'], m)
    print(f"  {name:24s} m={m:3d} worst X_e/F_(A') = {best:12.4e}  "
          f"{'GOOD (<=0)' if best <= 1e-10 else '*** POSITIVE ***'}  "
          f"C_r={np.array2string(Cs[:4], precision=4)}")
    sys.stdout.flush()
    return best


def ih_probe(name, Bs, m, a, ntrial=6, seed=0):
    """worst over e, x of  (x - <e,Adj e>/t) - F_A/F_{A^(e)}.   >0  => IH FAILS."""
    rng = np.random.default_rng(seed)
    Adm = H.Adj(Bs)
    FA = H.F_dense(Bs, m)

    def gap(v):
        e = v / np.linalg.norm(v)
        Q = H.ortho_complement([e], m)
        FAc = H.F_dense(H.compress(Bs, Q), m - 1)
        d = float(e @ Adm @ e)
        out = -np.inf
        for mul in (1.0, 1.02, 1.1, 1.5, 3.0):
            t = np.sqrt(a) * mul
            x = t + a / t
            den = np.polyval(FAc, x)
            if abs(den) < 1e-14:
                continue
            out = max(out, (x - d / t) - np.polyval(FA, x) / den)
        return out

    best, bv = -np.inf, None
    for tr in range(ntrial):
        v = np.eye(m)[tr % m] if tr < m else rng.standard_normal(m)
        g = gap(v)
        if g > best:
            best, bv = g, v
    try:
        from scipy.optimize import minimize
        res = minimize(lambda v: -gap(v), bv, method='Nelder-Mead',
                       options=dict(maxiter=400, xatol=1e-8, fatol=1e-12))
        best = max(best, -res.fun)
    except Exception:
        pass
    print(f"  {name:24s} m={m:3d} worst IH gap  = {best:12.4e}  "
          f"{'IH holds' if best <= 1e-9 else '*** IH FAILS ***'}")
    sys.stdout.flush()
    return best


def compress_rand(Bs, m, levels, seed):
    rng = np.random.default_rng(seed)
    cur, mm = Bs, m
    for _ in range(levels):
        e = rng.standard_normal(mm)
        e /= np.linalg.norm(e)
        Q = H.ortho_complement([e], mm)
        cur = H.compress(cur, Q)
        mm -= 1
    return cur, mm


def graph_fams():
    out = [('K_4', H.graph_blocks(H.Kn_edges(4), 4), 4, 3),
           ('K_{3,3}', H.graph_blocks(
               [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3),
           ('cube Q_3', H.graph_blocks(H.cube_edges(), 8), 8, 3),
           ('Petersen', H.graph_blocks(H.petersen_edges(), 10), 10, 3)]
    for m in (6, 8, 10):
        lam = 3.0 / (m - 1)
        out.append((f'weighted K_{m} (a=3)',
                    H.graph_blocks(H.Kn_edges(m), m, [lam] * (m * (m - 1) // 2)),
                    m, 3))
    return out


def proj_fams():
    out = []
    for m, a, sd in [(4, 3, 1), (6, 3, 5), (6, 3, 6), (8, 3, 9), (4, 5, 7),
                     (6, 5, 11)]:
        Bs, err = H.random_projection_family(m, a, seed=sd)
        if err < 1e-11:
            out.append((f'randproj m{m} a{a} s{sd}', Bs, m, a))
    return out


def plane_fams():
    out = []
    for m, a, sd in [(4, 3, 1), (5, 3, 3), (6, 3, 4), (6, 2, 5), (7, 3, 6),
                     (4, 6, 8), (5, 5, 9)]:
        Bs, res = H.random_plane_family(m, a, seed=sd)
        if Bs is not None:
            out.append((f'randplane m{m} a{a} s{sd}', Bs, m, a))
    return out


# --------------------------------------------------------------------------
if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'

    if which in ('all', 'band'):
        print("=" * 128)
        print("Q1  TARGET BAND and real-rootedness")
        print("=" * 128)
        for nm, Bs, m, a in graph_fams() + proj_fams():
            band_probe(nm, Bs, m, a)
        print("  -- random PLANE families (Adj = aI, noncommuting, NOT projections) --")
        for nm, Bs, m, a in plane_fams():
            band_probe(nm, Bs, m, a)
        print("  -- REGRESSION: weighted K_m approaches 2 sqrt(a) from below --")
        for a in (3, 5):
            for m in (6, 20, 60, 200, 2000, 200000):
                mr = hermite_maxroot(m, a / (m - 1))
                print(f"    weighted K_{m:<7d} a={a}  maxroot={mr:9.5f}  "
                      f"2sqrt(a-1)={2*np.sqrt(a-1):8.5f}  2sqrt(a)={2*np.sqrt(a):8.5f}"
                      f"  {'OK' if mr < 2*np.sqrt(a) else 'CEILING BROKEN'}")

    if which in ('all', 'overlap'):
        print()
        print("=" * 128)
        print("Q2  sign of the overlap X_e  (need <= 0) on Adj = aI families")
        print("=" * 128)
        for nm, Bs, m, a in graph_fams() + proj_fams() + plane_fams():
            if m > 7:
                continue
            overlap_probe(nm, Bs, m, a)

    if which in ('all', 'compress'):
        print()
        print("=" * 128)
        print("Q3  COMPRESSED families (Adj != aI): sign of X_e, and the IH")
        print("=" * 128)
        base = [('K_{3,3}', H.graph_blocks(
            [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3),
            ('cube', H.graph_blocks(H.cube_edges(), 8), 8, 3),
            ('wK_8', H.graph_blocks(H.Kn_edges(8), 8, [3.0 / 7] * 28), 8, 3)]
        Bs, err = H.random_projection_family(8, 3, seed=9)
        if err < 1e-11:
            base.append(('randproj m8 a3', Bs, 8, 3))
        Bs, res = H.random_plane_family(6, 3, 22, seed=4)
        if Bs is not None:
            base.append(('randplane m6 a3', Bs, 6, 3))
        for nm, Bs, m, a in base:
            for lvl in (0, 1, 2):
                if m - lvl < 4 or m - lvl > 7:
                    continue
                Bc, mc = compress_rand(Bs, m, lvl, seed=100 + lvl)
                overlap_probe(f'{nm} c{lvl}', Bc, mc, a, ntrial=5)
                ih_probe(f'{nm} c{lvl}', Bc, mc, a, ntrial=5)
