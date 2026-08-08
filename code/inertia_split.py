"""How the torus splits between abelian inertia classes inside a universal-cover gap.

G24 is the statement that for x outside spec(T),

    sign( integral over T^b of det S(x,z) dz ) = (-1)^{delta(x)},

with S(x,z) the 2x2 Schur complement of xI - A_G(z) onto a two-element feedback set and
delta the free inertia. G29 named the obstruction: the free side computes something like a
geometric mean while mu_G computes an arithmetic mean of determinants, and Jensen relates
them by an inequality that is too weak to fix a sign.

This script measures the quantity that decides it. Inside a gap of spec(T) the abelian
inertia delta_ab(z) is NOT constant, so the integrand changes sign over the torus. Writing
m_j for the measure of {z : delta_ab(z) = j} and I_j for the integral of |det S| over that
set, the average is I_0 - I_1 + I_2 and its sign is a competition. The question is whether
that competition is a landslide, which would be a lead, or close, which would say G24 is
genuinely delicate.

delta is obtained as kappa - N_F, with kappa from the cavity solver and N_F the root count
of the forest polynomial, using Haynsworth. Everything is compared against the prediction
(-1)^delta.
"""

import sys
import math
import cmath
import numpy as np

sys.path.insert(0, 'code')


def spanning_tree(n, edges):
    par = list(range(n))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    tree, cot = [], []
    for i, (u, v) in enumerate(edges):
        ru, rv = find(u), find(v)
        if ru != rv:
            par[ru] = rv
            tree.append(i)
        else:
            cot.append(i)
    return tree, cot


def magnetic(n, edges, cot, thetas):
    A = np.zeros((n, n), dtype=complex)
    ph = {i: thetas[j] for j, i in enumerate(cot)}
    for i, (u, v) in enumerate(edges):
        w = cmath.exp(1j * ph.get(i, 0.0))
        A[u, v] += w
        A[v, u] += w.conjugate()
    return A


def matching_coeffs(n, edges):
    from functools import lru_cache
    m = len(edges)

    @lru_cache(maxsize=None)
    def rec(i, mask, k):
        if i == m:
            return 1 if k == 0 else 0
        t = rec(i + 1, mask, k)
        if k > 0:
            u, v = edges[i]
            bu, bv = 1 << u, 1 << v
            if not (mask & bu) and not (mask & bv):
                t += rec(i + 1, mask | bu | bv, k - 1)
        return t

    c = [0] * (n + 1)
    for k in range(n // 2 + 1):
        c[n - 2 * k] += (-1) ** k * rec(0, 0, k)
    rec.cache_clear()
    return c


def roots_above(coeffs, e):
    """Budan-Fourier; exact for real-rooted polynomials."""
    cur = list(map(float, coeffs))
    vals = []
    for _ in range(len(coeffs)):
        acc = 0.0
        for j in range(len(cur) - 1, -1, -1):
            acc = acc * e + cur[j]
        vals.append(acc)
        cur = [cur[j] * j for j in range(1, len(cur))] if len(cur) > 1 else [0.0]
    ch, last = 0, 0.0
    for v in vals:
        if abs(v) < 1e-12:
            continue
        if last != 0.0 and v * last < 0:
            ch += 1
        last = v
    return ch


def delete(n, edges, drop):
    keep = [u for u in range(n) if u not in drop]
    idx = {u: i for i, u in enumerate(keep)}
    return len(keep), [(idx[a], idx[b]) for a, b in edges
                       if a not in drop and b not in drop]


def schur_2x2(A, x, W):
    """Schur complement of xI - A onto the index set W (size 2)."""
    n = A.shape[0]
    rest = [i for i in range(n) if i not in W]
    M = x * np.eye(n, dtype=complex) - A
    Mww = M[np.ix_(W, W)]
    Mwr = M[np.ix_(W, rest)]
    Mrw = M[np.ix_(rest, W)]
    Mrr = M[np.ix_(rest, rest)]
    return Mww - Mwr @ np.linalg.solve(Mrr, Mrw)


GRAPHS = {
    'twotriangles': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (0, 3)),
    'K4+pendant': (8, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                       (0, 4), (1, 5), (2, 6), (3, 7)], (0, 1)),
}


def main():
    src = open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:')
    ns = {}
    exec(src, ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    for name, (n, edges, W) in GRAPHS.items():
        nF, eF = delete(n, edges, set(W))
        cF = matching_coeffs(nF, eF)
        tree, cot = spanning_tree(n, edges)
        b = len(cot)
        steps = 40 if b <= 2 else 16
        grid = [2 * math.pi * k / steps for k in range(steps)]

        R = 5.0
        got = None
        for eta in (1e-6, 1e-4, 1e-3, 1e-2):
            es, ds, bad = scan(n, edges, -R, R, 3000, eta=eta)
            if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.02:
                got = (es, ds)
                break
        if got is None:
            print(f"{name}: solver gated"); continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        gaps = []
        prev = -R
        for a, bnd in bs:
            if a - prev > 0.06:
                gaps.append(0.5 * (prev + a))
            prev = bnd

        print(f"\n{name}  b={b}  bands {[('%.3f' % a, '%.3f' % c) for a, c in bs]}")
        print(f"{'x':>9}{'delta':>7}{'m0':>8}{'m1':>8}{'m2':>8}"
              f"{'avg det':>12}{'sign ok':>9}")
        for x in gaps:
            k = kappa_above(es, ds, n, x)
            NF = roots_above(cF, x)
            delta = round(k) - NF
            tot = steps ** b
            cnt = [0, 0, 0]
            acc = 0.0
            for t in range(tot):
                th, r = [], t
                for _ in range(b):
                    th.append(grid[r % steps]); r //= steps
                S = schur_2x2(magnetic(n, edges, cot, th), x, list(W))
                S = 0.5 * (S + S.conj().T)
                w = np.linalg.eigvalsh(S)
                j = int(np.sum(w < 0))
                if 0 <= j <= 2:
                    cnt[j] += 1
                acc += np.real(np.linalg.det(S))
            m = [c / tot for c in cnt]
            avg = acc / tot
            ok = (avg > 0) == (delta % 2 == 0)
            print(f"{x:>9.4f}{delta:>7}{m[0]:>8.3f}{m[1]:>8.3f}{m[2]:>8.3f}"
                  f"{avg:>12.4f}{('YES' if ok else 'NO'):>9}")
    print("\nm_j is the fraction of the torus with j negative eigenvalues of S(x,z);")
    print("a landslide would be a lead, a near tie would say G24 is delicate")
    return 0


if __name__ == '__main__':
    sys.exit(main())
