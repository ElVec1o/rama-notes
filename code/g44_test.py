"""Is G44 true as stated, or only the inequality underneath it?

G44 asks for   Delta > 2 * (the shell bound on I_wrong),   not   Delta > 2 * I_wrong.
The Jensen sweep tests the second. If the shell chain is lossy the two are very different and
G44 could be false while the thing it was invented to prove is fine. Rule 3 says find that out
before proving anything.

The chain of ShellBound, with every constant made explicit:

    I_wrong  <=  m * sup_A |det S|                          (crude sup bound)
             <=  m * M * L * reach                          (|det S| = ||S|| * min|lambda|,
                                                             and Weyl on the crossing one)
             <=  m * M * L * 2 pi (m / V_b)^(1/b)           (a region of inradius r contains
                                                             a ball, V_b the unit ball volume)

so at b = 2, since V_2 = pi,   I_wrong <= 2 sqrt(pi) * M * L * m^(3/2).

Here M = sup ||S|| over the wrong-parity region, L = sqrt(sum_j sup ||dS/dtheta_j||^2) so
that Weyl reads |lambda(z) - lambda(w)| <= L |z - w|_2, and reach is the inradius measured by
a torus BFS from the boundary.

The script prints each link separately so the loss is attributable:

    I_wrong      measured,
    step1        m * sup|det S|,
    step2        m * M * L * reach,
    step3        2 sqrt(pi) M L m^{3/2},     the bound G44 must beat,
    Delta/2      what it must be beaten by,
    G44          whether step3 < Delta/2.

If G44 fails while Delta > 2 I_wrong holds, the fix is to sharpen a named link, and the
printout says which one.
"""

import sys
import math
import cmath
from collections import deque
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

GRAPHS = {
    'twotri': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3)], (0, 3)),
    'theta': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3)], (0, 3)),
    'K4pend': (8, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
                   (0, 4), (1, 5), (2, 6), (3, 7)], (0, 1)),
}
STEPS = 96


def grid_data(n, edges, cot, W, x, steps):
    """S, its inertia, det and norm on the grid, plus the phase derivatives."""
    g = [2 * math.pi * k / steps for k in range(steps)]
    dm = np.zeros((steps, steps), dtype=int)
    dt = np.zeros((steps, steps))
    nrm = np.zeros((steps, steps))
    S = np.zeros((steps, steps, 2, 2), dtype=complex)
    for i in range(steps):
        for j in range(steps):
            M = schur_2x2(magnetic(n, edges, cot, [g[i], g[j]]), x, list(W))
            M = 0.5 * (M + M.conj().T)
            S[i, j] = M
            w = np.linalg.eigvalsh(M)
            dm[i, j] = int(np.sum(w < 0))
            dt[i, j] = np.real(np.linalg.det(M))
            nrm[i, j] = np.max(np.abs(w))
    return S, dm, dt, nrm


def lipschitz(S, steps):
    """sqrt(sum_j sup ||dS/dtheta_j||^2) by centred differences on the grid."""
    h = 2 * math.pi / steps
    out = 0.0
    for ax in (0, 1):
        d = (np.roll(S, -1, axis=ax) - np.roll(S, 1, axis=ax)) / (2 * h)
        # operator norm of each 2x2, vectorised via singular values
        sv = np.linalg.svd(d.reshape(-1, 2, 2), compute_uv=False)
        out += float(sv.max()) ** 2
    return math.sqrt(out)


def reach_of(mask, steps):
    dist = -np.ones((steps, steps), dtype=int)
    q = deque()
    for i in range(steps):
        for j in range(steps):
            if not mask[i, j]:
                dist[i, j] = 0
                q.append((i, j))
    if not q:
        return math.pi
    while q:
        i, j = q.popleft()
        for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            a, b2 = (i + di) % steps, (j + dj) % steps
            if dist[a, b2] < 0:
                dist[a, b2] = dist[i, j] + 1
                q.append((a, b2))
    return (int(dist[mask].max()) if mask.any() else 0) * 2 * math.pi / steps


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    print(f"{'graph':>9}{'x':>9}{'m':>8}{'M':>7}{'L':>7}{'reach':>7}"
          f"{'I_wrong':>10}{'step1':>10}{'step2':>10}{'step3':>11}"
          f"{'Delta/2':>9}{'G44':>6}")
    anyfail = False
    for name, (n, edges, W) in GRAPHS.items():
        nF, eF = delete(n, edges, set(W))
        cF = matching_coeffs(nF, eF)
        tree, cot = spanning_tree(n, edges)
        if len(cot) != 2:
            print(f"{name:>9}   b = {len(cot)}, skipped")
            continue
        got = None
        for eta in (1e-4, 1e-3, 1e-2):
            es, ds, _ = scan(n, edges, -5.0, 5.0, 1200, eta=eta)
            if abs(kappa_above(es, ds, 1, -5.0) - 1.0) <= 0.03:
                got = (es, ds); break
        if got is None:
            print(f"{name:>9}   spec(T) unresolved"); continue
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.06]
        for lo, hi in internal:
            for frac in (0.15, 0.5, 0.85):
                x = lo + frac * (hi - lo)
                k = kappa_above(es, ds, n, x)
                delta = round(k) - roots_above(cF, x)
                S, dm, dt, nrm = grid_data(n, edges, cot, W, x, STEPS)
                wrong = (dm % 2) != (delta % 2)
                m = float(wrong.mean())
                if m < 1e-9:
                    print(f"{name:>9}{x:>9.4f}   wrong-parity region empty")
                    continue
                Iw = float(np.abs(dt)[wrong].mean())      # (1/|T|) int over A
                Msup = float(nrm[wrong].max())
                L = lipschitz(S, STEPS)
                r = reach_of(wrong, STEPS)
                Delta = math.exp(float(np.mean(np.log(np.abs(dt) + 1e-300))))
                s1 = m * float(np.abs(dt)[wrong].max())
                s2 = m * Msup * L * r
                s3 = 2 * math.sqrt(math.pi) * Msup * L * m ** 1.5
                ok = s3 < Delta / 2
                anyfail |= not ok
                print(f"{name:>9}{x:>9.4f}{m:>8.4f}{Msup:>7.3f}{L:>7.3f}{r:>7.3f}"
                      f"{Iw:>10.5f}{s1:>10.5f}{s2:>10.4f}{s3:>11.4f}"
                      f"{Delta/2:>9.4f}{('yes' if ok else 'NO'):>6}")
    print("\nstep1 to step3 are the successive weakenings of ShellBound. G44 is the last")
    print("column. A 'NO' with I_wrong far below Delta/2 means the chain is lossy, not")
    print("that the underlying inequality fails, and names the link that must be sharpened.")
    return 1 if anyfail else 0


if __name__ == '__main__':
    sys.exit(main())
