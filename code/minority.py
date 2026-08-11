"""The crux, measured without a feedback vertex set and without mu_F.

The Schur complement is a computational device, not part of the statement. Dropping it:

    mu_G(x) = integral over T^b of P_x(z),   P_x(z) = det(xI - A_G(z)) = prod_k (x - lambda_k(z)),

so with N(z) = #{k : lambda_k(z) > x} the sign of P_x is (-1)^{N(z)} and

    mu_G(x) = I_even - I_odd,   I_p = integral over {N = p mod 2} of |P_x|.

Conjecture 10 at x is exactly I_even != I_odd. This formulation has no feedback vertex
hypothesis, no restriction on the first Betti number, and no mu_F, so it does not blow up
near roots of mu_F, which is where the Schur version of G44 fails: there sup||S|| and the
Lipschitz constant both scale like 1/mu_F(x) while Delta scales like 1/mu_F(x), so the bound
loses by a whole factor of mu_F.

It also makes the Lipschitz constant exact. dA/dtheta_j has a single entry of modulus one and
its conjugate, so its operator norm is exactly 1, and Weyl gives

    |lambda_k(z) - lambda_k(w)| <= ||A(z) - A(w)|| <= sum_j |dtheta_j| <= sqrt(b) |dtheta|_2,

that is L = sqrt(b), unconditionally, with nothing to measure.

What is left to establish is that the minority class does not catch up with the majority. The
decisive quantity is

    m = min( |{N even}| , |{N odd}| ),

the measure of the minority-parity region. If m can approach 1/2 while x sits in a gap of
spec(T), the cancellation is near total and every estimate of this shape dies. If m stays
small, that is a structural fact about gaps of the universal cover and is the theorem to aim
at. This script measures m, the number of bands that actually cross x, and the ground truth
ratio min(I_even, I_odd) / max(I_even, I_odd), which must stay below 1.

Rule 3: this is a falsification run. A single point with ratio 1 kills the whole route.
"""

import sys
import os
import math
import cmath
import time
import itertools
import numpy as np
import quickmode

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

CKPT = quickmode.ckpt('private/minority_ckpt.txt')
STRIDE = int(os.environ.get('STRIDE', '250'))
BMAX = int(os.environ.get('BMAX', '3'))
GRID = {2: 96, 3: 28}


def connected(n, edges):
    adj = {i: [] for i in range(n)}
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    seen, st = {0}, [0]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == n


def graphs(nmax=7):
    for n in range(4, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        for bits in range(1 << len(pairs)):
            e = [pairs[i] for i in range(len(pairs)) if bits >> i & 1]
            if len(e) < n or not connected(n, e):
                continue
            b = len(e) - n + 1
            if b < 2 or b > BMAX:
                continue
            yield n, e, b


def spectra(n, edges, cot, S, b):
    """All eigenvalues on an S^b torus grid, one batched call."""
    A0 = np.zeros((n, n), dtype=complex)
    cotidx = {i: j for j, i in enumerate(cot)}
    for i, (u, v) in enumerate(edges):
        if i not in cotidx:
            A0[u, v] += 1.0
            A0[v, u] += 1.0
    M = S ** b
    A = np.broadcast_to(A0, (M, n, n)).copy()
    th = 2 * math.pi * np.arange(S) / S
    for i, (u, v) in enumerate(edges):
        if i in cotidx:
            w = np.exp(1j * th[(np.arange(M) // (S ** cotidx[i])) % S])
            A[:, u, v] += w
            A[:, v, u] += np.conj(w)
    return np.linalg.eigvalsh(A)


def at(lam, x):
    """Minority measure, crossing-band count, and the two parity integrals."""
    above = lam > x
    N = above.sum(axis=1)
    P = np.prod(x - lam, axis=1)
    ev = (N % 2) == 0
    m_ev = float(ev.mean())
    m = min(m_ev, 1.0 - m_ev)
    Ie = float(np.abs(P)[ev].sum()) / lam.shape[0]
    Io = float(np.abs(P)[~ev].sum()) / lam.shape[0]
    lo, hi = lam.min(axis=0), lam.max(axis=0)
    kappa = int(np.sum((lo <= x) & (x <= hi)))
    ratio = min(Ie, Io) / max(Ie, Io) if max(Ie, Io) > 0 else 0.0
    # does the minority-measure class also carry the minority integral?
    aligned = (m_ev <= 0.5) == (Ie <= Io)
    return m, kappa, ratio, aligned


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    todo = list(graphs(7))[::STRIDE]
    print(f"{len(todo)} graphs, 2 <= b <= {BMAX} (stride {STRIDE})", flush=True)

    def run(n, edges, b):
        tree, cot = spanning_tree(n, edges)
        got = None
        for eta in quickmode.few((1e-4, 1e-3, 1e-2)):
            es, ds, _ = scan(n, edges, -5.5, 5.5, 800, eta=eta)
            if abs(kappa_above(es, ds, 1, -5.5) - 1.0) <= 0.03:
                got = (es, ds); break
        if got is None:
            return []
        es, ds = got
        bs = bands(es, ds, 1e-3)
        internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                    if bs[i + 1][0] - bs[i][1] > 0.08]
        if not internal:
            return []
        lamcache = spectra(n, edges, cot, GRID[b], b)
        out = []
        for lo, hi in internal:
            for f in quickmode.few((0.05, 0.2, 0.35, 0.5, 0.65, 0.8, 0.95), 2):
                x = lo + f * (hi - lo)
                m, kap, r, al = at(lamcache, x)
                if kap == 0:
                    continue                     # settled by the localization
                out.append((b, m, kap, r, al))
        return out

    t0 = time.time()
    probe = min(4, len(todo))
    for g in todo[:probe]:
        run(*g)
    rate = probe / max(time.time() - t0, 1e-9)
    print(f"measured rate {rate:.2f} graphs/s -> ETA {len(todo)/rate/60:.1f} min\n",
          flush=True)

    worst_m, worst_r, nmis, rows = 0.0, 0.0, 0, 0
    khist = {}
    t0 = time.time()
    for i, g in enumerate(todo):
        for (b, m, kap, r, al) in run(*g):
            rows += 1
            khist[kap] = khist.get(kap, 0) + 1
            worst_m = max(worst_m, m)
            worst_r = max(worst_r, r)
            nmis += (0 if al else 1)
            if r > 0.999:
                print(f"  NEAR CANCELLATION b={b} n={g[0]} edges={g[1]} "
                      f"m={m:.4f} kappa={kap} ratio={r:.6f}", flush=True)
        if (i + 1) % 10 == 0:
            print(f"  {i+1}/{len(todo)}  residue points {rows}  max m {worst_m:.4f}  "
                  f"max ratio {worst_r:.6f}  misaligned {nmis}  "
                  f"{time.time()-t0:.0f}s", flush=True)
            tmp = CKPT + '.tmp'
            with open(tmp, 'w') as f:
                f.write(f"{i+1}/{len(todo)} rows={rows} max_m={worst_m:.4f} "
                        f"max_ratio={worst_r:.6f} misaligned={nmis}\n")
            os.replace(tmp, CKPT)

    print(f"\nresidue points          : {rows}")
    print(f"largest minority measure: {worst_m:.4f}   (1/2 would be total cancellation)")
    print(f"largest integral ratio  : {worst_r:.6f}   (1 would falsify Conjecture 10)")
    print(f"misaligned              : {nmis}   (minority by measure but majority by integral)")
    print(f"crossing bands kappa    : {dict(sorted(khist.items()))}")
    print("kappa = 1 is the case the weighted-mean reduction covers. Any kappa >= 2 point is")
    print("outside it and needs the general parity split.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
