"""Attack A8: is the |Q|-weighted mean of the crossing band inside spec(T)?

ParitySplit reduces Conjecture 10 at a point where exactly one band crosses x to

    mu_G(x) = 0   iff   x = ( integral lambda_k0 |Q| ) / ( integral |Q| ),   Q = prod_{k != k0} (x - lambda_k).

So the conjecture holds at such a point as soon as that weighted mean differs from x. The
strong form, which would prove it, is that the mean always lies in spec(T), since x lies in a
gap. Rule 3 says try to break that before trying to prove it.

Reported per residue point with kappa = 1:

    wmean       the |Q|-weighted mean of the crossing band,
    |wmean - x| what actually has to be nonzero,
    in spec(T)  whether the strong form holds there,
    frac        where x sits in its gap, since a failure at an edge and a failure in the
                middle mean different things.

A single point with wmean = x refutes Conjecture 10 outright, so this is also a direct test of
the conjecture. A point with wmean outside spec(T) but different from x leaves the conjecture
intact and kills only the strong form, which would say the route needs the weaker statement.
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

CKPT = quickmode.ckpt('private/wmean_ckpt.txt')
STRIDE = int(os.environ.get('STRIDE', '600'))
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
    A0 = np.zeros((n, n), dtype=complex)
    ci = {i: j for j, i in enumerate(cot)}
    for i, (u, v) in enumerate(edges):
        if i not in ci:
            A0[u, v] += 1.0
            A0[v, u] += 1.0
    M = S ** b
    A = np.broadcast_to(A0, (M, n, n)).copy()
    th = 2 * math.pi * np.arange(S) / S
    for i, (u, v) in enumerate(edges):
        if i in ci:
            w = np.exp(1j * th[(np.arange(M) // (S ** ci[i])) % S])
            A[:, u, v] += w
            A[:, v, u] += np.conj(w)
    return np.linalg.eigvalsh(A)


def in_spec(bs, t, tol=1e-9):
    return any(lo - tol <= t <= hi + tol for lo, hi in bs)


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
        lam = spectra(n, edges, cot, GRID[b], b)
        lo, hi = lam.min(axis=0), lam.max(axis=0)
        out = []
        for a_, c_ in internal:
            for f in quickmode.few((0.05, 0.2, 0.35, 0.5, 0.65, 0.8, 0.95), 2):
                x = a_ + f * (c_ - a_)
                cross = [k for k in range(n) if lo[k] <= x <= hi[k]]
                if len(cross) != 1:
                    # kappa = 0 is settled by the localization and is not residue at all;
                    # only kappa >= 2 is residue the weighted-mean reduction misses.
                    out.append((b, len(cross), None, None, None, f))
                    continue
                k0 = cross[0]
                Q = np.prod(np.delete(x - lam, k0, axis=1), axis=1)
                aQ = np.abs(Q)
                sQ = float(aQ.sum())
                if sQ <= 0:
                    continue
                wm = float((lam[:, k0] * aQ).sum() / sQ)
                out.append((b, 1, wm, abs(wm - x), in_spec(bs, wm), f))
        return out

    t0 = time.time()
    probe = min(4, len(todo))
    for g in todo[:probe]:
        run(*g)
    rate = probe / max(time.time() - t0, 1e-9)
    print(f"measured rate {rate:.2f} graphs/s -> ETA {len(todo)/rate/60:.1f} min\n",
          flush=True)

    rows = k0 = k1 = kbig = inspec = 0
    mind = float('inf')
    worst = None
    t0 = time.time()
    for i, g in enumerate(todo):
        for (b, kap, wm, d, insp, f) in run(*g):
            rows += 1
            if kap == 0:
                k0 += 1
                continue
            if kap != 1:
                kbig += 1
                continue
            k1 += 1
            inspec += 1 if insp else 0
            if d < mind:
                mind, worst = d, (b, g[0], g[1], wm, f, insp)
            if d < 1e-6:
                print(f"  REFUTATION b={b} n={g[0]} edges={g[1]} wmean={wm:.9f} "
                      f"frac={f}", flush=True)
        if (i + 1) % 10 == 0:
            print(f"  {i+1}/{len(todo)}  pts {rows}  k=0 {k0}  k=1 {k1}  k>=2 {kbig}  "
                  f"in spec(T) {inspec}  min |wmean-x| {mind:.5f}  "
                  f"{time.time()-t0:.0f}s", flush=True)
            tmp = CKPT + '.tmp'
            with open(tmp, 'w') as f2:
                f2.write(f"{i+1}/{len(todo)} rows={rows} k0={k0} k1={k1} kbig={kbig} "
                         f"inspec={inspec} mind={mind:.6f}\n")
            os.replace(tmp, CKPT)

    print(f"\ngap points tested     : {rows}")
    print(f"  kappa = 0 (settled) : {k0}")
    print(f"  kappa = 1 (reduced) : {k1}")
    print(f"  kappa >= 2 (missed) : {kbig}")
    res = k1 + kbig
    if res:
        print(f"weighted-mean reduction covers {100*k1/res:.1f}% of the residue")
    if k1:
        print(f"weighted mean in spec(T): {inspec}/{k1}  ({100*inspec/k1:.1f}%)")
    print(f"min |wmean - x|       : {mind:.6f}   (0 would refute Conjecture 10)")
    print(f"attained at           : {worst}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
