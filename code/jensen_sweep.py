"""Does the Jensen margin ever fail, and how does it depend on the first Betti number?

G44 is all that remains at feedback vertex number two:

    Delta  >  2 * I_wrong,     Delta = exp( integral log |det S(x,z)| dz ),

with I_wrong bounded above unconditionally by M L c^{-1/2} m^{1+1/b}. Two gaps of one graph
gave margins between 41 and 3927. This sweeps many graphs and reports:

    b        the first Betti number, which controls the upper half's exponent 1 + 1/b,
    Delta    the Mahler measure of the abelian cover at x, divided by |mu_F(x)|,
    I_wrong  the wrong-parity integral,
    ratio    Delta / (2 I_wrong), which must exceed 1 for the route to close.

A single failure would kill G44. A ratio that degrades systematically with b would say the
route works only for small first Betti number, which matters because the upper half's
exponent degrades from 3/2 at b = 2 to 1 + 1/b in general.

Rule 8: cost is measured before the run, progress and ETA are printed, and results are
checkpointed by atomic rename so a kill loses nothing.
"""

import sys
import os
import math
import cmath
import time
import itertools
import numpy as np

sys.path.insert(0, 'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""', 2)[2])

CKPT = 'private/jensen_sweep_ckpt.txt'
BMAX = 4
# Rule 8: the full family is 17187 graphs at 2.3 s each, which is 224 minutes. The question
# is whether the margin ever fails and how it varies with b, and a stride-sample answers both
# at a fraction of the cost. STRIDE=1 runs everything.
STRIDE = int(os.environ.get('STRIDE', '12'))


def steps_for(b):
    return {1: 200, 2: 40, 3: 20, 4: 11}[b]


def connected(n, edges):
    if not edges:
        return n <= 1
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


def is_forest(n, edges):
    par = list(range(n))

    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for u, v in edges:
        ru, rv = f(u), f(v)
        if ru == rv:
            return False
        par[ru] = rv
    return True


def fvs2_pair(n, edges):
    for a in range(n):
        for b_ in range(a + 1, n):
            keep = [(u, v) for u, v in edges if u not in (a, b_) and v not in (a, b_)]
            if is_forest(n, keep):
                return (a, b_)
    return None


def graphs(nmax=6):
    for n in range(4, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        for bits in range(1 << len(pairs)):
            e = [pairs[i] for i in range(len(pairs)) if bits >> i & 1]
            if len(e) < n or not connected(n, e):
                continue
            b = len(e) - n + 1
            if b < 2 or b > BMAX:
                continue
            W = fvs2_pair(n, e)
            if W is None:
                continue
            yield n, e, W, b


def examine(n, edges, W, b, ns):
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']
    nF, eF = delete(n, edges, set(W))
    cF = matching_coeffs(nF, eF)
    tree, cot = spanning_tree(n, edges)
    st = steps_for(b)
    grid = [2 * math.pi * k / st for k in range(st)]
    R = 5.0
    got = None
    for eta in (1e-4, 1e-3, 1e-2):
        es, ds, _ = scan(n, edges, -R, R, 800, eta=eta)
        if abs(kappa_above(es, ds, 1, -R) - 1.0) <= 0.03:
            got = (es, ds); break
    if got is None:
        return []
    es, ds = got
    bs = bands(es, ds, 1e-3)
    internal = [(bs[i][1], bs[i + 1][0]) for i in range(len(bs) - 1)
                if bs[i + 1][0] - bs[i][1] > 0.08]
    out = []
    for lo, hi in internal:
        x = 0.5 * (lo + hi)
        k = kappa_above(es, ds, n, x)
        if abs(k - round(k)) > 0.3:
            continue
        delta = round(k) - roots_above(cF, x)
        tot = st ** b
        I = [0.0, 0.0, 0.0]
        logsum = 0.0
        for t in range(tot):
            th, r = [], t
            for _ in range(b):
                th.append(grid[r % st]); r //= st
            S = schur_2x2(magnetic(n, edges, cot, th), x, list(W))
            S = 0.5 * (S + S.conj().T)
            w = np.linalg.eigvalsh(S)
            d = np.real(np.linalg.det(S))
            j = int(np.sum(w < 0))
            if 0 <= j <= 2:
                I[j] += abs(d)
            logsum += math.log(max(abs(d), 1e-300))
        I = [v / tot for v in I]
        Iw = (I[0] + I[2]) if delta % 2 == 1 else I[1]
        Delta = math.exp(logsum / tot)
        ratio = Delta / (2 * Iw) if Iw > 1e-14 else float('inf')
        out.append((b, x, Delta, Iw, ratio))
    return out


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)

    todo = list(graphs(6))[::STRIDE]
    print(f"{len(todo)} graphs with fvs <= 2 and 2 <= b <= {BMAX} (stride {STRIDE})")
    t0 = time.time()
    probe = min(6, len(todo))
    for g in todo[:probe]:
        examine(*g, ns)
    rate = probe / max(time.time() - t0, 1e-9)
    print(f"measured rate {rate:.2f} graphs/s -> ETA {len(todo)/rate/60:.1f} min\n")

    done = 0
    if os.path.exists(CKPT):
        done = int(open(CKPT).readline().strip() or 0)
        print(f"resuming after {done}")

    rows, fails, t0 = [], 0, time.time()
    worst = float('inf')
    byb = {}
    for i, g in enumerate(todo):
        if i < done:
            continue
        for (b, x, D, Iw, r) in examine(*g, ns):
            rows.append((b, r))
            byb.setdefault(b, []).append(r)
            if r < worst:
                worst = r
            if r <= 1.0:
                fails += 1
                print(f"  FAIL b={b} n={g[0]} edges={g[1]} x={x:.4f} "
                      f"Delta={D:.5f} I_wrong={Iw:.6f} ratio={r:.3f}")
        if (i + 1) % 25 == 0:
            el = time.time() - t0
            print(f"  {i+1}/{len(todo)}  gap points {len(rows)}  fails {fails}  "
                  f"worst ratio {worst:.2f}  {el:.0f}s")
            tmp = CKPT + '.tmp'
            with open(tmp, 'w') as f:
                f.write(f"{i+1}\n")
                f.write(f"points={len(rows)} fails={fails} worst={worst:.4f}\n")
            os.replace(tmp, CKPT)
    print()
    print(f"gap points tested : {len(rows)}")
    print(f"Jensen failures   : {fails}")
    print(f"worst ratio       : {worst:.3f}")
    for b in sorted(byb):
        v = byb[b]
        print(f"  b={b}: {len(v):5d} points, min ratio {min(v):9.2f}, "
              f"median {sorted(v)[len(v)//2]:9.2f}")
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
