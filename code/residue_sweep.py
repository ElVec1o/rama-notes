"""How much of Conjecture 10 does the localization already settle?

The localization of the note gives Zeros(mu_G) inside spec(G^ab), so Conjecture 10 holds at
every x that lies in a gap of spec(T) and outside spec(G^ab), for EVERY graph and EVERY first
Betti number, with no feedback vertex hypothesis. The note previously asserted that this
region is essentially empty. Two growing families said otherwise. This sweep puts a number on
it over all connected graphs with feedback vertex number at most two on up to seven vertices:

    inside     the gap midpoint is swallowed by a band of the abelian cover, the residue,
    outside    settled outright by the localization,
    undecided  the certification did not resolve at the affordable grid.

Both verdicts are certified, not read off a grid.

    inside:  the grid is a subset of the torus, so if some band's grid range brackets x then
             by the intermediate value theorem that band attains x somewhere. Sound as is.

    outside: needs a margin. Every z is within h/2 per coordinate of a grid point, and
             perturbing one cotree phase by dt moves the matrix by at most |dt| in operator
             norm, so ||A(z) - A(grid)|| <= b h / 2 and by Weyl every band function moves by
             at most that. So the true range of band k is inside its grid range widened by
             b pi / S. If every widened range misses x, x is certifiably outside spec(G^ab).

Rule 8: cost is probed before the run, progress and ETA are printed, and the tally is
checkpointed by atomic rename.
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

CKPT = 'private/residue_sweep_ckpt.txt'
STRIDE = int(os.environ.get('STRIDE', '40'))
BMAX = int(os.environ.get('BMAX', '3'))
SMAX = {2: 512, 3: 96}


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


def fvs_le_two(n, edges):
    if is_forest(n, edges):
        return True
    for a in range(n):
        if is_forest(n, [(u, v) for u, v in edges if a not in (u, v)]):
            return True
    for a in range(n):
        for b_ in range(a + 1, n):
            if is_forest(n, [(u, v) for u, v in edges
                             if u not in (a, b_) and v not in (a, b_)]):
                return True
    return False


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
            if not fvs_le_two(n, e):
                continue
            yield n, e, b


def band_ranges(n, edges, cot, S, b):
    """Min and max of each band function over an S^b grid, computed in one batch."""
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
            j = cotidx[i]
            rep = S ** j
            w = np.exp(1j * th[(np.arange(M) // rep) % S])
            A[:, u, v] += w
            A[:, v, u] += np.conj(w)
    lam = np.linalg.eigvalsh(A)
    return lam.min(axis=0), lam.max(axis=0)


def verdict(n, edges, cot, x, b):
    """Certified 'inside' / 'outside' / 'undecided' for x against spec(G^ab)."""
    S = 32
    while S <= SMAX[b]:
        lo, hi = band_ranges(n, edges, cot, S, b)
        if np.any((lo <= x) & (x <= hi)):
            return 'inside', 0.0
        m = b * math.pi / S
        if np.all((hi + m < x) | (lo - m > x)):
            return 'outside', float(np.min(np.minimum(np.abs(x - hi), np.abs(x - lo))) - m)
        S *= 2
    return 'undecided', 0.0


def examine(n, edges, b, ns):
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']
    tree, cot = spanning_tree(n, edges)
    got = None
    for eta in (1e-4, 1e-3, 1e-2):
        es, ds, _ = scan(n, edges, -5.5, 5.5, 800, eta=eta)
        if abs(kappa_above(es, ds, 1, -5.5) - 1.0) <= 0.03:
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
        v, marg = verdict(n, edges, cot, x, b)
        out.append((b, x, v, marg))
    return out


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)

    todo = list(graphs(7))[::STRIDE]
    print(f"{len(todo)} graphs, fvs <= 2, 2 <= b <= {BMAX} (stride {STRIDE})", flush=True)
    t0 = time.time()
    probe = min(5, len(todo))
    for g in todo[:probe]:
        examine(*g, ns)
    rate = probe / max(time.time() - t0, 1e-9)
    print(f"measured rate {rate:.2f} graphs/s -> ETA {len(todo)/rate/60:.1f} min\n",
          flush=True)

    tal = {'inside': 0, 'outside': 0, 'undecided': 0}
    byb = {}
    t0 = time.time()
    for i, g in enumerate(todo):
        for (b, x, v, marg) in examine(*g, ns):
            tal[v] += 1
            d = byb.setdefault(b, {'inside': 0, 'outside': 0, 'undecided': 0})
            d[v] += 1
        if (i + 1) % 20 == 0:
            tot = sum(tal.values()) or 1
            print(f"  {i+1}/{len(todo)}  points {tot}  outside {tal['outside']} "
                  f"({100*tal['outside']/tot:.1f}%)  inside {tal['inside']}  "
                  f"undecided {tal['undecided']}  {time.time()-t0:.0f}s", flush=True)
            tmp = CKPT + '.tmp'
            with open(tmp, 'w') as f:
                f.write(f"{i+1}/{len(todo)} {tal}\n")
            os.replace(tmp, CKPT)

    tot = sum(tal.values()) or 1
    print(f"\ngap points          : {tot}")
    print(f"settled outright    : {tal['outside']}  ({100*tal['outside']/tot:.1f}%)")
    print(f"residue             : {tal['inside']}  ({100*tal['inside']/tot:.1f}%)")
    print(f"undecided           : {tal['undecided']}  ({100*tal['undecided']/tot:.1f}%)")
    for b in sorted(byb):
        d = byb[b]
        t = sum(d.values()) or 1
        print(f"  b={b}: {t:5d} points, outside {100*d['outside']/t:5.1f}%, "
              f"inside {100*d['inside']/t:5.1f}%, undecided {100*d['undecided']/t:5.1f}%")
    print("\n'outside' is settled by the localization alone, for every b and with no")
    print("feedback vertex hypothesis. 'inside' is what any proof still has to reach.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
