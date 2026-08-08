"""Redo the b = 3 verdicts with a certificate that can actually fire.

residue_sweep.py certifies 'x outside spec(G^ab)' by widening each band's grid range by the
Weyl margin b*pi/S. At b = 2 with S up to 512 that margin is 0.012 and the test is sharp. At
b = 3 the affordable grid was S = 96, giving a margin of 0.098, which is wider than the
half-width of the gaps being tested, so the test can essentially never succeed. Its b = 3 row,
0.2 percent outside and 22 percent undecided, measures the grid and not the mathematics.

The fix is to certify on the determinant instead of the bands. f(z) = det(xI - A_G(z)) has
degree one in each z_e, so its 3^b Fourier coefficients are exact from a three-point
transform, and they bound the gradient directly:

    |df/dtheta_j| <= sum over alpha of |alpha_j| |c_alpha|.

That constant adapts to the polynomial rather than to the worst case, and on b = 2 it gave
margins from 1.4 to 51 where the crude bound gave nothing. A sign change on the grid still
certifies 'inside' by the intermediate value theorem, and the cheap band test is kept as a
first pass because it is sound in that direction and costs almost nothing.

Rule 3 and Rule 7: both verdicts are certificates, never grid readings.
"""

import sys
import os
import math
import cmath
import time
import itertools
import numpy as np

sys.path.insert(0, 'code')
g = {}
exec(open('code/torus_gg.py').read().split("def main():")[0], g)
coeffs, spanning_tree = g['coeffs'], g['spanning_tree']
magnetic = g['magnetic']

CKPT = 'private/residue_b3_ckpt.txt'
STRIDE = int(os.environ.get('STRIDE', '400'))


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
            if len(e) - n + 1 != 3:
                continue
            yield n, e


def batch(n, edges, cot, S, b):
    """det(xI - A) needs the matrices; return the batched A on an S^b grid."""
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
    return A


def verdict(n, edges, cot, x, b=3):
    """Certified verdict, band test first then the determinant certificate."""
    # cheap sound test for 'inside'
    A = batch(n, edges, cot, 32, b)
    lam = np.linalg.eigvalsh(A)
    lo, hi = lam.min(axis=0), lam.max(axis=0)
    if np.any((lo <= x) & (x <= hi)):
        return 'inside', 0.0
    c = coeffs(n, edges, cot, x)
    L = 0.0
    for idx in itertools.product(range(3), repeat=b):
        a = [0 if k == 0 else (1 if k == 1 else -1) for k in idx]
        L += sum(abs(v) for v in a) * abs(c[idx])
    S = 48
    while S <= 160:
        A = batch(n, edges, cot, S, b)
        d = np.real(np.linalg.det(x * np.eye(n) - A))
        if d.min() < 0 < d.max():
            return 'inside', 0.0
        lb = float(np.abs(d).min()) - L * (2 * math.pi / S) * math.sqrt(b) / 2
        if lb > 0:
            return 'outside', lb
        S *= 2
    return 'undecided', 0.0


def main():
    ns = {}
    exec(open('code/universal_cover.py').read().replace(
        "if __name__ == '__main__':", 'if False:'), ns)
    scan, kappa_above, bands = ns['scan'], ns['kappa_above'], ns['bands']

    todo = list(graphs(7))[::STRIDE]
    print(f"{len(todo)} graphs with b = 3 (stride {STRIDE})", flush=True)

    def run(n, edges):
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
        return [verdict(n, edges, cot, 0.5 * (a + b_)) for a, b_ in internal]

    t0 = time.time()
    probe = min(3, len(todo))
    for gph in todo[:probe]:
        run(*gph)
    rate = probe / max(time.time() - t0, 1e-9)
    print(f"measured rate {rate:.2f} graphs/s -> ETA {len(todo)/rate/60:.1f} min\n",
          flush=True)

    tal = {'inside': 0, 'outside': 0, 'undecided': 0}
    t0 = time.time()
    for i, gph in enumerate(todo):
        for v, lb in run(*gph):
            tal[v] += 1
        if (i + 1) % 10 == 0:
            tot = sum(tal.values()) or 1
            print(f"  {i+1}/{len(todo)}  points {tot}  outside {tal['outside']} "
                  f"({100*tal['outside']/tot:.1f}%)  inside {tal['inside']}  "
                  f"undecided {tal['undecided']}  {time.time()-t0:.0f}s", flush=True)
            tmp = CKPT + '.tmp'
            with open(tmp, 'w') as f:
                f.write(f"{i+1}/{len(todo)} {tal}\n")
            os.replace(tmp, CKPT)
    tot = sum(tal.values()) or 1
    print(f"\nb = 3 gap points : {tot}")
    print(f"settled outright : {tal['outside']}  ({100*tal['outside']/tot:.1f}%)")
    print(f"residue          : {tal['inside']}  ({100*tal['inside']/tot:.1f}%)")
    print(f"undecided        : {tal['undecided']}  ({100*tal['undecided']/tot:.1f}%)")
    print("\nCompare residue_sweep.py's b = 3 row, which used a Weyl margin too wide to fire.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
