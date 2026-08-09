"""A criterion that separates the band geometry from the weight, for every crossing number.

Let K be the set of bands whose range contains x, and put

    pi(z) = prod_{k in K} (x - lambda_k(z)),    w(z) = |prod_{k not in K} (x - lambda_k(z))|.

The factors outside K never vanish, so their product has constant sign s and

    mu_G(x) = s * integral pi w.

Writing pi = pi_+ - pi_- and bounding w by its extremes IN EACH TERM SEPARATELY,

    integral pi w  >=  inf(w) J_+  -  sup(w) J_-,        J_pm = integral pi_pm,

so     J_+ / J_-  >  Lambda := sup(w) / inf(w)     is SUFFICIENT for mu_G(x) != 0.

Two things make this worth measuring. J_+ and J_- depend only on the crossing bands and not
on the weight, while Lambda depends only on the weight and not on where x sits, so the two
halves can be attacked separately. And nothing here constrains |K|, so it applies at every
residue point rather than only where one band crosses.

It is not the wasteful bound that was tried before. Applying sup(w) to the whole integrand
loses four orders of magnitude, since sup(w)/inf(w) reaches 5.4e4; here inf(w) goes on the
majority term and sup(w) only on the minority term.

Reported per point: the minority measure, J_+/J_-, Lambda, whether the criterion fires, and
the true ratio I_-/I_+ so the loss of the criterion against the truth is visible.

Rule 8: kept deliberately under five minutes by striding, and the sample size is reported.
The kappa >= 2 points are rare in a sample this size, so this run says almost nothing about
them.
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

STRIDE = int(os.environ.get('STRIDE', '5000'))
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
        for eta in (1e-4, 1e-3, 1e-2):
            es, ds, _ = scan(n, edges, -5.5, 5.5, 600, eta=eta)
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
            for f in (0.05, 0.25, 0.5, 0.75, 0.95):
                x = a_ + f * (c_ - a_)
                cross = [k for k in range(n) if lo[k] <= x <= hi[k]]
                kap = len(cross)
                if kap == 0:
                    continue                      # settled by the localization
                # pi over the crossing bands, w over the rest. No constraint on kappa.
                pi = np.prod(x - lam[:, cross], axis=1)
                aQ = np.abs(np.prod(np.delete(x - lam, cross, axis=1), axis=1))
                if aQ.min() <= 0:
                    continue
                Jp = float(np.mean(np.clip(pi, 0, None)))
                Jm = float(np.mean(np.clip(-pi, 0, None)))
                if Jp <= 0 or Jm <= 0:
                    continue
                Lam = float(aQ.max() / aQ.min())
                # WeightBound: Lambda <= product over non-crossing bands of the per-band
                # ratio, each equal to 1 + width / dist(x, band). Purely band geometry.
                Gb = 1.0
                for k in range(n):
                    if k in cross:
                        continue
                    if hi[k] < x:
                        Gb *= (x - lo[k]) / (x - hi[k])
                    else:
                        Gb *= (hi[k] - x) / (lo[k] - x)
                Ip = float(np.mean(np.clip(pi, 0, None) * aQ))
                Im = float(np.mean(np.clip(-pi, 0, None) * aQ))
                # orient so the majority side is first
                if Jp < Jm:
                    Jp, Jm = Jm, Jp
                    Ip, Im = Im, Ip
                m1 = min(float((pi > 0).mean()), float((pi < 0).mean()))
                out.append((b, m1, Jp / Jm, Lam, Im / Ip, Jp / Jm > Lam, kap, Gb,
                            Jp / Jm > Gb))
        return out

    t0 = time.time()
    rows, fires = [], 0
    for i, g in enumerate(todo):
        for r in run(*g):
            rows.append(r)
            fires += 1 if r[5] else 0
    el = time.time() - t0
    if not rows:
        print("no kappa = 1 points"); return 0
    JL = [r[2] / r[3] for r in rows]
    kh = {}
    for r in rows:
        kh.setdefault(r[6], [0, 0])
        kh[r[6]][0] += 1
        kh[r[6]][1] += 1 if r[5] else 0
    print(f"\nresidue points        : {len(rows)}   ({el:.0f}s)")
    print(f"criterion J+/J- > Lam : {fires}/{len(rows)}  ({100*fires/len(rows):.1f}%)")
    print(f"worst J+/J- over Lam  : {min(JL):.4g}   (must exceed 1 for the criterion)")
    print(f"median                : {sorted(JL)[len(JL)//2]:.4g}")
    print(f"true worst I-/I+      : {max(r[4] for r in rows):.6f}   (must stay below 1)")
    gfires = sum(1 for r in rows if r[8])
    GL = [r[2] / r[7] for r in rows]
    print(f"band-geometry form    : {gfires}/{len(rows)}  ({100*gfires/len(rows):.1f}%)")
    print(f"worst J+/J- over Gb   : {min(GL):.4g}")
    print(f"Gb/Lambda (slack lost): median {sorted(r[7]/r[3] for r in rows)[len(rows)//2]:.3g}"
          f", max {max(r[7]/r[3] for r in rows):.3g}")
    for k in sorted(kh):
        t, f_ = kh[k]
        print(f"  kappa={k}: {t:5d} points, criterion fires {f_}/{t} "
              f"({100*f_/t:.1f}%)")
    print(f"\n{'b':>3}{'kap':>4}{'minor':>8}{'J+/J-':>12}{'Lambda':>12}{'Gbound':>12}"
          f"{'J/Gb':>9}{'I-/I+':>10}{'fires':>7}")
    for r in sorted(rows, key=lambda r: r[2] / r[7])[:12]:
        print(f"{r[0]:>3}{r[6]:>4}{r[1]:>8.4f}{r[2]:>12.4g}{r[3]:>12.4g}{r[7]:>12.4g}"
              f"{r[2]/r[7]:>9.3g}{r[4]:>10.5f}{('yes' if r[8] else 'NO'):>7}")
    print("\nThe twelve worst points are shown. Where the criterion fails, compare I+/I- to")
    print("see how much of the gap is the crude weight bound and how much is real.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
