"""Is the soft-edge exponent universal, and what is the constant?

The margin between the smallest positive root of mu_G and the inner edge g = sqrt(q-1) -
sqrt(d-1) of the (d,q)-biregular tree spectrum decays like n^(-2/3) for (3,6) and (3,9), fitted
at R^2 = 0.9999 and 0.9995 (code/softedge.py). Two questions decide whether that is a law or an
accident of d = 3.

FROZEN BEFORE THIS DATA:
  P5. The exponent is -2/3 in every (d,q) family, not only d = 3.
  P6. In the y = x^2 variable, where the polynomial has degree r and r is the natural matrix
      size, the constant C_y in  y_min - g^2 = C_y r^(-2/3)  is a simple function of the
      biregular tree spectrum, and the candidate tested is C_y proportional to the band
      half-width sqrt(d-1) + sqrt(q-1).

P6 is the one that matters, because a recognisable constant is what a Friedman-type theorem
would have to reproduce, and because the x-variable fit mixes in the aspect ratio n / r.

TWO FIXES over the previous run, both of which were the bottleneck rather than the mathematics.

  Generation. The configuration-model shuffle rejected almost every sample at d = 4, 5, which
  is why those families had too few points to fit. Replaced by a deterministic biregular base,
  left vertex i joined to right (i d + j) mod r, which is exactly biregular because i d + j runs
  over all of 0 .. rq-1, followed by degree-preserving double-edge swaps. This never rejects.

  Counting. The bitmask permanent is now vectorised over states, so each left vertex costs one
  pass of 2^r rather than a Python loop, which moves the reachable r from about 16 to about 19.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import time
import random
import numpy as np
import sympy as sp

y = sp.Symbol('y')
BUDGET = 1700.0
CKPT = 'private/softedge2_ckpt.txt'


# ------------------------------------------------------------------ generation
def biregular_base(d, q, r):
    """left i joined to right (i*d + j) mod r: exactly biregular, since i*d+j covers 0..rq-1."""
    if (r * q) % d or d > r:
        return None
    m = (r * q) // d
    return m, [sorted({(i * d + j) % r for j in range(d)}) for i in range(m)]


def swap_randomize(m, r, nbr, seed, rounds=40):
    """degree-preserving double-edge swaps; keeps the graph simple and biregular."""
    rng = random.Random(seed * 104729 + r * 31 + 7)
    nb = [set(s) for s in nbr]
    for _ in range(rounds * m):
        a, b = rng.randrange(m), rng.randrange(m)
        if a == b:
            continue
        xa = list(nb[a] - nb[b])
        xb = list(nb[b] - nb[a])
        if not xa or not xb:
            continue
        u, v = rng.choice(xa), rng.choice(xb)
        nb[a].discard(u); nb[a].add(v)
        nb[b].discard(v); nb[b].add(u)
    return [sorted(s) for s in nb]


def connected(m, r, nbr):
    adj = {i: set() for i in range(m + r)}
    for i, s in enumerate(nbr):
        for j in s:
            adj[i].add(m + j); adj[m + j].add(i)
    st, vis = [0], {0}
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in vis:
                vis.add(w); st.append(w)
    return len(vis) == m + r


def check_biregular(m, r, nbr, d, q):
    if any(len(s) != d for s in nbr):
        return False
    deg = [0] * r
    for s in nbr:
        for j in s:
            deg[j] += 1
    return all(t == q for t in deg)


# ------------------------------------------------------------------ counting
def matching_counts(m, r, nbr):
    """m_k for k = 0..r, exactly, by a vectorised bitmask permanent over the small side."""
    size = 1 << r
    idx = np.arange(size, dtype=np.int64)
    free = [idx[(idx & (1 << j)) == 0] for j in range(r)]
    dp = np.zeros(size, dtype=np.int64)
    dp[0] = 1
    for s in nbr:
        delta = np.zeros(size, dtype=np.int64)
        for j in s:
            src = free[j]
            np.add.at(delta, src | (1 << j), dp[src])
        dp += delta
        if dp.max() > (1 << 61):
            return None
    pc = np.zeros(size, dtype=np.int64)
    for j in range(r):
        pc[(idx & (1 << j)) != 0] += 1
    out = np.zeros(r + 1, dtype=object)
    for k in range(r + 1):
        out[k] = int(dp[pc == k].sum())
    return list(out)


def ymin_from_counts(mk, r):
    co = [((-1) ** k) * int(mk[k]) for k in range(r + 1)]
    while co and co[-1] == 0:
        co.pop()
    if len(co) < 2:
        return None
    try:
        rs = sorted(sp.re(t) for t in sp.Poly(co, y).nroots(n=30, maxsteps=6000)
                    if abs(sp.im(t)) < 1e-18 and sp.re(t) > 1e-14)
    except Exception:
        return None
    return float(rs[0]) if rs else None


def main():
    print("P5: the exponent is -2/3 in every (d,q).")
    print("P6: C_y in  y_min - g^2 = C_y r^(-2/3)  tracks the band half-width s+t.\n")
    print(f"{'family':>9}{'r':>4}{'n':>5}{'best y_min':>12}{'margin_y':>11}"
          f"{'margin_x':>11}{'samples':>9}")
    t0 = time.time()
    T = {}
    FAM = ((3, 6), (3, 9), (3, 12), (4, 8), (4, 12), (5, 10), (5, 15), (6, 12))
    for (d, q) in FAM:
        g = math.sqrt(q - 1) - math.sqrt(d - 1)
        for r in range(max(d, 5), 19):
            if time.time() - t0 > BUDGET:
                break
            base = biregular_base(d, q, r)
            if base is None:
                continue
            m, nbr0 = base
            n = m + r
            if n > 90 or r > 18:
                continue
            best, used = None, 0
            for seed in range(8):
                if time.time() - t0 > BUDGET:
                    break
                nbr = swap_randomize(m, r, nbr0, seed)
                if not check_biregular(m, r, nbr, d, q) or not connected(m, r, nbr):
                    continue
                mk = matching_counts(m, r, nbr)
                if mk is None:
                    continue
                ym = ymin_from_counts(mk, r)
                if ym is None:
                    continue
                used += 1
                if best is None or ym < best:
                    best = ym
            if best is None or used < 2:
                continue
            my = best - g * g
            mx = math.sqrt(best) - g
            T.setdefault((d, q), []).append((r, n, my, mx))
            print(f"{f'({d},{q})':>9}{r:>4}{n:>5}{best:>12.6f}{my:>11.6f}"
                  f"{mx:>11.6f}{used:>9}", flush=True)
            with open(CKPT + '.tmp', 'w') as f:
                f.write(f"({d},{q}) r={r} margin_y={my:.6f}\n")
            os.replace(CKPT + '.tmp', CKPT)
        print()

    import json
    json.dump({f"{d},{q}": v for (d, q), v in T.items()},
              open('private/softedge2_data.json', 'w'))
    print(f"{time.time()-t0:.0f}s\n")
    print(f"{'family':>9}{'pts':>5}{'exp in r (y)':>14}{'R^2':>8}{'C_y':>10}"
          f"{'exp in n (x)':>14}{'s+t':>8}{'C_y/(s+t)':>11}")
    exps, rows = [], []
    for (d, q), data in sorted(T.items()):
        if len(data) < 5:
            continue
        rs = np.log(np.array([t[0] for t in data], float))
        ns = np.log(np.array([t[1] for t in data], float))
        ys = np.log(np.array([t[2] for t in data], float))
        xs = np.log(np.array([t[3] for t in data], float))
        ay, by = np.polyfit(rs, ys, 1)
        pred = ay * rs + by
        r2 = 1 - ((ys - pred) ** 2).sum() / ((ys - ys.mean()) ** 2).sum()
        ax = np.polyfit(ns, xs, 1)[0]
        st = math.sqrt(d - 1) + math.sqrt(q - 1)
        Cy = math.exp(by)
        print(f"{f'({d},{q})':>9}{len(data):>5}{ay:>14.4f}{r2:>8.4f}{Cy:>10.4f}"
              f"{ax:>14.4f}{st:>8.4f}{Cy/st:>11.4f}")
        exps.append(ay); rows.append((d, q, Cy, st, g))
    if not exps:
        print("  not enough points to fit.")
        return 0
    mu = float(np.mean(exps))
    print(f"\n  mean exponent in r: {mu:.4f}   (-2/3 = {-2/3:.4f})")
    near = min([(-1 / 2, '-1/2'), (-2 / 3, '-2/3'), (-1.0, '-1')], key=lambda t: abs(mu - t[0]))[1]
    print(f"  P5 {'HOLDS' if near == '-2/3' else 'FAILS'}: nearest exponent is {near}, "
          f"over {len(exps)} families including d = {sorted({t[0] for t in rows})}")
    if len(rows) >= 3:
        cs = np.array([t[2] for t in rows]); sts = np.array([t[3] for t in rows])
        ratio = cs / sts
        spread = ratio.std() / ratio.mean()
        a = np.polyfit(np.log(sts), np.log(cs), 1)[0]
        print(f"\n  C_y / (s+t): mean {ratio.mean():.4f}, relative spread {spread:.3f}")
        print(f"  log C_y against log(s+t): slope {a:.4f}")
        if spread < 0.05 and abs(a - 1) < 0.15:
            print("  P6 HOLDS: the constant is proportional to the band half-width.")
        else:
            print(f"  P6 FAILS: C_y is NOT proportional to s+t. Spread {spread:.3f} and the "
                  f"fitted power is {a:.3f}, not 1.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
