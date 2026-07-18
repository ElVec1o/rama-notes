#!/usr/bin/env python3
"""Paper 4: exact expected char poly of K4 6-lifts (Psi_6).

Faster orbit machinery than paper4_exact_k4_lifts.py:
- conjugation index tables per centralizer element
- e-class handled by class-decomposition of the second coordinate
- orbit data pickled once; workers lazy-load
Pipeline validated in-script by recomputing Psi_3 and comparing to the
known exact value before running r=6.
"""
import sys, os, time, itertools, pickle, math
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paper4_exact_k4_lifts import (lift_matrix, det_bareiss, interp_exact,
                                   poly_divide, compose, inverse, cycle_type)

CACHE = {}

def build_orbit_data(r):
    """Return list of (rep1, clsize1, orbits) where orbits = [((a,b),w),...]."""
    perms = list(itertools.permutations(range(r)))
    pidx = {p: i for i, p in enumerate(perms)}
    byct = {}
    for p in perms:
        byct.setdefault(cycle_type(p), []).append(p)
    classes = [(members[0], len(members)) for ct, members in sorted(byct.items())]

    def conj_tables(c):
        """Index tables for conjugation by each z in Z(c)."""
        Z = [g for g in perms if compose(g, c) == compose(c, g)]
        tables = []
        for z in Z:
            zi = inverse(z)
            tables.append([pidx[compose(z, compose(a, zi))] for a in perms])
        return tables

    out = []
    n2 = len(perms) ** 2
    for rep, clsize in classes:
        t0 = time.time()
        if rep == tuple(range(r)):
            # e-class: pairs (a,b) under full S_r conj = (class rep c2, b under Z(c2))
            orbits = []
            for rep2, clsize2 in classes:
                CT = conj_tables(rep2)
                weights = {}
                for ib in range(len(perms)):
                    canon = min(T[ib] for T in CT)
                    weights[canon] = weights.get(canon, 0) + 1
                for canon, w in weights.items():
                    orbits.append(((rep2, perms[canon]), clsize2 * w))
        else:
            CT = conj_tables(rep)
            weights = {}
            for ia in range(len(perms)):
                for ib in range(len(perms)):
                    canon = min((T[ia], T[ib]) for T in CT)
                    weights[canon] = weights.get(canon, 0) + 1
            orbits = [((perms[ia], perms[ib]), w) for (ia, ib), w in weights.items()]
        total_w = sum(w for _, w in orbits)
        assert total_w == n2, f"weight mismatch class {rep}: {total_w} != {n2}"
        out.append((rep, clsize, orbits))
        print(f"  class {cycle_type(rep)}: {len(orbits)} orbit reps "
              f"[{time.time()-t0:.1f}s]", flush=True)
    return out

def worker(args):
    r, x0, ci, path = args
    key = (r, path)
    if key not in CACHE:
        with open(path, "rb") as f:
            CACHE[key] = pickle.load(f)
    rep1, clsize, orbits = CACHE[key][ci]
    sub = 0
    for (a, b), w in orbits:
        sub += w * det_bareiss(lift_matrix(r, rep1, a, b, x0))
    return (x0, clsize * sub)

def run(r, pool, path):
    t0 = time.time()
    data = build_orbit_data(r)
    with open(path, "wb") as f:
        pickle.dump(data, f)
    nreps = sum(len(o) for _, _, o in data)
    print(f"r={r}: {len(data)} classes, {nreps} orbit reps "
          f"[setup {time.time()-t0:.0f}s]", flush=True)

    deg = 4 * r
    pts = list(range(-(deg // 2), deg // 2 + 1))
    tasks = [(r, x0, ci, path) for x0 in pts for ci in range(len(data))]
    sums = {x0: 0 for x0 in pts}
    for x0, part in pool.imap_unordered(worker, tasks, chunksize=1):
        sums[x0] += part
    print(f"r={r}: dets done [{time.time()-t0:.0f}s]", flush=True)

    coeffs = interp_exact([(x, sums[x]) for x in pts])
    fact3 = Fraction(math.factorial(r) ** 3)
    phi = [c / fact3 for c in coeffs]
    assert phi[-1] == 1, f"leading != 1: {phi[-1]}"
    chi = [Fraction(v) for v in (-3, -8, -6, 0, 1)]
    quot, rem = poly_divide(phi, chi)
    assert all(c == 0 for c in rem), f"remainder nonzero: {rem}"
    odd_zero = all(quot[j] == 0 for j in range(len(quot)) if j % 2 == 1)
    print(f"r={r}: Psi (ascending) = {[str(c) for c in quot]}", flush=True)
    print(f"r={r}: ALL ODD COEFFS ZERO: {odd_zero}", flush=True)
    print(f"r={r}: sub-leading = {quot[-3]} (predicted {-6*(r-1)}); "
          f"const = {quot[0]}", flush=True)
    print(f"r={r}: TOTAL {time.time()-t0:.0f}s\n", flush=True)
    return quot

if __name__ == "__main__":
    scratch = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_orbits")
    os.makedirs(scratch, exist_ok=True)
    with Pool(6) as pool:
        # validation: recompute Psi_3 through this pipeline
        q3 = run(3, pool, os.path.join(scratch, "orb3.pkl"))
        assert [str(c) for c in q3] == ['6', '0', '-40', '0', '42', '0', '-12', '0', '1'], \
            f"PIPELINE BUG: Psi_3 = {q3}"
        print("Psi_3 validation vs known exact value: OK\n", flush=True)
        run(6, pool, os.path.join(scratch, "orb6.pkl"))
    print("DONE")
