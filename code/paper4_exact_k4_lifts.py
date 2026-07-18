#!/usr/bin/env python3
"""Paper 4 enhancement: EXACT expected char poly of K4 r-lifts, r = 2,3,4,5.

Method: integer Bareiss determinants at 4r+1 integer points + exact Lagrange
interpolation (Fractions). Reductions: sigma1 -> conjugacy class reps (diagonal
conjugation invariance), then (sigma2,sigma3) -> orbit reps under centralizer
Z(sigma1). Cross-checked against full brute force for r=2,3.
"""
import sys, time, itertools
from fractions import Fraction
from multiprocessing import Pool

# ---------- permutation helpers (tuples) ----------
def compose(a, b):  # (a∘b)(i) = a[b[i]]
    return tuple(a[b[i]] for i in range(len(a)))

def inverse(a):
    inv = [0] * len(a)
    for i, v in enumerate(a):
        inv[v] = i
    return tuple(inv)

def conj(g, a):  # g a g^-1
    gi = inverse(g)
    return compose(g, compose(a, gi))

def cycle_type(a):
    n = len(a); seen = [False]*n; ct = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = a[j]; l += 1
            ct.append(l)
    return tuple(sorted(ct, reverse=True))

# ---------- lift adjacency & integer determinant ----------
def lift_matrix(r, s1, s2, s3, x0):
    """Return integer matrix x0*I - A(lift) as list of lists."""
    n = 4 * r
    M = [[0]*n for _ in range(n)]
    for i in range(n):
        M[i][i] = x0
    def add_edge(u, v, sigma):
        for c in range(r):
            d = sigma[c]
            M[u*r+c][v*r+d] -= 1
            M[v*r+d][u*r+c] -= 1
    ident = tuple(range(r))
    add_edge(0, 1, ident); add_edge(0, 2, ident); add_edge(0, 3, ident)
    add_edge(1, 2, s1); add_edge(1, 3, s2); add_edge(2, 3, s3)
    return M

def det_bareiss(M):
    n = len(M); sign = 1; prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            piv = next((i for i in range(k+1, n) if M[i][k] != 0), None)
            if piv is None:
                return 0
            M[k], M[piv] = M[piv], M[k]; sign = -sign
        akk = M[k][k]; rowk = M[k]
        for i in range(k+1, n):
            rowi = M[i]; aik = rowi[k]
            for j in range(k+1, n):
                rowi[j] = (rowi[j]*akk - aik*rowk[j]) // prev
        prev = akk
    return sign * M[n-1][n-1]

# ---------- orbit reduction ----------
def class_reps_and_data(r):
    """Conjugacy classes of S_r: (rep, class_size); and centralizers."""
    perms = list(itertools.permutations(range(r)))
    byct = {}
    for p in perms:
        byct.setdefault(cycle_type(p), []).append(p)
    out = []
    for ct, members in sorted(byct.items()):
        rep = members[0]
        Z = [g for g in perms if compose(g, rep) == compose(rep, g)]
        out.append((rep, len(members), Z))
    return out, perms

def orbit_reps(rep, Z, perms):
    """Orbit representatives + multiplicities of Z acting diagonally on pairs."""
    weights = {}
    Zi = [(g, inverse(g)) for g in Z]
    for a in perms:
        for b in perms:
            best = None
            for g, gi in Zi:
                ca = compose(g, compose(a, gi)); cb = compose(g, compose(b, gi))
                key = (ca, cb)
                if best is None or key < best:
                    best = key
            weights[best] = weights.get(best, 0) + 1
    return list(weights.items())

# ---------- evaluation ----------
def sum_at_point(args):
    """Weighted sum over reduced triples of det(x0 I - A)."""
    r, x0, classdata = args
    total = 0
    for rep1, clsize, orbits in classdata:
        sub = 0
        for (a, b), w in orbits:
            M = lift_matrix(r, rep1, a, b, x0)
            sub += w * det_bareiss(M)
        total += clsize * sub
    return (x0, total)

def brute_sum_at_point(r, x0, perms):
    total = 0
    for s1 in perms:
        for s2 in perms:
            for s3 in perms:
                total += det_bareiss(lift_matrix(r, s1, s2, s3, x0))
    return total

def interp_exact(points):
    """Clean Newton-form exact interpolation. Returns ascending coeff list."""
    xs = [Fraction(x) for x, _ in points]
    ys = [Fraction(y) for _, y in points]
    n = len(xs)
    # divided differences
    dd = ys[:]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            dd[i] = (dd[i] - dd[i - 1]) / (xs[i] - xs[i - j])
    # build polynomial: sum dd[k] * prod_{i<k}(x - xs[i])
    coeffs = [Fraction(0)] * n
    basis = [Fraction(1)]  # current product polynomial (ascending)
    for k in range(n):
        for idx, c in enumerate(basis):
            coeffs[idx] += dd[k] * c
        # basis *= (x - xs[k])
        nb = [Fraction(0)] * (len(basis) + 1)
        for idx, c in enumerate(basis):
            nb[idx + 1] += c
            nb[idx] -= xs[k] * c
        basis = nb
    return coeffs

def poly_divide(num, den):
    """Exact division of ascending-coeff Fraction polys; returns (quot, rem)."""
    num = num[:]
    dn = len(den) - 1
    while len(den) > 1 and den[-1] == 0:
        den = den[:-1]; dn -= 1
    q = [Fraction(0)] * (len(num) - dn)
    for k in range(len(num) - dn - 1 + 1)[::-1]:
        c = num[k + dn] / den[dn]
        q[k] = c
        for j in range(dn + 1):
            num[k + j] -= c * den[j]
    return q, num[:dn]

def run_r(r, pool):
    t0 = time.time()
    classdata_raw, perms = class_reps_and_data(r)
    classdata = []
    for rep, clsize, Z in classdata_raw:
        orbs = orbit_reps(rep, Z, perms)
        classdata.append((rep, clsize, orbs))
    nreps = sum(len(o) for _, _, o in classdata)
    print(f"r={r}: classes={len(classdata)}, orbit reps total={nreps} "
          f"(vs full {len(perms)**3})  [setup {time.time()-t0:.1f}s]", flush=True)

    deg = 4 * r
    pts = list(range(-(deg // 2), deg // 2 + 1))
    assert len(pts) == deg + 1

    tasks = [(r, x0, classdata) for x0 in pts]
    results = dict(pool.map(sum_at_point, tasks))

    # cross-check vs brute force for small r
    if r <= 3:
        for x0 in (0, 2):
            bs = brute_sum_at_point(r, x0, perms)
            assert bs == results[x0], f"REDUCTION BUG r={r} x0={x0}: {bs} vs {results[x0]}"
        print(f"r={r}: reduction cross-check vs full brute force OK", flush=True)

    coeffs = interp_exact([(x, results[x]) for x in pts])  # ascending, sum poly
    fact3 = Fraction(1)
    import math
    fact3 = Fraction(math.factorial(r) ** 3)
    phi = [c / fact3 for c in coeffs]   # expected char poly, ascending
    assert phi[-1] == 1, f"leading coeff != 1: {phi[-1]}"
    # divide by chi_K4 = (x-3)(x+1)^3 = x^4 - 6x^2 - 8x - 3  (ascending: [-3,-8,-6,0,1])
    chi = [Fraction(v) for v in (-3, -8, -6, 0, 1)]
    quot, rem = poly_divide(phi, chi)
    remnz = [c for c in rem if c != 0]
    print(f"r={r}: division by chi_K4 remainder zero: {not remnz}", flush=True)
    # integrality
    ints = all(c.denominator == 1 for c in quot)
    odd_coeffs = {j: quot[j] for j in range(len(quot)) if j % 2 == 1}
    odd_zero = all(v == 0 for v in odd_coeffs.values())
    print(f"r={r}: Psi_r integer coefficients: {ints}", flush=True)
    print(f"r={r}: Psi_r (ascending) = {[str(c) for c in quot]}", flush=True)
    print(f"r={r}: ALL ODD-DEGREE COEFFS ZERO: {odd_zero}", flush=True)
    sub = quot[-3] if len(quot) >= 3 else None
    print(f"r={r}: sub-leading coeff (x^{deg-6}... x^(deg-4-2)) = {sub}  "
          f"(claimed -6(r-1) = {-6*(r-1)})", flush=True)
    print(f"r={r}: TOTAL TIME {time.time()-t0:.1f}s\n", flush=True)
    return quot

if __name__ == "__main__":
    with Pool(8) as pool:
        for r in (2, 3, 4, 5):
            run_r(r, pool)
    print("ALL DONE")
