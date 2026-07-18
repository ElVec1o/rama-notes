#!/usr/bin/env python3
"""Paper 4: EXACT count of triples (s1,s2,s3) in S_r^3 whose K4 r-lift is
Ramanujan (all new eigenvalues in [-2*sqrt(2), 2*sqrt(2)]).

Method, fully exact:
  per (conjugacy-reduced) triple:
    psi(x)   = char(lift)/chi_K4          (integer poly, new eigenvalues)
    q(x)     = psi(x)*psi(-x)             (even poly)
    P(u)     = q with u = x^2             (roots = squares of psi's roots)
    Ramanujan <=> P has NO root in (8, oo)  [u = 8 <-> |x| = 2*sqrt(2)]
  decided by a Sturm chain of the squarefree part of P, evaluated at 8/+oo.
Cross-checked against float eigenvalues for r = 2, 3.
"""
import sys, os, time, math, itertools
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paper4_exact_k4_lifts import (lift_matrix, det_bareiss, interp_exact,
                                   poly_divide, class_reps_and_data, orbit_reps)

# ---------- Fraction-polynomial utilities (ascending coefficients) ----------
def ptrim(p):
    while p and p[-1] == 0:
        p.pop()
    return p

def pderiv(p):
    return [p[i] * i for i in range(1, len(p))]

def prem(a, b):
    """Remainder of a mod b (b nonzero)."""
    a = a[:]
    db, lb = len(b) - 1, b[-1]
    while len(a) - 1 >= db and ptrim(a):
        da = len(a) - 1
        c = a[-1] / lb
        for j in range(db + 1):
            a[da - db + j] -= c * b[j]
        a.pop()
        ptrim(a)
    return a

def pgcd(a, b):
    a, b = ptrim(a[:]), ptrim(b[:])
    while b:
        a, b = b, ptrim(prem(a, b))
    if a:
        la = a[-1]
        a = [c / la for c in a]
    return a

def pdiv_exact(a, b):
    q, r = poly_divide([Fraction(c) for c in a], [Fraction(c) for c in b])
    assert all(c == 0 for c in r), "non-exact division"
    return ptrim(q)

def peval(p, x):
    v = Fraction(0)
    for c in reversed(p):
        v = v * x + c
    return v

def sturm_roots_gt(P, a):
    """Number of distinct real roots of P in (a, +oo)."""
    S = ptrim([Fraction(c) for c in P])
    g = pgcd(S, pderiv(S))
    if len(g) > 1:
        S = pdiv_exact(S, g)          # squarefree part
    chain = [S, ptrim(pderiv(S))]
    while len(chain[-1]) > 1:
        nxt = [-c for c in prem(chain[-2], chain[-1])]
        if not ptrim(nxt):
            break
        chain.append(ptrim(nxt))
    def signs_at(x):
        out = []
        for q in chain:
            v = peval(q, x)
            if v != 0:
                out.append(1 if v > 0 else -1)
        return out
    def changes(sgns):
        return sum(1 for u, v in zip(sgns, sgns[1:]) if u != v)
    s_a = changes(signs_at(Fraction(a)))
    s_inf = changes([1 if q[-1] > 0 else -1 for q in chain])
    return s_a - s_inf

CHI = [Fraction(v) for v in (-3, -8, -6, 0, 1)]   # (x-3)(x+1)^3 ascending

def is_ramanujan(r, s1, s2, s3):
    pts = [(x0, det_bareiss(lift_matrix(r, s1, s2, s3, x0)))
           for x0 in range(-2 * r, 2 * r + 1)]
    char = interp_exact(pts)                       # ascending, degree 4r
    psi, rem = poly_divide(char, CHI)
    assert all(c == 0 for c in rem), "chi does not divide char"
    psi = ptrim(psi)
    # q(x) = psi(x) * psi(-x); collect even part -> P(u)
    m = len(psi)
    q = [Fraction(0)] * (2 * m - 1)
    for i, ci in enumerate(psi):
        for j, cj in enumerate(psi):
            q[i + j] += ci * cj * (-1) ** j
    assert all(q[k] == 0 for k in range(1, len(q), 2)), "q not even"
    P = [q[2 * k] for k in range((len(q) + 1) // 2)]
    return sturm_roots_gt(P, 8) == 0

def work(args):
    r, rep1, a, b, w = args
    return (w, is_ramanujan(r, rep1, a, b))

def run(r, pool):
    t0 = time.time()
    classdata_raw, perms = class_reps_and_data(r)
    tasks = []
    for rep, clsize, Z in classdata_raw:
        for (a, b), w in orbit_reps(rep, Z, perms):
            tasks.append((r, rep, a, b, clsize * w))
    total_w = sum(t[4] for t in tasks)
    assert total_w == math.factorial(r) ** 3
    count = 0
    for w, ok in pool.imap_unordered(work, tasks, chunksize=16):
        if ok:
            count += w
    print(f"r={r}: exact Ramanujan-triple count = {count} / {total_w}"
          f"   [{time.time()-t0:.0f}s]", flush=True)
    return count

def float_check(r):
    import numpy as np
    perms = list(itertools.permutations(range(r)))
    cnt = 0
    bound = 2 * math.sqrt(2) + 1e-9
    for s1 in perms:
        for s2 in perms:
            for s3 in perms:
                M0 = lift_matrix(r, s1, s2, s3, 0)
                A = -np.array(M0, dtype=float)
                ev = sorted(np.linalg.eigvalsh(A))
                # remove base spectrum 3, -1,-1,-1
                new = ev[:]
                for t in (3.0, -1.0, -1.0, -1.0):
                    i = min(range(len(new)), key=lambda k: abs(new[k] - t))
                    new.pop(i)
                if all(abs(x) <= bound for x in new):
                    cnt += 1
    return cnt

if __name__ == "__main__":
    with Pool(3) as pool:
        for r in (2, 3, 4, 5):
            c = run(r, pool)
            if r <= 3:
                fc = float_check(r)
                print(f"r={r}: float cross-check = {fc}  "
                      f"({'MATCH' if fc == c else 'DIFFERS'})", flush=True)
    print("DONE")
