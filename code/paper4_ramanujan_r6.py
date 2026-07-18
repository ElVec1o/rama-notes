#!/usr/bin/env python3
"""Exact Ramanujan-lift count for r = 6 (K4), reusing the orb6.pkl orbit data
and the Sturm machinery of paper4_ramanujan_exact.py."""
import sys, os, time, math, pickle
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paper4_exact_k4_lifts import lift_matrix, det_bareiss, interp_exact, poly_divide
from paper4_ramanujan_exact import ptrim, sturm_roots_gt, CHI

R = 6
ORB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_orbits", "orb6.pkl")
DATA = None

def is_ram(rep1, a, b):
    pts = [(x0, det_bareiss(lift_matrix(R, rep1, a, b, x0)))
           for x0 in range(-2 * R, 2 * R + 1)]
    char = interp_exact(pts)
    psi, rem = poly_divide(char, CHI)
    assert all(c == 0 for c in rem)
    psi = ptrim(psi)
    m = len(psi)
    q = [Fraction(0)] * (2 * m - 1)
    for i, ci in enumerate(psi):
        for j, cj in enumerate(psi):
            q[i + j] += ci * cj * (-1) ** j
    P = [q[2 * k] for k in range((len(q) + 1) // 2)]
    return sturm_roots_gt(P, 8) == 0

def worker(ci_chunk):
    global DATA
    if DATA is None:
        with open(ORB, "rb") as f:
            DATA = pickle.load(f)
    ci, lo, hi = ci_chunk
    rep1, clsize, orbits = DATA[ci]
    cnt = 0
    for (a, b), w in orbits[lo:hi]:
        if is_ram(rep1, a, b):
            cnt += w
    return clsize * cnt

if __name__ == "__main__":
    t0 = time.time()
    with open(ORB, "rb") as f:
        data = pickle.load(f)
    # chunk each class's orbit list into ~2000-orbit slices
    tasks = []
    for ci, (rep1, clsize, orbits) in enumerate(data):
        for lo in range(0, len(orbits), 2000):
            tasks.append((ci, lo, min(lo + 2000, len(orbits))))
    print(f"{len(tasks)} chunks over {sum(len(o) for _,_,o in data)} orbit reps",
          flush=True)
    total = 0
    done = 0
    with Pool(8) as pool:
        for c in pool.imap_unordered(worker, tasks):
            total += c
            done += 1
            if done % 25 == 0:
                print(f"  {done}/{len(tasks)} chunks, t={time.time()-t0:.0f}s",
                      flush=True)
    print(f"\nr=6: exact Ramanujan-triple count = {total} / {math.factorial(6)**3}"
          f"  (fraction {total/math.factorial(6)**3:.4f})  [{time.time()-t0:.0f}s]",
          flush=True)
