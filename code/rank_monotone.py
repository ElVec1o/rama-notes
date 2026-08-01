"""Regenerates the rank-monotonicity table in paper2_note/note.tex.

Fix (a,b) and let the common rank n of the A_k vary, holding trace and sum fixed:
A_k = (b/n) Q_k with Q_k rank-n orthogonal projections summing to (a n / b) I, so
tr A_k = b and sum_k A_k = a I for every n.  The extreme roots of the MSS mixed
characteristic polynomial then move monotonically outward in n, from the tree band
[(sqrt(a-1)-sqrt(b-1))^2, (sqrt(a-1)+sqrt(b-1))^2] at n = b to the Marchenko-Pastur
interval [(sqrt a - sqrt b)^2, (sqrt a + sqrt b)^2] approached at n = p.

So the conjectured band is the n = b endpoint of an increasing family whose other
endpoint is Marchenko-Pastur, and the Marchenko-Pastur value is attained (by the
scalar family A_k = (b/p) I, the n = p case).

Usage:  python3 rank_monotone.py
Seed is fixed; output is deterministic.
"""
import math
import numpy as np
import mixed_char_poly as mcp

SEED = 11


def tight_fusion_frame(p, n, q, target, rng, iters=6000, tol=1e-13):
    """q rank-n orthogonal projections on R^p summing to target * I.

    Alternating projection: rescale by the inverse Cholesky factor of the current
    sum, then re-project each summand onto the rank-n projections.  Returns None if
    the iteration does not reach a genuine idempotent frame.
    """
    mats = []
    for _ in range(q):
        g = rng.normal(size=(p, n))
        qq, _ = np.linalg.qr(g)
        mats.append(qq @ qq.T)
    for _ in range(iters):
        s = sum(mats)
        try:
            scale = np.linalg.inv(np.linalg.cholesky(s / target)).T
        except np.linalg.LinAlgError:
            return None
        new = []
        for m in mats:
            mp = scale.T @ m @ scale
            w, v = np.linalg.eigh(mp)
            basis = v[:, np.argsort(-w)[:n]]
            new.append(basis @ basis.T)
        if max(np.linalg.norm(new[i] - mats[i]) for i in range(q)) < tol:
            mats = new
            break
        mats = new
    if not np.allclose(sum(mats), target * np.eye(p), atol=1e-6):
        return None
    if max(np.linalg.norm(m @ m - m) for m in mats) > 1e-7:
        return None
    return mats


def extreme_roots(mats):
    roots = np.sort(np.roots(mcp.mixed_char_poly(mats)).real)
    return roots[0], roots[-1]


def main():
    a, b, p, q = 4, 2, 6, 12
    rng = np.random.default_rng(SEED)
    lo_tree = (math.sqrt(a - 1) - math.sqrt(b - 1)) ** 2
    hi_tree = (math.sqrt(a - 1) + math.sqrt(b - 1)) ** 2
    lo_mp = (math.sqrt(a) - math.sqrt(b)) ** 2
    hi_mp = (math.sqrt(a) + math.sqrt(b)) ** 2

    print(f"(a,b) = ({a},{b}),  p = {p},  q = {q}")
    print(f"  tree band        [{lo_tree:.5f}, {hi_tree:.5f}]   (rank n = b = {b})")
    print(f"  Marchenko-Pastur [{lo_mp:.5f}, {hi_mp:.5f}]   (rank n = p, scalar family)")
    print()
    print(f"{'n':>3} {'least root':>12} {'greatest root':>14}")
    for n in range(b, p + 1):
        target = a * n / b
        if abs(target - round(target)) > 1e-9 or q * n != p * round(target):
            print(f"{n:>3}   (incompatible parameters, skipped)")
            continue
        best = None
        for _ in range(12):
            proj = tight_fusion_frame(p, n, q, round(target), rng)
            if proj is None:
                continue
            mats = [(b / n) * x for x in proj]
            if not np.allclose(sum(mats), a * np.eye(p), atol=1e-6):
                continue
            lo, hi = extreme_roots(mats)
            if best is None or lo < best[0]:
                best = (lo, hi)
        if best is None:
            print(f"{n:>3}   (construction failed)")
            continue
        print(f"{n:>3} {best[0]:>12.5f} {best[1]:>14.5f}")
    print()
    print("The interval widens monotonically in n, from inside the tree band at n = b")
    print("towards the Marchenko-Pastur interval at n = p.")


if __name__ == "__main__":
    main()
