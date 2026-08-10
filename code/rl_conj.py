"""The bridge between our note's objects and Xu's, verified, and what his conjecture says here.

Zili Xu's note (Aug 2026) proposes Conjecture 1.4: for X_i >= 0 with rank X_i <= k and
sum_i X_i <= I_N, setting eta = max_i tr X_i, if eta <= k-1 then

    maxroot mu[X_1,...,X_m] <= ( sqrt(1 - eta/k) + sqrt((1 - 1/k) eta) )^2,                 (*)

mu being the MSS mixed characteristic polynomial. Conjecture 1.2 implies (*), and Conjecture 1.2
generalizes Ravichandran-Leake Conjecture 1. His Remark 1.6 specializes: for rank-b projections
with sum P_i = a I and b/a <= b-1,

    maxroot mu[P_1,...,P_q] <= ( sqrt(a-1) + sqrt(b-1) )^2,                                 (**)

which at b = 2 is a + 2 sqrt(a-1), the upper edge of the (a,2)-biregular tree band and STRICTLY
STRONGER than the a + 2 sqrt(a) our note takes as its target.

Talking to Xu about this requires knowing exactly where our F_A and his mu are the same object.
The answer is not uniform across our class, and pinning down the boundary is what this script is
for. Section 1 measures, and the result is:

  UNWEIGHTED (coordinate) FAMILIES: the same object, to machine precision. With A_e = P_e the
  edge projections, the M_r come out equal to the matching numbers of the graph and the MSS
  roots reproduce the F_A roots shifted by a, at 1e-13 to 1e-8. So on this subclass our
  polynomial IS the MSS mixed characteristic polynomial, our band question IS Xu's largest-root
  question, and code/adversarial.py is already an adversarial search against (**).

  WEIGHTED FAMILIES: NOT the same object, under either naive scaling. Neither A_k = c_k P_k nor
  A_k = sqrt(c_k) P_k reproduces F_A; the root discrepancies are 1e-1, not 1e-8. The two
  candidates are the only natural ones -- e_2(A_k) = c_k, which the note's
  Adj(A) = sum_k e_2(A_k) P_{range A_k} asks for, forces sqrt(c_k) P_k, while mu being
  multilinear in the A_k forces the wedge form's degree-one dependence on c_k, hence c_k P_k --
  and they disagree with each other and with F_A. So the note's weighted plane class is a
  genuine extension beyond MSS's mixed characteristic polynomial, not a reparameterization of
  it, and Xu's conjectures do not transfer to it for free.

Section 2 unwinds (*) into our normalization and checks the unwinding by reproducing (**)
exactly on unweighted projections, which is the case where the correspondence holds.

A PREDICTION WAS WITHDRAWN HERE. P18 was frozen as "y_max <= 4 c_max (a - c_max) for every
weighted family with c_max <= a/2", read off from the assumption that the MSS inputs were
c_k P_k and that Conjecture 1.4 therefore applied verbatim to our weighted class. Section 1
shows that assumption is false, so the statement was never an instance of Conjecture 1.4 and
could not have refuted it. P18 is withdrawn as MALFORMED, not refuted: it was a prediction
about a correspondence that does not exist. The sharp testable instance is the unweighted
projection case, which code/adversarial.py already searches against
band(a,b) = [(sqrt(a-1)-sqrt(b-1))^2, (sqrt(a-1)+sqrt(b-1))^2].
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import math
import itertools
import numpy as np
import networkx as nx
from scipy.optimize import nnls

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mixed_char_poly import mixed_char_poly

rng = np.random.default_rng(20260823)


def wedge_M(frames, c, m):
    """M_r = sum_{|T|=r} (prod c_k) det Gram(T): the note's wedge route."""
    M = [1.0] + [0.0] * (m // 2)
    for r in range(1, m // 2 + 1):
        if r > len(frames):
            break
        tot = 0.0
        for T in itertools.combinations(range(len(frames)), r):
            C = np.hstack([frames[k] for k in T])
            d = float(np.linalg.det(C.T @ C))
            if d > 0.0:
                tot += float(np.prod([c[k] for k in T])) * d
        M[r] = tot
    return M


def FA_roots(frames, c, m):
    M = wedge_M(frames, c, m)
    coef = [0.0] * (m + 1)
    for r in range(m // 2 + 1):
        coef[2 * r] = ((-1) ** r) * M[r]      # coefficient of x^{m-2r}
    return np.sort(np.roots(coef).real), M


def mss_roots(frames, c, a, scaling='sqrt'):
    """Roots of the MSS mixed characteristic polynomial, shifted: mu(y) -> y - a.

    Two candidate inputs. `sqrt` uses sqrt(c_k) P_k, which makes e_2(A_k) = c_k as the note's
    Adj(A) = sum_k e_2(A_k) P_k requires. `lin` uses c_k P_k, which is what the wedge form's
    degree-one dependence on each c_k would require, mu being multilinear in the A_k.
    """
    f = math.sqrt if scaling == 'sqrt' else (lambda t: t)
    As = [f(ci) * (B @ B.T) for ci, B in zip(c, frames)]
    return np.sort(np.roots(mixed_char_poly(As)).real) - a


def coordinate_family(m, a, seed):
    G = nx.random_regular_graph(a, m, seed=seed)
    frames = []
    for (u, v) in G.edges():
        B = np.zeros((m, 2)); B[u, 0] = 1.0; B[v, 1] = 1.0
        frames.append(B)
    return G, frames, np.ones(len(frames))


def matching_numbers(G, m):
    E = list(G.edges())
    mk = [1] + [0] * (m // 2)
    for r in range(1, m // 2 + 1):
        cnt = 0
        for T in itertools.combinations(range(len(E)), r):
            vs = set(); ok = True
            for k in T:
                u, v = E[k]
                if u in vs or v in vs:
                    ok = False; break
                vs.add(u); vs.add(v)
            if ok:
                cnt += 1
        mk[r] = cnt
    return mk


def weighted_tight(m, q, a):
    frames = [np.linalg.qr(rng.standard_normal((m, 2)))[0] for _ in range(q)]
    iu = np.triu_indices(m)
    w = np.array([1.0 if i == j else math.sqrt(2.0) for i, j in zip(*iu)])
    A = np.stack([(B @ B.T)[iu] for B in frames], axis=1)
    c, _ = nnls(A * w[:, None], (a * np.eye(m))[iu] * w)
    keep = [k for k in range(len(c)) if c[k] > 1e-10]
    frames = [frames[k] for k in keep]; c = c[keep]
    S = sum(ci * (B @ B.T) for ci, B in zip(c, frames))
    if float(np.abs(S - a * np.eye(m)).max()) > 1e-9:
        return None
    return frames, c


def xu_bound(frames, c, k=2):
    """Conjecture 1.4 unwound to our normalization; None if its hypothesis fails."""
    S = sum(math.sqrt(ci) * (B @ B.T) for ci, B in zip(c, frames))
    sigma = float(np.linalg.eigvalsh(S).max())
    eta = 2.0 * float(np.max(np.sqrt(c))) / sigma
    if eta > k - 1:
        return None, eta, sigma
    v = (math.sqrt(1.0 - eta / k) + math.sqrt((1.0 - 1.0 / k) * eta)) ** 2
    return sigma * v, eta, sigma


def main():
    print("SECTION 1. The correspondence F_A(x) = mu(x+a) with MSS inputs sqrt(c_k) P_k.\n")
    print("Coordinate families: M_r must be the matching numbers, and mu(y)-a the F_A roots.")
    print(f"{'m':>4}{'a':>4}{'M_r = m(G,r)':>14}{'max|mu-a - F_A|':>18}{'max|x|':>9}"
          f"{'2sqrt(a-1)':>12}{'ratio':>8}")
    okall = True
    for (m, a) in ((6, 3), (8, 3), (10, 3), (6, 4), (8, 4)):
        G, frames, c = coordinate_family(m, a, seed=7 + m)
        xr, M = FA_roots(frames, c, m)
        mk = matching_numbers(G, m)
        same = all(abs(M[r] - mk[r]) < 1e-9 for r in range(m // 2 + 1))
        d = float(np.max(np.abs(mss_roots(frames, c, a) - xr)))
        edge = 2.0 * math.sqrt(a - 1.0)
        xmax = float(np.max(np.abs(xr)))
        okall = okall and same and d < 1e-6   # degree-m root finding, not exact arithmetic
        print(f"{m:>4}{a:>4}{str(same):>14}{d:>18.2e}{xmax:>9.4f}{edge:>12.4f}"
              f"{xmax/edge:>8.4f}")

    print("\nWeighted tight families: wedge route vs direct MSS subset formula.")
    print("(The subset formula is 2^q, so this runs where the NNLS support stays small.)")
    print(f"{'m':>4}{'a':>4}{'|supp|':>8}{'sqrt(c)P: err':>15}{'cP: err':>12}{'match':>8}")
    ntested = 0
    wok = True
    for (m, a) in ((4, 3.0), (4, 4.0), (4, 5.0), (6, 3.0), (6, 4.0)):
        got = None
        for _ in range(60):
            fam = weighted_tight(m, 4 * m * (m + 1) // 2, a)
            if fam is not None and len(fam[0]) <= 18:
                got = fam
                break
        if got is None:
            print(f"{m:>4}{int(a):>4}   no tight family with support <= 18"); continue
        frames, c = got
        xr, _ = FA_roots(frames, c, m)
        d1 = float(np.max(np.abs(mss_roots(frames, c, a, 'sqrt') - xr)))
        d2 = float(np.max(np.abs(mss_roots(frames, c, a, 'lin') - xr)))
        hit = 'sqrt' if d1 < 1e-8 else ('lin' if d2 < 1e-8 else 'NEITHER')
        wok = wok and hit != 'NEITHER'
        ntested += 1
        print(f"{m:>4}{int(a):>4}{len(frames):>8}{d1:>15.2e}{d2:>12.2e}{hit:>8}")
    print(f"\n  coordinate correspondence verified: {okall}")
    print(f"  weighted correspondence via either naive scaling: {wok}")
    okall = okall and ntested >= 2
    print(f"\n  correspondence verified: {okall}")
    if not okall:
        return 1

    print("\nSECTION 2. Conjecture 1.4 unwound, and why weights do not sharpen it.\n")
    print("Correctness check: on unweighted rank-b projections the unwinding must reproduce")
    print("Remark 1.6, maxroot mu <= (sqrt(a-1)+sqrt(b-1))^2.")
    print(f"{'m':>4}{'a':>4}{'unwound':>12}{'Remark 1.6':>13}{'diff':>10}")
    for (m, a) in ((6, 3), (8, 3), (6, 4), (8, 4)):
        _, frames, c = coordinate_family(m, a, seed=11 + m)
        bnd, eta, sigma = xu_bound(frames, c)
        r16 = (math.sqrt(a - 1.0) + 1.0) ** 2
        print(f"{m:>4}{a:>4}{bnd:>12.6f}{r16:>13.6f}{abs(bnd - r16):>10.1e}")

    print("\nWeighted families: the bound relative to the unweighted one at the same a.")
    print(f"{'m':>4}{'a':>4}{'|supp|':>8}{'c_max':>9}{'eta':>8}{'bound':>10}"
          f"{'a+2sqrt(a-1)':>14}{'weaker?':>9}")
    for (m, a) in ((6, 3.0), (8, 3.0), (6, 4.0), (8, 4.0)):
        fam = weighted_tight(m, 3 * m * (m + 1) // 2, a)
        if fam is None:
            continue
        frames, c = fam
        bnd, eta, sigma = xu_bound(frames, c)
        r16 = a + 2.0 * math.sqrt(a - 1.0)
        if bnd is None:
            print(f"{m:>4}{int(a):>4}{len(frames):>8}{float(np.max(c)):>9.4f}{eta:>8.4f}"
                  f"{'hypothesis fails':>24}")
            continue
        print(f"{m:>4}{int(a):>4}{len(frames):>8}{float(np.max(c)):>9.4f}{eta:>8.4f}"
              f"{bnd:>10.4f}{r16:>14.4f}{str(bnd > r16):>9}")

    print("\n  If the weighted bound is uniformly weaker, weights cannot break the conjecture")
    print("  and the sharp instance is the unweighted projection case, which is what")
    print("  code/adversarial.py searches against band(a,b) = [(s-t)^2,(s+t)^2].")
    return 0


if __name__ == '__main__':
    sys.exit(main())
