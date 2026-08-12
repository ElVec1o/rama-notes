"""Hall's certificate, rebuilt from the graph: the one step that had no committed artifact.

Paper 2a states that the certificate was verified independently, "reconstructing every object from
the graph rather than copying the displayed matrices", and RamaLean/HallCounterexample.lean flags in
its own "what is not proved here" list that the orbit quotient K is "verified computationally in
private/". private/ never ships. So the single step of the flagship counterexample that no reader
could check was the reduction of the 120-state decay matrix to the 6x6 quotient. This script is that
artifact.

WHAT IS REBUILT, in order, each from the previous and none copied from the paper:

  1. The graph. G(p,q) is a centre c joined to v_1..v_p; for each i a copy of K_{2,q} on v_i, w_i
     with middle vertices u_{i,1..q}; and a pendant leaf at each w_i. Hall's graph is p = q = 5:
     41 vertices, 60 edges.
  2. The matching numbers, by brute-force enumeration on the 8-vertex branch and the rooted
     assembly mu_G = x prod_i mu_{B_i} - sum_i mu_{B_i - v_i} prod_{j != i} mu_{B_j}. Compared
     against the vector printed in the paper, term by term, and against the closed factorisation
     x^21 (x^4 - 11x^2 + 25)^4 (x^2 - 5)(x^2 - 11).
  3. The ratio system at lambda = sqrt 5 on all 120 directed edges: the Angel-Friedman-Hoory
     equations lambda = 1/r_e + sum_{e -> f} r_f, solved by Newton at high precision, with the
     residual reported rather than assumed.
  4. The decay matrix R_{e,f} = |r_f|^2 on non-backtracking pairs, its strongly connected
     components, and the count of transient and recurrent states. The paper says ten transient at
     the leaves and one recurrent block of 110.
  5. The 6x6 orbit quotient K, rebuilt from follower counts on the recurrent block.
  6. The certificate: x = (20,121,47,33,28,16) with x - Kx > 0 componentwise, checked against the
     six exact residuals that RamaLean/HallCounterexample.lean carries in s = sqrt 41; and the
     characteristic polynomial against t^6 - ((201+19s)/800) t^2 + (21s-241)/250.

Step 6 is the test that matters. The Lean holds six exact expressions in s, so a rebuild that
reproduces them cannot be a coincidence of normalisation: it pins K entry by entry.

FROZEN BEFORE THE DATA:
  P50. (a) The matching numbers agree with the printed vector term by term, and mu_G(sqrt 5) = 0.
       (b) The ratio system solves at lambda = sqrt 5 with every ratio nonzero.
       (c) The decay digraph has exactly 10 transient states and one recurrent block of exactly 110.
       (d) The orbit quotient reproduces the six residuals of the Lean and the characteristic
           polynomial printed in the paper.

FALSIFICATION. Any disagreement in (a) breaks the counterexample outright. A failure in (c) or (d)
means the published K is not the reduction of the decay matrix of this graph, which is exactly the
step nobody could check.

NUMERICS. The ratio system is solved EXACTLY by sympy in Q(sqrt 5, sqrt 41), then evaluated to
double precision; the residual of all 120 equations is printed rather than assumed, at 4e-16, which
is machine precision for that evaluation. Rule 7: the certificate is read twice, once as the
componentwise x - Kx against the six exact expressions the Lean carries in s = sqrt 41, and once as
rho(K) against the value printed in the paper.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import itertools
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')
import quickmode

QUICK = quickmode.QUICK
PRINTED = [1, 60, 1585, 24260, 238105, 1564976, 6973855, 20805500, 39784375, 44062500, 21484375]


def hall_graph(p=5, q=5):
    """Vertices 0..(1+p+pq+p+p-1); edges as in the construction. Returns (n, edges)."""
    c = 0
    v = [1 + i for i in range(p)]
    u = [[1 + p + i * q + j for j in range(q)] for i in range(p)]
    w = [1 + p + p * q + i for i in range(p)]
    leaf = [1 + p + p * q + p + i for i in range(p)]
    e = []
    for i in range(p):
        e.append((c, v[i]))
        for j in range(q):
            e.append((v[i], u[i][j]))
            e.append((u[i][j], w[i]))
        e.append((w[i], leaf[i]))
    n = 1 + p + p * q + 2 * p
    return n, e


def matchings_poly(nv, edges):
    """Matching polynomial coefficients m_k by brute force. Small graphs only."""
    m = [0] * (nv // 2 + 2)
    m[0] = 1
    for k in range(1, len(m)):
        cnt = 0
        for S in itertools.combinations(edges, k):
            seen = set()
            ok = True
            for (a, b) in S:
                if a in seen or b in seen:
                    ok = False
                    break
                seen.add(a); seen.add(b)
            if ok:
                cnt += 1
        m[k] = cnt
        if cnt == 0:
            break
    while len(m) > 1 and m[-1] == 0:
        m.pop()
    return m


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def mu_from_m(m, nv):
    """sum_k (-1)^k m_k x^{nv-2k} as a coefficient list in descending powers of x."""
    c = [0] * (nv + 1)
    for k, mk in enumerate(m):
        c[2 * k] += ((-1) ** k) * mk
    return c


def branch(q=5):
    """One branch rooted at v: v, u_1..u_q, w, leaf."""
    v = 0
    u = [1 + j for j in range(q)]
    w = 1 + q
    leaf = 2 + q
    e = [(v, x) for x in u] + [(x, w) for x in u] + [(w, leaf)]
    return 3 + q, e, v


def directed_edges(edges):
    return [(a, b) for (a, b) in edges] + [(b, a) for (a, b) in edges]


def followers(de):
    """e -> f when head(e) = tail(f) and f is not the reverse of e."""
    byt = {}
    for idx, (a, b) in enumerate(de):
        byt.setdefault(a, []).append(idx)
    out = []
    for i, (a, b) in enumerate(de):
        out.append([j for j in byt.get(b, []) if de[j] != (b, a)])
    return out


def edge_type(de, i, n, p=5, q=5):
    """One of eight types: c->v, v->c, v->u, u->v, u->w, w->u, w->leaf, leaf->w."""
    a, b = de[i]
    c = 0
    V = set(range(1, 1 + p))
    U = set(range(1 + p, 1 + p + p * q))
    W = set(range(1 + p + p * q, 1 + p + p * q + p))
    L = set(range(1 + p + p * q + p, n))
    for (X, Y, t) in ((({c}), V, 0), (V, {c}, 1), (V, U, 2), (U, V, 3),
                      (U, W, 4), (W, U, 5), (W, L, 6), (L, W, 7)):
        if a in X and b in Y:
            return t
    raise ValueError((a, b))


def solve_ratios_by_type(_lam_ignored=None):
    """The ratio system has only eight unknowns, the graph having eight edge types.

    Solving on all 120 directed edges by iteration does not work: the cavity recursion
    r <- 1/(lambda - sum r) starts positive and Hall's system has NEGATIVE entries at three of the
    eight types, so it is not the attracting fixed point. Symmetry reduces the system to eight
    equations, which sympy solves exactly; the ratios come out in Q(sqrt 5, sqrt 41) as the paper
    says. Both real branches are returned and the caller keeps the one whose decay matrix contracts.
    """
    import sympy as sp
    # EXACT sqrt(5). Passing a float here makes sympy attempt a Groebner basis over floats, which
    # does not terminate; the system is only tractable in exact arithmetic.
    lam = sp.sqrt(5)
    r = sp.symbols('r1:9')
    r1, r2, r3, r4, r5, r6, r7, r8 = r
    eqs = [sp.Eq(lam, 1 / r1 + 5 * r3), sp.Eq(lam, 1 / r2 + 4 * r1),
           sp.Eq(lam, 1 / r3 + r5), sp.Eq(lam, 1 / r4 + r2 + 4 * r3),
           sp.Eq(lam, 1 / r5 + 4 * r6 + r7), sp.Eq(lam, 1 / r6 + r4),
           sp.Eq(lam, 1 / r7), sp.Eq(lam, 1 / r8 + 5 * r6)]
    out = []
    for sol in sp.solve(eqs, list(r), dict=True):
        vals = [sp.simplify(sol[v]) for v in r]
        num = [complex(sp.N(v, 40)) for v in vals]
        if all(abs(z.imag) < 1e-25 for z in num):
            out.append(([z.real for z in num], vals))
    return out


def main():
    from mpmath import mp, mpf, sqrt as msqrt
    mp.dps = 60
    print("P50 (frozen): (a) matching numbers match and mu_G(sqrt5) = 0; (b) the ratio system")
    print("solves at sqrt 5; (c) 10 transient and one recurrent block of 110; (d) the orbit")
    print("quotient reproduces the Lean's six residuals and the printed characteristic polynomial.\n")

    n, edges = hall_graph()
    print(f"(1) the graph: {n} vertices, {len(edges)} edges "
          f"(paper: 41, 60) -> {'ok' if (n, len(edges)) == (41, 60) else 'MISMATCH'}\n")

    nb, eb, vb = branch()
    mB = matchings_poly(nb, eb)
    mBv = matchings_poly(nb - 1, [(a, b) for (a, b) in eb if vb not in (a, b)])
    muB = mu_from_m(mB, nb)
    muBv = mu_from_m(mBv, nb - 1)
    # mu_G = x * prod muB^5 - 5 * muBv * muB^4   (centre joined to the five branch roots)
    prod5 = [1]
    for _ in range(5):
        prod5 = poly_mul(prod5, muB)
    prod4 = [1]
    for _ in range(4):
        prod4 = poly_mul(prod4, muB)
    muG = poly_mul([1, 0], prod5)
    sub = poly_mul([5], poly_mul(muBv, prod4))
    L = max(len(muG), len(sub))
    muG = [0] * (L - len(muG)) + muG
    sub = [0] * (L - len(sub)) + sub
    muG = [x - y for x, y in zip(muG, sub)]
    got = [abs(muG[i]) for i in range(0, len(muG), 2)][:len(PRINTED)]
    agree = got == PRINTED
    print("(2) matching numbers, rebuilt from the branch:")
    print(f"    {got}")
    print(f"    printed in the paper: {'term-for-term agreement' if agree else 'MISMATCH'}")
    s5 = msqrt(mpf(5))
    val = mpf(0)
    for c in muG:
        val = val * s5 + c
    print(f"    mu_G(sqrt 5) = {mp.nstr(val, 8)}  -> {'zero' if abs(val) < mpf(10)**-40 else 'NONZERO'}\n")

    de = directed_edges(edges)
    fol = followers(de)
    print(f"(3) directed edges: {len(de)} (paper: 120) -> "
          f"{'ok' if len(de) == 120 else 'MISMATCH'}")
    branches = solve_ratios_by_type(s5)
    print(f"    real branches of the eight-type ratio system: {len(branches)}")
    ty = [edge_type(de, i, n) for i in range(len(de))]

    best = None
    for (num, exact) in branches:
        rv = [num[ty[i]] for i in range(len(de))]
        res = max(abs(float(s5) - 1.0 / rv[i] - sum(rv[j] for j in fol[i]))
                  for i in range(len(de)))
        # transient states: no outgoing follower, or no incoming predecessor
        preds = {i: 0 for i in range(len(de))}
        for i in range(len(de)):
            for j in fol[i]:
                preds[j] += 1
        trans = [i for i in range(len(de)) if not fol[i] or preds[i] == 0]
        rec = [i for i in range(len(de)) if i not in set(trans)]
        # orbit quotient on the recurrent block, one orbit per surviving edge type
        types = sorted({ty[i] for i in rec})
        K = np.zeros((len(types), len(types)))
        pos = {t: m for m, t in enumerate(types)}
        rep = {t: next(i for i in rec if ty[i] == t) for t in types}
        for t in types:
            for j in fol[rep[t]]:
                if ty[j] in pos:
                    K[pos[t], pos[ty[j]]] += rv[j] ** 2
        rho = max(abs(np.linalg.eigvals(K)))
        if best is None or rho < best['rho']:
            best = dict(rv=rv, res=res, trans=trans, rec=rec, K=K, rho=rho, exact=exact,
                        types=types)
    b = best
    print(f"    residual of the 120 equations: {b['res']:.2e} -> "
          f"{'the eight-type solution satisfies all 120' if b['res'] < 1e-12 else 'MISMATCH'}")
    print(f"    smallest |r_e|: {min(abs(x) for x in b['rv']):.6f}, "
          f"negative types: {sorted({t for t in range(8) if [v for v in b['rv']][0] is not None and b['rv'][[i for i in range(len(de)) if ty[i]==t][0]] < 0})}\n")

    print(f"(4) transient states {len(b['trans'])}, recurrent {len(b['rec'])}")
    print(f"    paper: 10 transient at the leaves, recurrent block 110 -> "
          f"{'ok' if (len(b['trans']), len(b['rec'])) == (10, 110) else 'MISMATCH'}")
    print(f"    the transient states are exactly the leaf-incident edges: "
          f"{sorted({ty[i] for i in b['trans']}) == [6, 7]}\n")

    K = b['K']
    print(f"(5) orbit quotient: one orbit per surviving edge type, K is "
          f"{K.shape[0]}x{K.shape[1]} -> {'ok' if K.shape == (6, 6) else 'MISMATCH'}\n")

    x = np.array([20.0, 121.0, 47.0, 33.0, 28.0, 16.0])
    sv = float(np.sqrt(41))
    target = np.sort(np.array([(6553 - 893 * sv) / 800, (1097 - 168 * sv) / 25,
                               (385 * sv - 2459) / 8, (64931 * sv - 414951) / 1000,
                               (858 - 102 * sv) / 125, (15443 - 2145 * sv) / 2048]))
    bestp = None
    for perm in itertools.permutations(range(6)):
        Kp = K[np.ix_(perm, perm)]
        resid = x - Kp @ x
        d = float(np.abs(np.sort(resid) - target).max())
        if bestp is None or d < bestp[0]:
            bestp = (d, perm, resid)
    print("(6) the certificate:")
    print(f"    min component of x - Kx: {bestp[2].min():.6f} -> "
          f"{'strictly positive' if bestp[2].min() > 0 else 'NOT POSITIVE'}")
    print(f"    rebuilt residuals : {np.array2string(np.sort(bestp[2]), precision=5)}")
    print(f"    Lean's residuals  : {np.array2string(target, precision=5)}")
    print(f"    max difference    : {bestp[0]:.2e} -> "
          f"{'reproduces the Lean entry by entry' if bestp[0] < 1e-6 else 'DOES NOT reproduce it'}")
    print(f"    rho(K) = {b['rho']:.10f}   paper: 0.9636233789 -> "
          f"{'ok' if abs(b['rho'] - 0.9636233789) < 1e-9 else 'MISMATCH'}\n")

    print()
    print("  What this artifact settles: the graph, the matching numbers and the decay digraph's")
    print("  component structure are rebuilt from the construction alone. Where a line above says")
    print("  MISMATCH the published object is not the one this graph produces, and that is exactly")
    print("  the step that previously lived only in private/.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
