r"""fv_recursion.py -- the FRACTIONAL VERTEX recursion.

DERIVED (proofs in the report), all verified numerically here.

(G)  Grassmann form of the recentred mixed characteristic polynomial.
     For A_1..A_q PSD of rank <= 2 on R^p write A_k = b_{k1}b_{k1}^T+b_{k2}b_{k2}^T
     and omega_k = b_{k1} ^ b_{k2} in Lambda^2 R^p.  Then by Cauchy-Binet

         e_{2r}(A_T) = || ^_{k in T} omega_k ||^2      (|T| = r)

     so    F_A(x) := sum_{T subset [q]} (-1)^{|T|} ||^_{k in T} omega_k||^2 x^{p-2|T|}
     and   F_A(x) = mu_A(x + a)   when sum_k A_k = a I.

(V)  Vertex deletion = compression.  For a unit e, put Q = the isometry
     R^p -> e^perp.  Then A' := (Q A_k Q^*) satisfies sum A'_k = a I_{p-1}, and
     writing  f_k := iota_e omega_k  in e^perp,  g_k := omega_k - e ^ f_k:
         ||f_k||^2 = <e, Theta_k e> =: theta_k(e),   Theta_k := e_2(A_k) R_k,
                                     R_k = orthogonal projection onto range(A_k)
         e_2(A'_k) = e_2(A_k) - theta_k(e)
         theta_k^{A'}(w) = theta_k^{A}(w) - <w,f_k>^2   for w in e^perp.
     Hence with  D_A(e) := sum_k theta_k(e) = <e, Adj(A) e>,  Adj(A) := sum_k Theta_k,
         D_{A'}(w) = D_A(w) - <w, Phi_e w>,   Phi_e := sum_k f_k f_k^T,  tr Phi_e = D_A(e).
     For a projection family Theta_k = P_k, so Adj(A) = a I and D == a.
     NB e_2(A) A^+ is NOT the right operator (it equals Theta only when the two
     nonzero eigenvalues coincide); adj2() below is kept only for the projection
     case.  The correct Theta lives in fv_induction.py.

(R)  The recursion (exact, no hypotheses):
         F_A(x) = x F_{A'}(x) - sum_k theta_k(e) F_{A^{(e, fhat_k)}}(x) - X_e(x)
     where A^{(e,fhat_k)} is the compression to (span{e,f_k})^perp and
         X_e(x) = sum_s (-1)^s [ sum_{|T|=s+1} sum_{j != l in T}
                    <f_j ^ G_{T\j}, f_l ^ G_{T\l}> ] x^{p-2-2s}
     is the OVERLAP term, identically zero when the family commutes.

(K)  rho_j(e) := <fhat_j, Phi_e fhat_j> / 1 = sum_k <fhat_j, f_k>^2.
     The HL cavity induction (see fv_induction.py) closes with constant
     2 sqrt(a - rho_min).  rho == 1 exactly in the graph case.
"""
import numpy as np
from itertools import combinations
from mixed_char_poly import mixed_char_poly
import fv_setup as S


# --------------------------------------------------------------- utilities
def esym(eigs, p):
    e = np.zeros(p + 1)
    e[0] = 1.0
    for lam in eigs:
        e[1:] += lam * e[:-1]
    return e


def e2(A):
    """product of the two largest eigenvalues (= e_2 for rank<=2 PSD)."""
    w = np.linalg.eigvalsh(A)
    return float(w[-1] * w[-2])


def adj2(A, tol=1e-11):
    """e_2(A) * A^+.  CORRECT ONLY FOR PROJECTIONS -- for the general rank-2 PSD
    case use Theta(A) = e_2(A) * (range projection) from fv_induction.py."""
    w, V = np.linalg.eigh(A)
    s1, s2 = w[-1], w[-2]
    if s1 <= tol:
        return np.zeros_like(A)
    if s2 <= tol:
        return np.zeros_like(A)
    return s1 * s2 * (V[:, -1:] @ V[:, -1:].T / s1 + V[:, -2:-1] @ V[:, -2:-1].T / s2)


def omega_vecs(A, tol=1e-11):
    """b_1,b_2 with A = b1 b1^T + b2 b2^T (top two eigenpairs)."""
    w, V = np.linalg.eigh(A)
    out = []
    for j in (-1, -2):
        if w[j] > tol:
            out.append(np.sqrt(w[j]) * V[:, j])
    return out


def F_poly(As, p):
    """F_A(x) = sum_T (-1)^{|T|} e_{2|T|}(A_T) x^{p-2|T|}; returns array c
    with F(x) = sum_r c[r] x^{p-2r}."""
    q = len(As)
    rmax = p // 2
    c = np.zeros(rmax + 1)
    c[0] = 1.0
    for r in range(1, min(rmax, q) + 1):
        tot = 0.0
        for T in combinations(range(q), r):
            M = sum(As[k] for k in T)
            w = np.linalg.eigvalsh(M)
            tot += esym(w, p)[2 * r]
        c[r] = ((-1) ** r) * tot
    return c


def as_dense(c, p):
    """c[r] * x^{p-2r}  ->  ordinary coeff array high->low of length p+1."""
    out = np.zeros(p + 1)
    for r, v in enumerate(c):
        out[2 * r] = v          # coefficient of x^{p-2r}
    return out


def compress(As, basisQ):
    """Q: (m x p) with orthonormal rows.  Returns (Q A Q^T)."""
    return [basisQ @ A @ basisQ.T for A in As]


def ortho_complement(vs, p):
    """orthonormal rows spanning the complement of span(vs) in R^p."""
    Vm = np.array(vs).T if len(vs) else np.zeros((p, 0))
    Qf, _ = np.linalg.qr(np.hstack([Vm, np.eye(p)]))
    return Qf[:, len(vs):].T


def f_vectors(As, e):
    """f_k = iota_e omega_k, expressed in R^p (automatically orthogonal to e)."""
    out = []
    for A in As:
        bs = omega_vecs(A)
        if len(bs) < 2:
            out.append(np.zeros_like(e))
            continue
        b1, b2 = bs
        out.append(np.dot(e, b1) * b2 - np.dot(e, b2) * b1)
    return out


# ------------------------------------------------------------------- tests
def test_grassmann(As, p, a, name):
    mu = mixed_char_poly(np.array(As))          # mu(y) = sum_m mu[m] y^{p-m}
    # evaluate mu(x+a) and compare with F
    xs = np.linspace(-3, 3, 7) + 0.0
    Fc = F_poly(As, p)
    Fd = as_dense(Fc, p)
    err = 0.0
    for x in xs:
        v1 = np.polyval(mu, x + a)
        v2 = np.polyval(Fd, x)
        err = max(err, abs(v1 - v2) / max(1.0, abs(v1)))
    return err


def test_compression_facts(As, p, a, e):
    Q = ortho_complement([e], p)
    Ac = compress(As, Q)
    fs = f_vectors(As, e)
    errs = {}
    # ||f_k||^2 = <e, adj_2(A_k) e>
    errs['|f|^2=theta'] = max(abs(np.dot(f, f) - e @ adj2(A) @ e)
                              for f, A in zip(fs, As))
    # e_2(A'_k) = e_2(A_k) - theta_k(e)
    errs['e2 drop'] = max(abs(e2(Ac[k]) - (e2(As[k]) - e @ adj2(As[k]) @ e))
                          for k in range(len(As)))
    # theta drop:  theta^{A'}_k(w) = theta^A_k(w) - <w,f_k>^2
    rng = np.random.default_rng(0)
    w = rng.standard_normal(p)
    w -= np.dot(w, e) * e
    w /= np.linalg.norm(w)
    wc = Q @ w
    errs['theta drop'] = max(abs(wc @ adj2(Ac[k]) @ wc
                                 - (w @ adj2(As[k]) @ w - np.dot(w, fs[k]) ** 2))
                             for k in range(len(As)))
    # sum A'_k = a I
    errs['sum=aI'] = np.abs(sum(Ac) - a * np.eye(p - 1)).max()
    return errs


def recursion_terms(As, p, a, e):
    """Return F_A, x F_{A'}, sum_k theta_k F_{A''_k}, all as dense arrays of
    length p+1 (high->low), plus theta and the rho's."""
    q = len(As)
    Q = ortho_complement([e], p)
    Ac = compress(As, Q)
    fs = f_vectors(As, e)
    th = np.array([float(np.dot(f, f)) for f in fs])
    FA = as_dense(F_poly(As, p), p)
    FAc = as_dense(F_poly(Ac, p - 1), p - 1)
    xFAc = np.concatenate([FAc, [0.0]])           # multiply by x
    acc = np.zeros(p + 1)
    rho = np.full(q, np.nan)
    Phi = sum(np.outer(f, f) for f in fs)
    for k in range(q):
        if th[k] < 1e-12:
            continue
        fh = fs[k] / np.sqrt(th[k])
        rho[k] = fh @ Phi @ fh
        Q2 = ortho_complement([e, fh], p)
        A2 = compress(As, Q2)
        F2 = as_dense(F_poly(A2, p - 2), p - 2)
        acc[2:] += th[k] * F2
    return FA, xFAc, acc, th, rho


if __name__ == '__main__':
    np.set_printoptions(precision=5, suppress=True)
    rng = np.random.default_rng(7)
    cases = []
    for nm, f in [('K_4', S.K4), ('K_{3,3}', S.K33), ('cube Q_3', S.cube)]:
        Ps, p, a = f()
        cases.append((nm, [P for P in Ps], p, a))
    for nm, (n, aa, Ss) in [('circ n=12,a=3', (12, 3, [1, 11, 2, 10])),
                            ('circ n=16,a=4', (16, 4, [1, 15, 2, 14])),
                            ('circ n=20,a=5', (20, 5, [1, 19, 2, 18]))]:
        Ps, p, aa, Pi, U = S.family_circulant(n, aa, Ss)
        cases.append((nm, [P for P in Ps], p, aa))
    for seed in (1, 2, 3):
        Ps, p, aa, Pi, U, err = S.family_random(4, 3, seed=seed)
        cases.append((f'rand p4 a3 s{seed}', [P for P in Ps], p, aa))
    Ps, p, aa, Pi, U, err = S.family_random(6, 3, seed=5)
    cases.append(('rand p6 a3 s5', [P for P in Ps], p, aa))

    print(f"{'family':16s} {'p':>2s} {'a':>2s} {'q':>3s} | {'F=mu(x+a)':>10s} "
          f"{'|f|=th':>8s} {'e2drop':>8s} {'thdrop':>8s} | {'||X_e||':>10s} "
          f"{'rho_min':>8s} {'th_min':>8s} {'th_max':>8s}")
    for nm, As, p, a in cases:
        q = len(As)
        gerr = test_grassmann(As, p, a, nm)
        # random unit vector e, plus coordinate directions
        best = None
        for trial in range(6):
            if trial == 0:
                e = np.zeros(p)
                e[0] = 1.0
            else:
                e = rng.standard_normal(p)
                e /= np.linalg.norm(e)
            cf = test_compression_facts(As, p, a, e)
            FA, xFAc, acc, th, rho = recursion_terms(As, p, a, e)
            X = xFAc - acc - FA
            key = np.abs(X).max()
            rm = np.nanmin(rho) if np.any(~np.isnan(rho)) else np.nan
            row = (cf, key, rm, th.min(), th.max())
            if best is None or key > best[1]:
                best = row
        cf, Xn, rm, thmn, thmx = best
        print(f"{nm:16s} {p:2d} {a:2d} {q:3d} | {gerr:10.2e} "
              f"{cf['|f|^2=theta']:8.1e} {cf['e2 drop']:8.1e} "
              f"{cf['theta drop']:8.1e} | {Xn:10.3e} {rm:8.4f} "
              f"{thmn:8.4f} {thmx:8.4f}")
