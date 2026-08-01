r"""hl_theory.py -- the identities and bounds PROVED in this pass, each verified
numerically here to ~1e-12 before being asserted.

Notation.  A_1..A_q PSD of rank <= 2 on R^m;  omega_k = b_{k1} ^ b_{k2} in Lambda^2;
c_k = e_2(A_k) = ||omega_k||^2;  V_k = range A_k;  Theta_k = c_k P_{V_k};
Adj(A) = sum_k Theta_k;  omega_T = ^_{k in T} omega_k;  M_r = sum_{|T|=r}||omega_T||^2;
F_A(x) = sum_r (-1)^r M_r x^{m-2r}   ( = mu_A(x+a) when sum_k A_k = a I ).
For a form w, M_w is the PSD matrix with <v,M_w v> = ||iota_v w||^2.
A^(e) = compression of the family to e^perp;  Phi_e = sum_k f_k f_k^T, f_k = iota_e omega_k.

T1  REDUCTION TO PLANES.  F_A and Adj(A) depend on (A_k) only through (c_k, V_k):
    omega_k = sqrt(c_k) w_k with w_k the unit bivector of V_k, and Theta_k = c_k P_{V_k}.
    So the class is  { 2-planes V_k with weights c_k >= 0, sum_k c_k P_{V_k} <= aI },
    F is the "matching polynomial of a weighted plane family", and for coordinate
    planes it is literally the weighted matching polynomial of a graph.
    ==> the target 2 sqrt(a) is the SHARP weighted Heilmann-Lieb constant 2 sqrt(D),
    attained in the limit by weighted K_m.

T2  THE VERTEX MATRIX.  Put Theta^(r) := sum_{|T|=r} M_{omega_T}  (PSD) and
        W(x) := sum_{r>=1} (-1)^r Theta^(r) x^{m-2r}.
    Then for EVERY unit e
        <e, W(x) e>  =  F_A(x) - x F_{A^(e)}(x),
    tr Theta^(r) = 2 r M_r,  tr W(x) = m F_A(x) - x F_A'(x),  and summing over an
    orthonormal basis, F_A'(x) = sum_i F_{A^(e_i)}(x).
    Proof: ||omega_T||^2 = ||pi_{e^perp} omega_T||^2 + ||iota_e omega_T||^2, and
    pi_{e^perp} is an algebra homomorphism on Lambda, so pi(omega_T) = ^ pi(omega_k).

T3  THE CAVITY REMAINDER IS CANONICAL (a NEGATIVE result: it removes a natural
    repair).  The cavity step needs only sum_alpha nu_alpha = tr Phi_e, so one is
    free to use ANY rank-one decomposition Phi_e = sum_alpha nu_alpha h h^T with
    unit h in e^perp.  But
        sum_alpha nu_alpha F_{A^(e,h_alpha)}(x)
            = [ D_A(e) F_{A^(e)}(x) - tr( Phi_e W^(e)(x) ) ] / x
    depends only on Phi_e.  Hence the remainder
        Y_e(x) := F_A(x) - x F_{A^(e)}(x) + sum_alpha nu_alpha F_{A^(e,h_alpha)}(x)
                = <e,W(x)e> + [ D_A(e) F_{A^(e)}(x) - tr(Phi_e W^(e)(x)) ] / x
    is the SAME for every decomposition, and equals -X_e for the canonical
    h = fhat_k, nu = theta_k.  Proof: ||pi_{h^perp} G||^2 = ||G||^2 - <h, M_G h>.

T4  C_2 (the leading overlap coefficient).  With f_j = iota_e omega_j and
    g_j = pi_{e^perp} omega_j:  f_j lies in the plane of g_j, so f_j ^ g_j = 0 and
    ||iota_{f_j} g_j||^2 = ||f_j||^2 ||g_j||^2; and sum_j iota_{f_j} g_j
    = - pi_{e^perp}( Adj(A) e ).  Hence
        C_2 = 1^T (Fm o Gm) 1 - || pi_{e^perp}( Adj(A) e ) ||^2,
    Fm_{jl} = <f_j,f_l>, Gm_{jl} = <g_j,g_l>.  Both are Gram matrices, so by the
    Schur product theorem C_2 >= 0 whenever Adj(A) e is parallel to e -- in
    particular whenever Adj(A) = a I.

T5  THE INDUCTION HYPOTHESIS IN MATRIX FORM.  With x = t + a/t, t >= sqrt(a) and
    d = <e,Adj(A)e>, the cavity hypothesis  F_A >= (x - d/t) F_{A^(e)}  is
    EQUIVALENT to    d F_A(x) + (t^2 + a - d) <e,W(x)e>  >=  0 .
    For Adj(A) = a I this is the single matrix inequality
        W(x) + (a/t^2) F_A(x) I  >=  0        (at t = sqrt a:  W + F_A I >= 0).

T6  UNCONDITIONAL BOUNDS (real-rooted F_A).
    (A)  max root^2 <= M_1 = tr Adj(A)/2 <= a m / 2      => the band for m <= 8.
    (B)  max root^4 <= M_1^2 - 2 M_2 <= tr(Adj^2) - sum_k c_k^2 <= a^2 m - sum c_k^2
         => the band whenever m <= 16 + (sum_k c_k^2)/a^2, i.e. m <= 32a/(2a-1)
         for a projection family.  (B) uses  ||w_j ^ w_l||^2 >= 1 - tr(P_j P_l).
"""
import numpy as np
import hl_planes as H


def W_matrix(Bs, m, x):
    """W(x) = sum_{r>=1} (-1)^r Theta^(r) x^{m-2r}, built from the definition."""
    from itertools import combinations
    q = len(Bs)
    out = np.zeros((m, m))
    for r in range(1, m // 2 + 1):
        Th = np.zeros((m, m))
        for T in combinations(range(q), r):
            Th += M_of_wedge([Bs[k] for k in T], m)
        out += ((-1) ** r) * Th * x ** (m - 2 * r)
    return out


def M_of_wedge(Blist, m):
    """M_{omega_T} for omega_T = ^_k (b_k1 ^ b_k2):  <v,Mv> = ||iota_v omega_T||^2.
    Computed from the Gram matrix: with C the m x 2r matrix of all the b's,
    ||iota_v omega||^2 = sum over columns j of  det Gram(C with column j replaced
    ... ) -- simplest correct route: expand iota_v (^ cols) by Leibniz."""
    C = np.hstack(Blist)                      # m x n, n = 2r
    n = C.shape[1]
    G = C.T @ C
    # iota_v (c_1^...^c_n) = sum_j (-1)^{j-1} <v,c_j> (c_1^..^ĉ_j^..^c_n)
    # so M = sum_{j,k} (-1)^{j+k} <c_j ^..^, ..> c_j c_k^T with the (n-1)-Gram
    Mm = np.zeros((m, m))
    minors = np.zeros((n, n))
    for j in range(n):
        for k in range(n):
            idxj = [i for i in range(n) if i != j]
            idxk = [i for i in range(n) if i != k]
            minors[j, k] = np.linalg.det(G[np.ix_(idxj, idxk)])
    for j in range(n):
        for k in range(n):
            Mm += ((-1) ** (j + k)) * minors[j, k] * np.outer(C[:, j], C[:, k])
    return Mm


def check(name, val, tol=1e-9):
    print(f"    {name:62s} err = {val:9.2e}   {'ok' if val < tol else 'FAIL'}")
    return val < tol


if __name__ == '__main__':
    rng = np.random.default_rng(7)
    cases = []
    cases.append(('K_{3,3}', H.graph_blocks(
        [(i, 3 + j) for i in range(3) for j in range(3)], 6), 6, 3))
    cases.append(('weighted K_6 a=3', H.graph_blocks(
        H.Kn_edges(6), 6, [3.0 / 5] * 15), 6, 3))
    Bs, err = H.random_projection_family(6, 3, seed=5)
    if err < 1e-11:
        cases.append(('randproj m6 a3', Bs, 6, 3))
    Bs, res = H.random_plane_family(5, 3, seed=3)
    if Bs is not None:
        cases.append(('randplane m5 a3', Bs, 5, 3))

    ok = True
    for nm, Bs, m, a in cases:
        print(f"  == {nm}  (m={m}, q={len(Bs)}, a={a}) ==")
        FA = H.F_dense(Bs, m)
        Adm = H.Adj(Bs)

        # T1 : replacing A_k by sqrt(c_k) P_{V_k} changes nothing
        Bs2 = []
        for B in Bs:
            c = float(np.linalg.det(B.T @ B))
            Qb, _ = np.linalg.qr(B)
            Bs2.append(Qb * c ** 0.25)
        ok &= check('T1  F_A depends only on (c_k, V_k)',
                    float(np.abs(H.F_dense(Bs2, m) - FA).max()
                          / max(1, np.abs(FA).max())))
        ok &= check('T1  Adj depends only on (c_k, V_k)',
                    float(np.abs(H.Adj(Bs2) - Adm).max()))

        x = 2 * np.sqrt(a) * 1.3
        Wx = W_matrix(Bs, m, x)

        # T2 : <e,W e> = F_A - x F_{A^(e)}
        e2err = 0.0
        for _ in range(4):
            e = rng.standard_normal(m)
            e /= np.linalg.norm(e)
            Fc = H.F_dense(H.compress(Bs, H.ortho_complement([e], m)), m - 1)
            lhs = float(e @ Wx @ e)
            rhs = np.polyval(FA, x) - x * np.polyval(Fc, x)
            e2err = max(e2err, abs(lhs - rhs) / max(1.0, abs(rhs)))
        ok &= check('T2  <e,W(x)e> = F_A(x) - x F_{A^(e)}(x)', e2err)
        dF = np.polyder(FA)
        ok &= check('T2  tr W(x) = m F_A(x) - x F_A\'(x)',
                    abs(np.trace(Wx) - (m * np.polyval(FA, x)
                                        - x * np.polyval(dF, x)))
                    / max(1.0, abs(np.polyval(FA, x))))
        s = 0.0
        for i in range(m):
            e = np.eye(m)[i]
            s += np.polyval(H.F_dense(H.compress(
                Bs, H.ortho_complement([e], m)), m - 1), x)
        ok &= check("T2  sum_i F_{A^(e_i)}(x) = F_A'(x)",
                    abs(s - np.polyval(dF, x)) / max(1.0, abs(s)))

        # T3 : the remainder does not depend on the rank-one decomposition
        import hl_decomp as D
        e = rng.standard_normal(m)
        e /= np.linalg.norm(e)
        Yf, Fc, sf, trf = D.Y_of(Bs, m, e, 'f')
        Ye, _, se, tre = D.Y_of(Bs, m, e, 'eig')
        ok &= check('T3  Y^f = Y^eig  (remainder is canonical)',
                    float(np.abs(Yf - Ye).max() / max(1.0, np.abs(Yf).max())))
        R = H.recursion(Bs, m, e)
        ok &= check('T3  Y_e = -X_e for the canonical decomposition',
                    float(np.abs(Yf + R['X']).max() / max(1.0, np.abs(Yf).max())))
        # T3 closed form:  Y_e = <e,We> + [D F_{A'} - tr(Phi_e W')]/x
        Q = H.ortho_complement([e], m)
        Ac = H.compress(Bs, Q)
        Wp = W_matrix(Ac, m - 1, x)
        Phi_c = Q @ R['Phi'] @ Q.T
        d = float(e @ Adm @ e)
        closed = (float(e @ Wx @ e)
                  + (d * np.polyval(Fc, x) - float(np.trace(Phi_c @ Wp))) / x)
        ok &= check('T3  Y_e = <e,We> + [D F_{A\'} - tr(Phi_e W\')]/x',
                    abs(closed - np.polyval(Yf, x))
                    / max(1.0, abs(np.polyval(Yf, x))))

        # T4 : the C_2 identity
        fs = R['fs']
        gsB = [Q @ B for B in Bs]
        Fm = np.array([[float(fi @ fj) for fj in fs] for fi in fs])
        gv = []
        for B in gsB:
            gv.append(B)
        Gm = np.zeros((len(Bs), len(Bs)))
        for j in range(len(Bs)):
            for l in range(len(Bs)):
                # <g_j, g_l> for decomposable 2-forms: det of the 2x2 cross-Gram
                Cj, Cl = gsB[j], gsB[l]
                Gm[j, l] = np.linalg.det(Cj.T @ Cl)
        C2 = H.C_list(R['X'], m)[0] if m >= 4 else None
        if C2 is not None:
            pred = float(Fm.__mul__(Gm).sum()
                         - np.linalg.norm(Q.T @ (Q @ (Adm @ e))) ** 2)
            ok &= check('T4  C_2 = 1^T(F o G)1 - ||pi_{e^perp} Adj e||^2',
                        abs(C2 - pred) / max(1.0, abs(C2)))

        # T5 : IH  <=>  d F_A + (t^2+a-d) <e,W e>  >= 0
        t = np.sqrt(a) * 1.2
        xx = t + a / t
        Wxx = W_matrix(Bs, m, xx)
        bad = 0.0
        for _ in range(4):
            v = rng.standard_normal(m)
            v /= np.linalg.norm(v)
            Fc2 = H.F_dense(H.compress(Bs, H.ortho_complement([v], m)), m - 1)
            dv = float(v @ Adm @ v)
            lhs = np.polyval(FA, xx) - (xx - dv / t) * np.polyval(Fc2, xx)
            rhs = (dv * np.polyval(FA, xx)
                   + (t * t + a - dv) * float(v @ Wxx @ v)) / (t * xx)
            bad = max(bad, abs(lhs - rhs) / max(1.0, abs(lhs)))
        ok &= check('T5  IH  <=>  d F_A + (t^2+a-d)<e,We> >= 0', bad)

        # T6 : the two unconditional bounds
        rts = float(np.abs(np.roots(FA)).max())
        M = H.M_coeffs(Bs, m)
        cs = np.array([float(np.linalg.det(B.T @ B)) for B in Bs])
        bA = np.sqrt(M[1])
        bB = (M[1] ** 2 - 2 * M[2]) ** 0.25 if len(M) > 2 else np.inf
        bB2 = (float(np.trace(Adm @ Adm)) - (cs ** 2).sum()) ** 0.25
        print(f"    T6  maxroot={rts:8.5f}  BOUND A={bA:8.5f}  "
              f"(M1^2-2M2)^(1/4)={bB:8.5f}  tr(Adj^2)-sum c^2 form={bB2:8.5f}  "
              f"{'ok' if rts <= min(bA, bB, bB2) + 1e-8 else 'FAIL'}")
        ok &= rts <= min(bA, bB, bB2) + 1e-8
        print()
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED")
