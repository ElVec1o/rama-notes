r"""Exact rational certificate that the unfolding inequality (UI) FAILS on
the kernel class K(3,2) -- the kill certificate for the scalar cavity route.

(UI) claim (graph identity, conjectured inequality):
    N_M(y) >= N_{M'}(y) - a sum_k m_k N_{M' \ blk k}(y),
    M' = M - v v^T / c,  m_k = |v_k|^2 / c,
for legal bordered kernels [[c, v^T],[v, M]] in class, y > (s+t)^2.

This script constructs an explicit rational (c, v, M, y), verifies ALL class
constraints in exact arithmetic, and evaluates the (UI) slack exactly.
Everything below is Fraction arithmetic; numpy appears only to seed the
rounding.  Constraint tests used (all exact):
  * symmetric rational A is PSD  iff  char poly det(tI - A) = sum c_j t^j
    has (-1)^{n-j} c_j >= 0 for all j  (alternating-sign test).
  * block <= (1/a) I  iff  (1/a)I - block is PSD.
  * bordered PSD  iff  M - vv^T/c PSD (Schur, c>0);
    bordered <= I  iff  (I-M) - vv^T/(1-c) PSD.
"""
import sys
from fractions import Fraction
from itertools import product
import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from frac_naimark import det_frac

SCRATCH = ('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-RAMA-'
           'NOTEBOOK/0d522a0e-ade5-4120-8948-e5567f4829cb/scratchpad')


# ------------------------------------------------------- exact linear algebra
def charpoly_frac(A):
    """coefficients of det(tI - A) via Faddeev-LeVerrier, exact."""
    n = len(A)
    I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    c = [Fraction(1)]
    Mk = [row[:] for row in I]
    Ak = A
    M = [row[:] for row in I]
    coeffs = [Fraction(1)]
    for k in range(1, n + 1):
        AM = mat_mul(A, M)
        ck = Fraction(-1, k) * trace(AM)
        coeffs.append(ck)
        M = mat_add(AM, sc_mul(ck, I))
    return coeffs        # det(tI-A) = sum coeffs[j] t^{n-j}


def mat_mul(A, B):
    n = len(A)
    m = len(B[0])
    K = len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(K)) for j in range(m)]
            for i in range(n)]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))]
            for i in range(len(A))]


def sc_mul(s, A):
    return [[s * x for x in row] for row in A]


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def is_psd(A):
    """exact PSD test via alternating signs of char poly of A."""
    co = charpoly_frac(A)      # det(tI - A) = sum co[j] t^{n-j}
    n = len(A)
    # eigenvalues >= 0 iff det(tI - A) has no sign changes for t<0:
    # coefficients of det(tI-A) in t: co[j] multiplies t^{n-j};
    # PSD iff (-1)^j co[j] >= 0 for all j.
    return all(((-1) ** j) * co[j] >= 0 for j in range(n + 1))


def N_frac(K, blocks, a, y):
    """exact N_K(y) for rational y."""
    q = len(blocks)
    opts = [[None] + list(bk) for bk in blocks]
    tot = Fraction(0)
    for choice in product(*opts):
        T = [x for x in choice if x is not None]
        m = len(T)
        d = det_frac([[K[i][j] for j in T] for i in T]) if m else Fraction(1)
        tot += Fraction((-a) ** m) * d * y ** (q - m)
    return tot


# ------------------------------------------------------- build the certificate
def build_certificate(denom=400, theta_grid=60):
    dat = np.load(SCRATCH + '/ui_min_violator.npz')
    Mf, wf, cf = dat['M'], dat['w'], float(dat['c'])
    n = 4
    a = 3
    blocks = [[0, 1], [2, 3]]

    def rat(x, d=denom):
        return Fraction(round(x * d), d)

    c = rat(cf, 64)
    vf = np.sqrt(cf) * wf
    v = [rat(x) for x in vf]
    M0 = [[rat(Mf[i, j]) for j in range(n)] for i in range(n)]
    # symmetrise exactly
    M0 = [[(M0[i][j] + M0[j][i]) / 2 for j in range(n)] for i in range(n)]
    # exact block-2 = (1/3) I
    M0[2][2] = M0[3][3] = Fraction(1, 3)
    M0[2][3] = M0[3][2] = Fraction(0)

    Ifr = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    D = [[M0[i][j] if (i < 2) == (j < 2) else Fraction(0) for j in range(n)]
         for i in range(n)]

    third = Fraction(1, 3)

    def block_ok(M):
        for bk in blocks:
            B = [[third * Fraction(int(i == j)) - M[bi][bj]
                  for j, bj in enumerate(bk)] for i, bi in enumerate(bk)]
            if not is_psd(B):
                return False
        return True

    def shrink_block1(M, f):
        M = [row[:] for row in M]
        for i in range(2):
            for j in range(2):
                M[i][j] = M[i][j] * f
        return M

    # make block 1 strictly inside, then mix towards D for global PSD
    M1 = M0
    f = Fraction(1)
    while not block_ok(M1):
        f *= Fraction(199, 200)
        M1 = shrink_block1(M0, f)
    Mc = None
    for t in range(theta_grid):
        th = Fraction(t, 2 * theta_grid)
        Mtry = mat_add(sc_mul(1 - th, M1), sc_mul(th, D))
        if is_psd(Mtry) and is_psd(mat_add(Ifr, sc_mul(-1, Mtry))) \
                and block_ok(Mtry):
            Mc = Mtry
            theta = th
            break
    assert Mc is not None, 'could not repair global PSD'

    # shrink v until bordered kernel is PSD and <= I  (exact)
    def bordered_ok(vv):
        Mdown = [[Mc[i][j] - vv[i] * vv[j] / c for j in range(n)]
                 for i in range(n)]
        if not is_psd(Mdown):
            return False
        IM = mat_add(Ifr, sc_mul(-1, Mc))
        R = [[IM[i][j] - vv[i] * vv[j] / (1 - c) for j in range(n)]
             for i in range(n)]
        return is_psd(R)

    rho = Fraction(1)
    vv = v
    for _ in range(200):
        if bordered_ok(vv):
            break
        rho *= Fraction(99, 100)
        vv = [rho * x for x in v]
    assert bordered_ok(vv), 'could not repair bordered feasibility'
    return a, blocks, c, vv, Mc, theta, rho


def verify(a, blocks, c, v, M, ys):
    n = len(M)
    third = Fraction(1, a)
    Ifr = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    print('exact constraint checks:')
    print(f"   M PSD                : {is_psd(M)}")
    print(f"   I - M PSD            : {is_psd(mat_add(Ifr, sc_mul(-1, M)))}")
    for k, bk in enumerate(blocks):
        B = [[third * Fraction(int(i == j)) - M[bi][bj]
              for j, bj in enumerate(bk)] for i, bi in enumerate(bk)]
        print(f"   (1/a)I - block{k+1} PSD : {is_psd(B)}")
    print(f"   c = {c} <= 1/a       : {c <= third}")
    Md = [[M[i][j] - v[i] * v[j] / c for j in range(n)] for i in range(n)]
    print(f"   M - vv^T/c PSD       : {is_psd(Md)}  (bordered kernel PSD)")
    IM = mat_add(Ifr, sc_mul(-1, M))
    R = [[IM[i][j] - v[i] * v[j] / (1 - c) for j in range(n)]
         for i in range(n)]
    print(f"   (I-M) - vv^T/(1-c)   : {is_psd(R)}  (bordered kernel <= I)")

    m1 = sum(v[i] * v[i] for i in blocks[0]) / c
    m2 = sum(v[i] * v[i] for i in blocks[1]) / c
    print(f"   masses m1 = {m1} = {float(m1):.6f},  m2 = {m2} = "
          f"{float(m2):.6f},  delta = {float(m1 + m2):.6f}")
    for y in ys:
        NM = N_frac(M, blocks, a, y)
        NMp = N_frac(Md, blocks, a, y)
        N1 = N_frac(Md, [blocks[1]], a, y)     # M' minus block 1
        N2 = N_frac(Md, [blocks[0]], a, y)     # M' minus block 2
        slack = NM - (NMp - a * (m1 * N1 + m2 * N2))
        S = NMp / NM
        # S > Lambda test: Q(y/S) < 0 with Q(A) = A^2 - (y-a+b)A + (b-1)y
        b = 2
        x = y / S
        Qx = x * x - (y - a + b) * x + (b - 1) * y
        print(f"   y = {y}:")
        print(f"      N_M(y)  = {NM} = {float(NM):.8f}   (positive: "
              f"{NM > 0})")
        print(f"      (UI) slack = {slack} = {float(slack):.8f}   "
              f"VIOLATED: {slack < 0}")
        print(f"      S = {float(S):.8f};  S > Lambda(y): {Qx < 0}"
              f"   (exact sign of Q(y/S) = {'-' if Qx < 0 else '+'})")


if __name__ == '__main__':
    a, blocks, c, v, M, theta, rho = build_certificate()
    print('rational certificate  (a, b) = (3, 2),  blocks = [[0,1],[2,3]]')
    print(f"   repair parameters: theta = {theta}, rho = {rho}")
    print(f"   c = {c}")
    print(f"   v = {[str(x) for x in v]}")
    print('   M =')
    for row in M:
        print('      [' + ', '.join(str(x) for x in row) + ']')
    verify(a, blocks, c, v, M, [Fraction(6), Fraction(119, 20)])
