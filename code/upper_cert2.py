r"""Exact rational certificate: S > Lambda(y) on a legal K(3,2) kernel.

Kills the per-slot tree-interval invariant (S-hi side) of the upper-edge
ratio induction: for the explicit rational (c, v, M) below, all class
constraints hold exactly, and
    S := N_{M - vv^T/c}(y) / N_M(y)  >  Lambda(y) = y / A_+(y)
exactly at y = 583/100, 2919/500, 117/20 (all > (1+sqrt2)^2 = upper edge).
The exact test for S > Lambda: Q(y/S) < 0 with Q(A) = A^2-(y-a+b)A+(b-1)y.
Provenance: Schur-descent state of the rotated-complementary-pairs Naimark
kernel (4,6,3,2), rationalised and exactly repaired (upper_dissect.py).
Verifier below is pure Fraction arithmetic (imports from upper_cert).
"""
import sys
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from fractions import Fraction as F
from upper_cert import is_psd, mat_add, sc_mul, N_frac

a, b = 3, 2
blocks = [[0, 1], [2, 3], [4, 5], [6, 7]]
c = F(171, 4000)
v = [F(-128356288710644871, 4000000000000000000), F(-424869265732134573, 4000000000000000000), F(995009990004999, 4000000000000000000), F(48755489510244951, 4000000000000000000), F(-110446108890554889, 1000000000000000000), F(168156688310844831, 4000000000000000000), F(-410939125872064587, 4000000000000000000), F(2985029970014997, 800000000000000000)]
M = [
    [F(799401433, 2400000000), F(0), F(21827, 100000), F(-36179, 150000), F(15847, 240000), F(-299, 24000), F(-24817, 1200000), F(46943, 300000)],
    [F(0), F(799401433, 2400000000), F(-107939, 1200000), F(-2093, 400000), F(35581, 150000), F(-85813, 400000), F(371059, 1200000), F(2093, 37500)],
    [F(21827, 100000), F(-107939, 1200000), F(53373389, 300000000), F(-112144087, 800000000), F(2093, 120000), F(34983, 400000), F(-53521, 600000), F(15249, 400000)],
    [F(-36179, 150000), F(-2093, 400000), F(-112144087, 800000000), F(495952727, 2400000000), F(6279, 400000), F(94783, 1200000), F(9867, 400000), F(-242489, 1200000)],
    [F(15847, 240000), F(35581, 150000), F(2093, 120000), F(6279, 400000), F(31784153, 96000000), F(-7796113, 800000000), F(59501, 240000), F(-24219, 200000)],
    [F(-299, 24000), F(-85813, 400000), F(34983, 400000), F(94783, 1200000), F(-7796113, 800000000), F(136132127, 480000000), F(-100763, 600000), F(-8671, 37500)],
    [F(-24817, 1200000), F(371059, 1200000), F(-53521, 600000), F(9867, 400000), F(59501, 240000), F(-100763, 600000), F(711845087, 2400000000), F(599701, 480000000)],
    [F(46943, 300000), F(2093, 37500), F(15249, 400000), F(-242489, 1200000), F(-24219, 200000), F(-8671, 37500), F(599701, 480000000), F(799401433, 2400000000)],
]


def verify():
    n = len(M)
    I = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    third = F(1, a)
    ok = True
    ok &= is_psd(M); print('M PSD                  :', is_psd(M))
    t = is_psd(mat_add(I, sc_mul(-1, M))); ok &= t
    print('I - M PSD              :', t)
    for kk, bk in enumerate(blocks):
        B = [[third * F(int(i == j)) - M[bi][bj]
              for j, bj in enumerate(bk)] for i, bi in enumerate(bk)]
        t = is_psd(B); ok &= t
        print(f'(1/a)I - block{kk+1} PSD   :', t)
    print('c <= 1/a               :', c <= third); ok &= c <= third
    Md = [[M[i][j] - v[i] * v[j] / c for j in range(n)] for i in range(n)]
    t = is_psd(Md); ok &= t
    print('M - vv^T/c PSD         :', t)
    IM = mat_add(I, sc_mul(-1, M))
    R = [[IM[i][j] - v[i] * v[j] / (1 - c) for j in range(n)]
         for i in range(n)]
    t = is_psd(R); ok &= t
    print('(I-M) - vv^T/(1-c) PSD :', t)
    delta = sum(x * x for x in v) / c
    print('delta = |v|^2/c        =', float(delta))
    for y in (F(583, 100), F(2919, 500), F(117, 20)):
        NM = N_frac(M, blocks, a, y)
        NMp = N_frac(Md, blocks, a, y)
        S = NMp / NM
        x = y / S
        Qx = x * x - (y - a + b) * x + (b - 1) * y
        viol = Qx < 0
        ok &= viol and NM > 0
        print(f'y = {y}: N_M > 0: {NM > 0}   S = {float(S):.6f}   '
              f'S > Lambda(y) exactly: {viol}')
    print('CERTIFICATE VALID      :', ok)
    return ok


if __name__ == '__main__':
    verify()
