"""Independent cross-check of the paper4 pipeline using sympy + numpy."""
import itertools, random
from fractions import Fraction
import sympy as sp
from paper4_exact_k4_lifts import lift_matrix, det_bareiss, interp_exact

random.seed(7)
x = sp.symbols('x')

# 1) random triples r=3: my interpolated char poly vs sympy charpoly
r = 3
perms = list(itertools.permutations(range(r)))
for trial in range(4):
    s1, s2, s3 = (random.choice(perms) for _ in range(3))
    pts = [(x0, det_bareiss(lift_matrix(r, s1, s2, s3, x0))) for x0 in range(-6, 7)]
    mine = interp_exact(pts)  # ascending
    A = sp.zeros(4*r)
    M0 = lift_matrix(r, s1, s2, s3, 0)   # = -A
    for i in range(4*r):
        for j in range(4*r):
            A[i, j] = -M0[i][j]
    cp = A.charpoly(x).all_coeffs()[::-1]  # ascending
    assert [Fraction(int(c)) for c in cp] == mine, f"MISMATCH {s1} {s2} {s3}"
print("per-matrix charpoly cross-check (sympy Berkowitz): OK, 4/4")

# 2) full expected char poly r=2 via sympy directly over all 8 triples
r = 2
perms = list(itertools.permutations(range(r)))
tot = sp.zeros(1)[0] * 0
for s1 in perms:
    for s2 in perms:
        for s3 in perms:
            M0 = lift_matrix(r, s1, s2, s3, 0)
            A = sp.Matrix(8, 8, lambda i, j: -M0[i][j])
            tot = tot + A.charpoly(x).as_expr()
phi = sp.expand(tot / 8)
base = sp.expand((x - 3) * (x + 1) ** 3)
quot = sp.simplify(sp.cancel(phi / base))
print("r=2 expected char poly / chi =", sp.expand(quot))
