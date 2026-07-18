#!/usr/bin/env python3
"""MOONSHOT: does the d-matching polynomial of K4 have a closed-form recurrence?

Data: mu_d = Psi_{d+1} (exact, from paper4 §2.1). mu_0=1, mu_1..mu_5 below.
Cycles satisfy mu_{d+1} = 2*T_n(x/2)*mu_d - mu_{d-1} (3-term, constant-in-d,
poly-in-x coeffs). We test whether K4 satisfies ANY low-order linear
recurrence with polynomial (or rational) coefficients in x, constant in d.
Memory-light: exact sympy on deg<=20 polynomials.
"""
import sympy as sp

x = sp.symbols('x')

mu = {
 0: sp.Integer(1),
 1: x**4 - 6*x**2 + 3,
 2: x**8 - 12*x**6 + 42*x**4 - 40*x**2 + 6,
 3: x**12 - 18*x**10 + 117*x**8 - 332*x**6 + 393*x**4 - 158*x**2 + sp.Rational(97,9),
 4: x**16 - 24*x**14 + 228*x**12 - 1092*x**10 + 2781*x**8 - 3654*x**6
      + 2230*x**4 - 495*x**2 + sp.Rational(75,4),
 5: x**20 - 30*x**18 + 375*x**16 - 2536*x**14 + 10086*x**12
      - sp.Rational(120204,5)*x**10 + sp.Rational(840006,25)*x**8
      - sp.Rational(646848,25)*x**6 + sp.Rational(242478,25)*x**4
      - sp.Rational(34068,25)*x**2 + sp.Rational(162,5),
}
for d in mu: mu[d] = sp.expand(mu[d])

print("=== TEST 1: 3-term, constant-in-d, poly/rational coeffs A(x),B(x) ===")
# mu_{d+1} = A*mu_d + B*mu_{d-1}; solve from d=1,2 then check d=3,4.
A, B = sp.symbols('A B')
sol = sp.solve([sp.Eq(mu[2], A*mu[1] + B*mu[0]),
                sp.Eq(mu[3], A*mu[2] + B*mu[1])], [A, B], dict=True)
if sol:
    A0 = sp.cancel(sol[0][A]); B0 = sp.cancel(sol[0][B])
    print("A(x) =", A0)
    print("B(x) =", B0)
    A_poly = sp.simplify(A0).is_polynomial(x)
    B_poly = sp.simplify(B0).is_polynomial(x)
    print("A polynomial?", A_poly, " B polynomial?", B_poly)
    chk3 = sp.simplify(mu[4] - (A0*mu[3] + B0*mu[2]))
    chk4 = sp.simplify(mu[5] - (A0*mu[4] + B0*mu[3]))
    print("predicts mu_4?", chk3 == 0, "  predicts mu_5?", chk4 == 0)
else:
    print("no solution")

print("\n=== TEST 2: 3-term with rational coeffs, does it hold for ALL d? ===")
# If A,B above are not polynomials or don't predict, try solving with 3 eqs / least structure.

print("\n=== TEST 3: rational generating function G(x,z)=sum mu_d z^d = P/Q ===")
# Guess Q(z) of degree q with coeffs poly in x: sum_{k} q_k(x) mu_{d+k} = 0 (d>=0).
# Equivalent to a linear recurrence of order q. Try q=2,3 with poly coeffs of
# bounded x-degree via linear algebra over the mu-data.
z = sp.symbols('z')
def try_recurrence(order, maxdeg):
    """Seek q_0..q_order (poly in x, deg<=maxdeg, q_order=1 monic) with
       sum_k q_k(x) mu_{d+k} = 0 for all available d."""
    # unknowns: coefficients of q_0..q_{order-1}
    coeffs = {}
    unknown = []
    for k in range(order):
        cs = sp.symbols(f'c_{k}_0:{maxdeg+1}')
        coeffs[k] = cs
        unknown += list(cs)
    def qk(k):
        return sum(coeffs[k][j]*x**j for j in range(maxdeg+1))
    eqs = []
    dmax = 5 - order
    for d in range(0, dmax+1):
        expr = mu[d+order] + sum(qk(k)*mu[d+k] for k in range(order))
        # expr must be identically 0 in x
        p = sp.Poly(sp.expand(expr), x)
        eqs += p.all_coeffs()
    sol = sp.solve(eqs, unknown, dict=True)
    return sol, coeffs, qk
for order in (2, 3):
    for maxdeg in range(0, 9):
        sol, coeffs, qk = try_recurrence(order, maxdeg)
        if sol:
            print(f"order={order}, maxdeg={maxdeg}: SOLUTION FOUND")
            s = sol[0]
            for k in range(order):
                print(f"  q_{k}(x) =", sp.expand(qk(k).subs(s)))
            # verify it is fully determined (no free params) and check
            break
    else:
        continue
    break
else:
    print("no constant-in-d polynomial recurrence of order<=3, xdeg<=8 found")
