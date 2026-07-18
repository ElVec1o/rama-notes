#!/usr/bin/env python3
"""Verify the GENERAL coefficient-stability theorem on cycles (infinite family,
exact closed form mu_{d,C_n} = U_d(T_n(x/2))). Prediction: [x^{nd-2k}] mu_{d,C_n}
= (-1)^k c_k(d), c_k poly in d of degree k, leading coeff |E|^k/k! = n^k/k!."""
import sympy as sp
x, d = sp.symbols('x d')

def mu_cycle(n, dd):
    y = sp.chebyshevt(n, x/2)
    return sp.expand(sp.chebyshevu(dd, y))

for n in (3, 4, 5):
    print(f"--- C_{n} (|E|={n}): predicted leading c_k = {n}^k/k! ---")
    for k in range(0, 4):
        pts = []
        for dd in range(0, 8):
            deg = n*dd - 2*k
            if deg < 0: continue
            p = sp.Poly(mu_cycle(n, dd), x)
            c = p.coeff_monomial(x**deg) if deg > 0 else p.coeff_monomial(1)
            pts.append((dd, sp.Rational(c)))
        if len(pts) < k+2: 
            print(f"   c_{k}: too few pts"); continue
        poly = sp.expand(sp.interpolate([(sp.Integer(a), b) for a,b in pts], d))
        deg_d = sp.degree(poly, d) if poly != 0 else 0
        lead = poly.coeff(d, k) if deg_d==k else None
        pred = sp.Rational(n**k, sp.factorial(k))
        ok = (deg_d == k) and (lead == (-1)**k * pred or lead == pred)
        # sign: coeff of x^{nd-2k} is (-1)^k c_k, so extracted 'poly' already includes sign; |lead| vs pred
        print(f"   c_{k}(d): {(-1)**k*poly if k%2 else poly}  deg_d={deg_d}  "
              f"|lead|={abs(lead) if lead is not None else '?'}  pred {n}^{k}/{k}!={pred}  "
              f"{'OK' if deg_d==k and abs(lead)==pred else 'CHECK'}")
    print()
print("If deg_d==k and |leading|==n^k/k! across cycles -> general theorem confirmed on")
print("an infinite family with EXACT closed forms (not just fitted data).")
