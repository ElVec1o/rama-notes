#!/usr/bin/env python3
"""Paper 4: coefficient stability of the K4 d-matching polynomial.
mu_d = Psi_{d+1}. Claim: [x^{4d-2k}] mu_d = (-1)^k c_k(d), c_k poly in d of degree k,
leading coeff 6^k/k!. PROVEN k=1,2 (deterministic: 4d verts, 6d edges, 3-regular);
E[#triangles]=4 (const) makes k=3 a provable cubic. c_3..c_5 from exact data.
Also: NO constant-in-d (C-finite) recurrence exists (unlike cycles)."""
import sympy as sp
x, d = sp.symbols('x d')
mu = {0: sp.Integer(1),
 1: x**4-6*x**2+3, 2: x**8-12*x**6+42*x**4-40*x**2+6,
 3: x**12-18*x**10+117*x**8-332*x**6+393*x**4-158*x**2+sp.Rational(97,9),
 4: x**16-24*x**14+228*x**12-1092*x**10+2781*x**8-3654*x**6+2230*x**4-495*x**2+sp.Rational(75,4),
 5: x**20-30*x**18+375*x**16-2536*x**14+10086*x**12-sp.Rational(120204,5)*x**10
      +sp.Rational(840006,25)*x**8-sp.Rational(646848,25)*x**6+sp.Rational(242478,25)*x**4
      -sp.Rational(34068,25)*x**2+sp.Rational(162,5)}
for k in range(6):
    pts=[(dd, sp.Poly(mu[dd],x).coeff_monomial(x**(4*dd-2*k) if 4*dd-2*k>0 else 1))
         for dd in range(6) if 4*dd-2*k>=0]
    poly=sp.expand(sp.interpolate([(sp.Integer(a),sp.Rational(b)) for a,b in pts], d))
    lead = sp.Rational(6**k, sp.factorial(k))
    status = "PROVEN(det.)" if k<=2 else ("provable(E[tri]=4)" if k==3 else "data-fit(need mu_6)")
    print(f"  c_{k}(d) = {(-1)**k*poly if k%2 else poly}  deg={sp.degree(poly,d)}  lead 6^{k}/{k}!={lead}  [{status}]")
