#!/usr/bin/env python3
"""Explicit general low-order coefficients of mu_{d,G} for ANY graph G.
Convention: [x^{|V|d-2k}] mu_{d,G} = (-1)^k c_k(d).  Claims (deterministic for k<=2):
   c_1(d) = |E| d
   c_2(d) = C(|E|d,2) - P d,  P = #2-paths = sum_v C(deg v,2)
   c_3(d): E[#triangles(H_d)] = t := #triangles(G) (const in d); constant term of c_3 = -t.
Verified on cycles C_3..C_6 (exact U_d(T_n(x/2))) and K4 (exact data)."""
import sympy as sp
from collections import Counter
x, d = sp.symbols('x d')

def ginfo(V,E):
    deg=Counter()
    for u,v in E: deg[u]+=1; deg[v]+=1
    P=sum(sp.binomial(deg[v],2) for v in V)
    Es=set(map(frozenset,E)); t=0; Vl=list(V)
    for i in range(len(Vl)):
        for j in range(i+1,len(Vl)):
            for k in range(j+1,len(Vl)):
                a,b,c=Vl[i],Vl[j],Vl[k]
                if {frozenset((a,b)),frozenset((b,c)),frozenset((a,c))}<=Es: t+=1
    return len(E),int(P),t

def c_k(mu_fn, per_d, k, dmax):
    pts=[]
    for dd in range(dmax+1):
        deg=per_d*dd-2*k
        if deg<0: continue
        p=sp.Poly(mu_fn(dd),x); c=p.coeff_monomial(x**deg) if deg>0 else p.coeff_monomial(1)
        pts.append((dd,sp.Rational(c)))
    raw=sp.expand(sp.interpolate([(sp.Integer(a),b) for a,b in pts],d))
    return sp.expand((-1)**k*raw)               # (-1)^k * [x^..] = c_k

def check(name,V,E,mu_fn,per_d,dmax):
    nE,P,t=ginfo(V,E)
    c1=c_k(mu_fn,per_d,1,dmax); c2=c_k(mu_fn,per_d,2,dmax); c3=c_k(mu_fn,per_d,3,dmax)
    c2f=sp.expand(sp.Rational(1,2)*(nE*d)*(nE*d-1)-P*d)
    print(f" {name}: |E|={nE} P={P} tri={t}")
    print(f"   c_1={c1}  (=|E|d? {sp.expand(c1-nE*d)==0})")
    print(f"   c_2={c2}  ==C(|E|d,2)-Pd? {sp.expand(c2-c2f)==0}")
    print(f"   c_3={c3}  const={c3.subs(d,0)}  ==-tri? {c3.subs(d,0)==-t}")

def mu_cycle(n): return lambda dd: sp.expand(sp.chebyshevu(dd,sp.chebyshevt(n,x/2)))
print("=== cycles ===")
for n in (3,4,5,6):
    E=[(i,(i+1)%n) for i in range(n)]
    check(f"C_{n}",list(range(n)),E,mu_cycle(n),n,8)
print("=== K4 ===")
muK4={0:sp.Integer(1),1:x**4-6*x**2+3,2:x**8-12*x**6+42*x**4-40*x**2+6,
 3:x**12-18*x**10+117*x**8-332*x**6+393*x**4-158*x**2+sp.Rational(97,9),
 4:x**16-24*x**14+228*x**12-1092*x**10+2781*x**8-3654*x**6+2230*x**4-495*x**2+sp.Rational(75,4),
 5:x**20-30*x**18+375*x**16-2536*x**14+10086*x**12-sp.Rational(120204,5)*x**10
   +sp.Rational(840006,25)*x**8-sp.Rational(646848,25)*x**6+sp.Rational(242478,25)*x**4
   -sp.Rational(34068,25)*x**2+sp.Rational(162,5)}
check("K4",[0,1,2,3],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],lambda dd:muK4[dd],4,5)
