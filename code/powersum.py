"""The power-sum certificate for the biregular case.

By Heilmann-Lieb the matching polynomial is real-rooted, so writing mu_G = x^{n-2nu} g(x^2)
the polynomial g has all roots real and POSITIVE. For positive reals the l^m norm of the
reciprocals decreases to the l^infinity norm, so with P_m = sum y_i^{-m},

    min_i y_i  >=  P_m^{-1/m},

sharpening as m grows and exact in the limit. m = 1 is the harmonic bound m_nu / m_(nu-1);
the Cauchy estimate of code/rootsep.py is cruder still and throws real-rootedness away.

The P_m are computed exactly from the matching numbers by Newton's identities on the reversed
polynomial, whose roots are the 1/y_i, so the whole computation is rational.

This tabulates the bound at m = 1, 2, 4, 8 against the true smallest root and against
tau^2 = (sqrt(a-1) - sqrt(b-1))^2. Whenever the bound reaches tau^2 the conjecture is PROVED
for that graph, unconditionally and with no appeal to Angel-Friedman-Hoory; the implication is
machine-checked as PowerSumCertificate.roots_ge_of_powersum.
"""
import sys, math, random
import numpy as np, sympy as sp
sys.path.insert(0,'code')
g={}
src=open('code/rootsep.py').read()
exec(src.split("# ------------------------------------------------------------------ the two mechanisms")[0], g)
even_part = g['even_part']
exec(src.split("# ------------------------------------------------------------------ biregular")[1].split("def check_biregular")[0], g)
counts, random_biregular = g['counts'], g['random_biregular']
x=sp.Symbol('x')

def power_sums(coeffs_asc, M):
    """coeffs of Gt ascending: c_0..c_nu. Roots y_i. Return p_m = sum (1/y_i)^m, m=1..M,
    via Newton's identities on the REVERSED polynomial (whose roots are 1/y_i)."""
    c=[sp.Rational(t) for t in coeffs_asc]
    nu=len(c)-1
    # reversed poly R(z) = sum_j c_{nu-j} z^j ; leading coeff a_nu = c_0
    a=[c[nu-j] for j in range(nu+1)]     # a[j] = coeff of z^j in R
    lead=a[nu]
    e=[sp.Rational(0)]*(nu+1)            # e[k] = elementary symm of the 1/y_i
    for k in range(nu+1):
        e[k]=(-1)**k*a[nu-k]/lead
    p=[sp.Rational(0)]*(M+1)
    for m in range(1,M+1):
        s=sp.Rational(0)
        for i in range(1,m):
            s+= (-1)**(i-1)*e[i]*p[m-i] if i<=nu else 0
        term=(-1)**(m-1)*m*e[m] if m<=nu else sp.Rational(0)
        p[m]=s+term
    return p

print(f"{'a':>3}{'b':>3}{'k':>3}{'n':>4}{'tau^2':>9}"
      f"{'m=1':>9}{'m=2':>9}{'m=4':>9}{'m=8':>9}{'true^2':>9}{'best m proves?':>16}")
rng=random.Random(11); proved=0; tot=0
for (a,b) in [(3,4),(3,5),(3,6)]:
    tau2=(math.sqrt(a-1)-math.sqrt(b-1))**2
    for k in (1,2,3,4):
        gg=random_biregular(a,b,k,rng)
        if gg is None: continue
        nA,nB,adjA=gg; n=nA+nB
        if nB>12: continue
        m_=counts(nA,nB,adjA)
        poly=sum((-1)**kk*m_[kk]*x**(n-2*kk) for kk in range(len(m_)))
        Gt,d=even_part(sp.expand(poly))
        asc=[t for t in Gt.all_coeffs()[::-1]]
        if len(asc)<2 or asc[0]==0: continue
        P=power_sums(asc, 8)
        bnds={}
        for mm in (1,2,4,8):
            v=abs(float(P[mm]))
            bnds[mm]= v**(-1.0/mm) if v>0 else float('inf')
        cop=sp.Poly(poly,x).all_coeffs()
        while cop and cop[-1]==0: cop.pop()
        rts=[abs(complex(r)) for r in sp.Poly(cop,x).nroots(n=20,maxsteps=600)
             if abs(sp.im(r))<1e-9 and abs(sp.re(r))>1e-9]
        true2=min(rts)**2 if rts else float('nan')
        best=max(bnds.values())
        ok= best>=tau2
        proved+=1 if ok else 0; tot+=1
        print(f"{a:>3}{b:>3}{k:>3}{n:>4}{tau2:>9.5f}"
              f"{bnds[1]:>9.5f}{bnds[2]:>9.5f}{bnds[4]:>9.5f}{bnds[8]:>9.5f}"
              f"{true2:>9.5f}{('YES' if ok else 'no'):>16}")
print(f"\nproves SFM for {proved} of {tot} with the best m tried")
