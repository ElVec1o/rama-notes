#!/usr/bin/env python3
"""Verify coefficient-stability formulas on the diamond (K4-e): a THIRD graph
with E,P,S,W,t all nonzero and DIFFERENT from cycles/K4.
KEY: the r-lift quotient Psi_r = mu_{r-1}, so mu_d = quotient of the (d+1)-lift.
Fast orbit-BFS conjugacy reduction; exact integer Bareiss; d<=5 (=> 6-lift)."""
import itertools, math
from fractions import Fraction
from collections import Counter
import sympy as sp

V=[0,1,2,3]; EDGES=[(0,1),(0,2),(0,3),(1,2),(1,3)]
TREE=[(0,1),(0,2),(0,3)]; FREE=[(1,2),(1,3)]

def compose(a,b): return tuple(a[b[i]] for i in range(len(a)))
def inv(a):
    r=[0]*len(a)
    for i,v in enumerate(a): r[v]=i
    return tuple(r)
def lift_matrix(r, perms, x0):
    n=4*r; M=[[0]*n for _ in range(n)]
    for i in range(n): M[i][i]=x0
    for (u,v) in EDGES:
        s=perms[(u,v)]
        for c in range(r):
            dd=s[c]; M[u*r+c][v*r+dd]-=1; M[v*r+dd][u*r+c]-=1
    return M
def det_bareiss(M):
    n=len(M); sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            piv=next((i for i in range(k+1,n) if M[i][k]!=0),None)
            if piv is None: return 0
            M[k],M[piv]=M[piv],M[k]; sign=-sign
        akk=M[k][k]
        for i in range(k+1,n):
            aik=M[i][k]
            for j in range(k+1,n): M[i][j]=(M[i][j]*akk-aik*M[k][j])//prev
        prev=akk
    return sign*M[n-1][n-1]
def interp(points):
    xs=[Fraction(x) for x,_ in points]; ys=[Fraction(y) for _,y in points]
    n=len(xs); dd=ys[:]
    for j in range(1,n):
        for i in range(n-1,j-1,-1): dd[i]=(dd[i]-dd[i-1])/(xs[i]-xs[i-j])
    coeffs=[Fraction(0)]*n; basis=[Fraction(1)]
    for k in range(n):
        for idx,c in enumerate(basis): coeffs[idx]+=dd[k]*c
        nb=[Fraction(0)]*(len(basis)+1)
        for idx,c in enumerate(basis): nb[idx+1]+=c; nb[idx]-=xs[k]*c
        basis=nb
    return coeffs
def poly_div(num,den):
    num=num[:]; dn=len(den)-1
    while len(den)>1 and den[-1]==0: den=den[:-1]; dn-=1
    q=[Fraction(0)]*(len(num)-dn)
    for k in range(len(num)-dn-1,-1,-1):
        c=num[k+dn]/den[dn]; q[k]=c
        for j in range(dn+1): num[k+j]-=c*den[j]
    return q
def base_charpoly():
    x=sp.symbols('x'); A=sp.zeros(4)
    for u,v in EDGES: A[u,v]=1; A[v,u]=1
    p=sp.Poly(sp.expand((x*sp.eye(4)-A).det()),x)
    return [Fraction(int(c)) for c in p.all_coeffs()[::-1]]
CHI=base_charpoly()

def quotient_r(r):
    """Psi_r = mu_{r-1}: expected char poly of r-lift / chi_base."""
    ident=tuple(range(r)); perms_id={e:ident for e in TREE}
    allp=list(itertools.permutations(range(r)))
    # orbit-BFS reduction of (s12,s13) under simultaneous conjugation
    seen=set(); reps=[]
    for a in allp:
        for b in allp:
            if (a,b) in seen: continue
            orbit=set()
            for g in allp:
                gi=inv(g); orbit.add((compose(g,compose(a,gi)),compose(g,compose(b,gi))))
            seen|=orbit; reps.append(((a,b),len(orbit)))
    deg=4*r; pts=list(range(-(deg//2),deg//2+1)); sums={x0:0 for x0 in pts}
    for (a,b),w in reps:
        perms=dict(perms_id); perms[(1,2)]=a; perms[(1,3)]=b
        for x0 in pts: sums[x0]+=w*det_bareiss(lift_matrix(r,perms,x0))
    coeffs=interp([(x,sums[x]) for x in pts])
    fact=Fraction(math.factorial(r)**2)
    phi=[c/fact for c in coeffs]; quo=poly_div(phi,CHI)
    while len(quo)>1 and quo[-1]==0: quo=quo[:-1]
    return quo

MU={}
for r in range(1,7):          # r=1..6  ->  mu_{0}..mu_{5}
    MU[r-1]=quotient_r(r)
    print(f"  mu_{r-1} = quotient of {r}-lift (deg {len(MU[r-1])-1})", flush=True)

deg=Counter()
for u,v in EDGES: deg[u]+=1; deg[v]+=1
E=len(EDGES); P=sum(math.comb(deg[v],2) for v in V); S=sum(math.comb(deg[v],3) for v in V)
W=sum((deg[u]-1)*(deg[v]-1) for u,v in EDGES)
Es=set(map(frozenset,EDGES))
t=sum(1 for a,b,c in itertools.combinations(V,3) if {frozenset((a,b)),frozenset((b,c)),frozenset((a,c))}<=Es)
c4c=0
for q in itertools.combinations(V,4):
    for p in [(q[0],q[1],q[2],q[3]),(q[0],q[1],q[3],q[2]),(q[0],q[2],q[1],q[3])]:
        a,b,c,e=p
        if {frozenset((a,b)),frozenset((b,c)),frozenset((c,e)),frozenset((e,a))}<=Es: c4c+=1
print(f"\ndiamond: E={E} P={P} S={S} W={W} t={t} #C4={c4c}")
dd=sp.symbols('d')
def ck(k):
    pts=[]
    for d in range(0,6):
        dx=4*d-2*k
        if dx<0 or d not in MU: continue
        mu=MU[d]; c=mu[dx] if dx<len(mu) else Fraction(0)
        pts.append((sp.Integer(d),sp.Rational(c.numerator,c.denominator)))
    return sp.expand((-1)**k*sp.interpolate(pts,dd))
c1,c2,c3,c4=ck(1),ck(2),ck(3),ck(4)
print(f" c_1={c1}  ==E*d? {sp.expand(c1-E*dd)==0}")
print(f" c_2={c2}  ==C(Ed,2)-Pd? {sp.expand(c2-(E*dd*(E*dd-1)/2-P*dd))==0}")
c3f=sp.expand(E*dd*(E*dd-1)*(E*dd-2)/6-P*dd*(E*dd-2)+(W+2*S)*dd-t)
print(f" c_3={c3}")
print(f"     PROVEN formula match? {sp.expand(c3-c3f)==0}")
print(f" c_4(0)={c4.subs(dd,0)}  conj #C4+6t={c4c+6*t}  match={c4.subs(dd,0)==c4c+6*t}   lead={c4.coeff(dd,4)} (pred {sp.Rational(E**4,24)})")
