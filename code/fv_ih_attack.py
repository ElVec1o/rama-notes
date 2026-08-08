import numpy as np, sys
import fv_setup as S
from fv_recursion import F_poly, as_dense, compress, ortho_complement
from fv_induction import Adj
from fv_attack import compress_random
from fv_limits import weighted_Kp_family
try:
    from scipy.optimize import minimize; HS=True
except Exception: HS=False

def ih_gap(As,p,a,c,v,mults=(1.0,1.02,1.1,1.4,2.0)):
    """max over x of (x - D/t) - F_A/F_A'.  >0 means the IH FAILS."""
    e=v/np.linalg.norm(v)
    t=np.sqrt(max(a-c,1e-9)); x0=t+(a-c)/t
    Q=ortho_complement([e],p); Ac=compress(As,Q)
    FA=as_dense(F_poly(As,p),p); FAc=as_dense(F_poly(Ac,p-1),p-1)
    D=float(e@Adj(As)@e)
    out=-np.inf
    for m in mults:
        x=m*x0; den=np.polyval(FAc,x)
        if abs(den)<1e-13: continue
        out=max(out,(x-D/t)-np.polyval(FA,x)/den)
    return out

def worst_ih(As,p,a,c,ntr=60,seed=0):
    rng=np.random.default_rng(seed); best=-np.inf; bv=None
    for i in range(ntr):
        v=np.eye(p)[0] if i==0 else rng.standard_normal(p)
        g=ih_gap(As,p,a,c,v)
        if g>best: best,bv=g,v
    if HS:
        r=minimize(lambda v:-ih_gap(As,p,a,c,v),bv,method='Nelder-Mead',
                   options=dict(maxiter=1200,xatol=1e-9,fatol=1e-13))
        best=max(best,-r.fun)
    return best

rows=[]
Ps,p,a=S.K33(); K33=[P for P in Ps]
Ps,p8,a8=S.cube(); CUBE=[P for P in Ps]
fams=[('K_{3,3}',K33,6,3,0),('cube',CUBE,8,3,0)]
for lvl in (1,2,3):
    AA,pp=compress_random(K33,6,lvl,7); fams.append((f'K33 c{lvl}',AA,pp,3,lvl))
for sd in (1,2,3):
    Ps,pp,aa,_,_,_=S.family_random(6,3,seed=200+sd); AA=[P for P in Ps]
    fams.append((f'r6/3.{sd}',AA,pp,aa,0))
    A1,p1=compress_random(AA,pp,1,sd); fams.append((f'r6/3.{sd} c1',A1,p1,aa,1))
    A2,p2=compress_random(AA,pp,2,sd); fams.append((f'r6/3.{sd} c2',A2,p2,aa,2))
print('%-12s %3s %3s %3s | %12s %12s'%('family','p','a','lvl','IHgap c=1','IHgap c=0'))
for nm,AA,pp,aa,lvl in fams:
    if pp<3: continue
    g1=worst_ih(AA,pp,aa,1.0,seed=3); g0=worst_ih(AA,pp,aa,0.0,seed=3)
    print('%-12s %3d %3d %3d | %12.4e %12.4e'%(nm,pp,aa,lvl,g1,g0)); sys.stdout.flush()

# weighted K_p (q = C(p,2) blocks, too many for F_poly): use the exact Hermite
# form  F_A(x) = lam^{p/2} He_p(x/sqrt(lam)),  lam = a/(p-1),  Adj = a I.
def He_pair(p,u):
    a0,a1=1.0,u
    for k in range(2,p+1): a0,a1=a1,u*a1-(k-1)*a0
    return a1,a0
print()
print('weighted K_p in C(a): largest root vs the two candidate bands')
print('%5s %3s %9s | %9s %9s %9s'%('p','a','lam','maxroot','2sq(a-1)','2sq(a)'))
for a in (3,5):
    for p in (6,20,60,200,2000):
        lam=a/(p-1); off=np.sqrt(np.arange(1,p)*lam)
        mr=np.linalg.eigvalsh(np.diag(off,1)+np.diag(off,-1)).max()
        flag='  <-- EXCEEDS 2sqrt(a-1)' if mr>2*np.sqrt(a-1) else ''
        print('%5d %3d %9.4f | %9.4f %9.4f %9.4f%s'%(p,a,lam,mr,2*np.sqrt(a-1),2*np.sqrt(a),flag))
