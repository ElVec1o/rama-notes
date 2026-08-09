"""Do wheels violate D3?  A falsification pass on a family D3 has not met.

D3 says minimum degree three suffices for Conjecture 10.  Every family it has been tested
against so far came from the two-hub engine with delta>=3 branches, or from 3-connected
constructions, and all were bipartite or near it.  Wheels are none of those: a hub joined to a
cycle has minimum degree three, is non-bipartite by construction, and has wide gaps in
spec(T), from (2.02, 2.08) at W_5 out to (2.02, 3.04) at W_10.

The path-tree ratios there come within 0.0764 of zero (code/d3ratio.py), which is close enough
to be worth checking directly rather than inferring.  This computes mu_G exactly and tests every
root against the measured gaps.
"""
import os, sys, math, functools
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gapscale import setup, rho_at, gap_profile
x=sp.Symbol('x')

def wheel(L):
    e=[(0,i+1) for i in range(L)]
    e+=[(i+1,(i+1)%L+1) for i in range(L)]
    return L+1,e

def mu(n,edges):
    adj={i:set() for i in range(n)}
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    sys.setrecursionlimit(200000)
    @functools.lru_cache(maxsize=None)
    def rec(vs):
        S=set(vs)
        if not S: return sp.Integer(1)
        v=min(S,key=lambda z: len(adj[z]&S)); S1=S-{v}
        t=x*rec(tuple(sorted(S1)))
        for u in adj[v]&S: t-=rec(tuple(sorted(S1-{u})))
        return sp.expand(t)
    return rec(tuple(range(n)))

print("Wheels: minimum degree three, non-bipartite, wide gaps.  Does any root land in one?\n")
print(f"{'W_L':>6}{'n':>4}{'gaps':>6}{'widest gap':>18}{'roots in gaps':>15}{'closest root':>26}")
viol=[]
for L in range(4,15):
    n,e=wheel(L)
    g=[t for t in gap_profile(n,e) if t[1]-t[0]>=0.02]
    if not g:
        print(f"{f'W_{L}':>6}{n:>4}{0:>6}{'-':>18}{'-':>15}{'-':>26}"); continue
    co=sp.Poly(mu(n,e),x).all_coeffs()
    while co and co[-1]==0: co.pop()
    rts=[float(sp.re(t)) for t in sp.Poly(co,x).nroots(n=25,maxsteps=4000)
         if abs(sp.im(t))<1e-12 and sp.re(t)>1e-9]
    B,M=setup(n,e)
    inside=[]
    for th in rts:
        for lo,hi in g:
            if lo<th<hi:
                r=rho_at(th,B,M)
                if r is not None and r<1: inside.append((th,lo,hi,r))
    w=max(g,key=lambda t:t[1]-t[0])
    # closest approach of any root to a gap interior
    best=None
    for th in rts:
        for lo,hi in g:
            d=min(abs(th-lo),abs(th-hi))
            if lo<th<hi: d=-d
            if best is None or d<best[0]: best=(d,th,lo,hi)
    print(f"{f'W_{L}':>6}{n:>4}{len(g):>6}{f'({w[0]:.3f},{w[1]:.3f})':>18}"
          f"{len(inside):>15}{f'{best[1]:.5f} at dist {best[0]:.5f}':>26}")
    if inside: viol.append((L,inside))
print()
if viol:
    print("D3 IS REFUTED by a wheel:")
    for L,ins in viol:
        for th,lo,hi,r in ins:
            print(f"  W_{L}: root {th:.6f} in gap ({lo:.3f},{hi:.3f}), decay rate {r:.6f}")
else:
    print("No wheel violates D3.  The family is non-bipartite with minimum degree three and")
    print("wide gaps, so it is a genuine new test rather than a variation of the old ones.")
