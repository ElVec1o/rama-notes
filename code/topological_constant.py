#!/usr/bin/env python3
"""D: pin c_k(0) = constant term of E[m_k(H_d)].  Compute E[m_4(H_d)] directly
by matching-counting over orbit-reduced covers, fit c_4, read c_4(0).
Test conjecture c_4(0) = #C4 + 6t on graphs with varied (t,#C4)."""
import itertools, math
from fractions import Fraction
from collections import Counter
import sympy as sp

def compose(a,b): return tuple(a[b[i]] for i in range(len(a)))
def inv(a):
    r=[0]*len(a)
    for i,v in enumerate(a): r[v]=i
    return tuple(r)

def analyze(name, V, EDGES, TREE):
    FREE=[e for e in EDGES if e not in TREE]
    nfree=len(FREE)
    deg=Counter()
    for u,v in EDGES: deg[u]+=1; deg[v]+=1
    Es=set(map(frozenset,EDGES))
    t=sum(1 for a,b,c in itertools.combinations(V,3)
          if {frozenset((a,b)),frozenset((b,c)),frozenset((a,c))}<=Es)
    c4c=0
    for q in itertools.combinations(V,4):
        for p in [(q[0],q[1],q[2],q[3]),(q[0],q[1],q[3],q[2]),(q[0],q[2],q[1],q[3])]:
            a,b,c,e=p
            if {frozenset((a,b)),frozenset((b,c)),frozenset((c,e)),frozenset((e,a))}<=Es: c4c+=1
    nV=len(V)
    # count m_k in a cover given free perms (tree perms = identity)
    def cover_edges(d, freeperms):
        # returns list of lifted edges as (vertex_id, vertex_id) with id = base*d+fiber
        pm={e:tuple(range(d)) for e in TREE}
        for e,s in zip(FREE,freeperms): pm[e]=s
        edges=[]
        for (u,v) in EDGES:
            s=pm[(u,v)]
            for c in range(d):
                edges.append((u*d+c, v*d+s[c]))
        return edges
    def count_mk(edges, k):
        cnt=0
        for comb in itertools.combinations(edges,k):
            verts=set()
            ok=True
            for a,b in comb:
                if a in verts or b in verts: ok=False; break
                verts.add(a); verts.add(b)
            if ok: cnt+=1
        return cnt
    def Emk(d,k):
        allp=list(itertools.permutations(range(d)))
        # orbit-BFS reduction over nfree-tuples under simultaneous conjugation
        seen=set(); reps=[]
        for tup in itertools.product(allp, repeat=nfree):
            if tup in seen: continue
            orbit=set()
            for g in allp:
                gi=inv(g); orbit.add(tuple(compose(g,compose(s,gi)) for s in tup))
            seen|=orbit; reps.append((tup,len(orbit)))
        tot=0; W=0
        for tup,w in reps:
            tot+=w*count_mk(cover_edges(d,tup),k); W+=w
        return Fraction(tot,W)
    dsym=sp.symbols('d')
    # c_4: need d=2..6 (5 pts, degree 4)
    pts=[(sp.Integer(d), sp.Rational(Emk(d,4))) for d in range(2,7)]
    c4=sp.expand(sp.interpolate(pts,dsym))
    # c_3 check: d=2..5
    pts3=[(sp.Integer(d), sp.Rational(Emk(d,3))) for d in range(2,6)]
    c3=sp.expand(sp.interpolate(pts3,dsym))
    print(f" {name}: t={t} #C4={c4c} | c_3(0)={c3.subs(dsym,0)}(=-t? {c3.subs(dsym,0)==-t}) "
          f"c_4(0)={c4.subs(dsym,0)}  #C4+6t={c4c+6*t}  match={c4.subs(dsym,0)==c4c+6*t}", flush=True)
    return t,c4c,int(c4.subs(dsym,0))

print("graph: t #C4 | c_3(0) c_4(0) vs #C4+6t")
# diamond K4-e
analyze("diamond", [0,1,2,3], [(0,1),(0,2),(0,3),(1,2),(1,3)], [(0,1),(0,2),(0,3)])
# bowtie: two triangles sharing vertex 0
analyze("bowtie ", [0,1,2,3,4], [(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)], [(0,1),(0,2),(0,3),(0,4)])
