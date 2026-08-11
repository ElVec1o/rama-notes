"""Pointing the ratio route at D3: what is the sign pattern without a bipartition?

The certificate that works for biregular graphs is SIGN-ALTERNATING, and the alternation came
from the bipartition: left-type ratios positive, right-type negative, with no exceptions over
twenty-two thousand path-tree vertices. D3 is not restricted to bipartite graphs, and the cavity
recursion is not either, but the sign structure has to come from somewhere else.

So: find small graphs with minimum degree three that are NOT bipartite and whose universal cover
has a gap, and look at the signs of the path-tree ratios at a gap point. If a pattern appears,
a certificate can be designed against it. If the signs are unstructured, the route needs a
different shape for D3 and that is worth knowing before any design work.

Wheels are the natural first family: a hub joined to a cycle gives minimum degree three, strong
degree contrast, and triangles, so they are non-bipartite by construction.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gapscale import setup, rho_at, gap_profile
import quickmode

def wheel(L):
    """hub 0 joined to a cycle on 1..L."""
    e=[(0,i+1) for i in range(L)]
    e+= [(i+1, (i+1)%L+1) for i in range(L)]
    return L+1, e

def bipartite(n, edges):
    adj={i:set() for i in range(n)}
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    col={0:0}; st=[0]
    while st:
        u=st.pop()
        for w in adj[u]:
            if w not in col: col[w]=1-col[u]; st.append(w)
            elif col[w]==col[u]: return False
    return True

def path_ratios(n, edges, root, lam, maxp=600000):
    adj={i:set() for i in range(n)}
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    out=[]; cnt=[0]
    def rec(v,vis,l):
        cnt[0]+=1
        if cnt[0]>maxp: raise RuntimeError
        kids=[u for u in adj[v] if u not in vis]
        cf=[rec(u,vis|{u},l+1) for u in kids]
        F=lam-sum(1.0/x for x in cf)
        if abs(F)<1e-13: raise ZeroDivisionError
        out.append((l,v,len(kids),F))
        return F
    rec(root,{root},1)
    return out

print("Non-bipartite, minimum degree three: do the path-tree ratios have a sign structure?\n")
print(f"{'graph':>10}{'n':>4}{'dmin':>6}{'bip':>6}{'#gaps':>7}{'widest gap':>18}")
cands=[]
for L in quickmode.few(range(4,11), 4):
    n,e = wheel(L)
    deg=[0]*n
    for a,b in e: deg[a]+=1; deg[b]+=1
    g = gap_profile(n,e)
    g = [t for t in g if t[1]-t[0] >= 0.05]
    w = max(g, key=lambda t:t[1]-t[0]) if g else None
    print(f"{f'W_{L}':>10}{n:>4}{min(deg):>6}{str(bipartite(n,e)):>6}{len(g):>7}"
          f"{(f'({w[0]:.3f},{w[1]:.3f})' if w else '-'):>18}")
    if w and min(deg)>=3 and not bipartite(n,e): cands.append((f"W_{L}",n,e,w))

print()
print("Re-rooted at a LOW-degree vertex, so high-degree endpoints occur many times.\n")
for name,n,e,(lo,hi) in cands[:(2 if quickmode.QUICK else 4)]:
    lam=0.5*(lo+hi)
    deg={i:0 for i in range(n)}
    for a,b in e: deg[a]+=1; deg[b]+=1
    root=min(range(n), key=lambda v: deg[v])
    try: rows=path_ratios(n,e,root,lam)
    except (RuntimeError, ZeroDivisionError) as ex:
        print(f"{name}: {type(ex).__name__}"); continue
    pos=[t for t in rows if t[3]>0]; neg=[t for t in rows if t[3]<0]
    print(f"=== {name}, n={n}, root deg {deg[root]}, lam={lam:.4f} in gap "
          f"({lo:.3f},{hi:.3f}), {len(rows)} path-tree vertices")
    print(f"    positive {len(pos)}  negative {len(neg)}  min|F| "
          f"{min(abs(t[3]) for t in rows):.4f}")
    for key,lab in ((lambda t: deg[t[1]], 'endpoint degree'),
                    (lambda t: t[0]%2, 'depth parity'),
                    (lambda t: t[2], 'child count')):
        d={}
        for t in rows: d.setdefault(key(t), []).append(t[3]>0)
        pure=all(all(v) or not any(v) for v in d.values())
        detail = "  ".join(f"{k}:{'+' if all(v) else ('-' if not any(v) else 'mixed')}"
                           for k,v in sorted(d.items()))
        print(f"    by {lab:>16}: {'DETERMINED' if pure else 'no':>10}   {detail}")
    if pos and neg:
        print(f"    positive range [{min(t[3] for t in pos):.4f}, {max(t[3] for t in pos):.4f}]"
              f"   negative range [{min(t[3] for t in neg):.4f}, {max(t[3] for t in neg):.4f}]")
