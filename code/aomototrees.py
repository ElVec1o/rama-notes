"""Which (tree, eigenvalue) pairs can be Aomoto trees?

By Lemma 4.2 of Banks-Garza-Vargas-Mukherjee, an Aomoto tree for lambda carries a
lambda-eigenvector that is nonzero at EVERY vertex. So the possible Aomoto trees are exactly
the pairs (T, lambda) with a nowhere-vanishing lambda-eigenvector.

P82 (frozen before the data):
  (a) lambda_max always qualifies (Perron-Frobenius), and so does -lambda_max (trees are bipartite).
  (b) For the path P_n, lambda_k = 2cos(k pi/(n+1)) qualifies iff gcd(k, n+1) = 1, since the
      eigenvector entry sin(j k pi/(n+1)) vanishes iff (n+1) | jk for some 1 <= j <= n.
  (c) For the star K_{1,m}, only +-sqrt(m) qualify.
  (d) lambda = 0 qualifies only for K_1 (this is BGM Observation 4.2).
"""
import itertools, math
from math import gcd
import numpy as np

def trees(n):
    """all labelled trees on n vertices by Pruefer sequence, deduplicated up to isomorphism
    by sorted-eigenvalue + degree-sequence signature (adequate for n <= 10 exploration)"""
    seen = {}
    import numpy as _np
    if n == 1:
        yield _np.zeros((1,1)); return
    if n == 2:
        yield _np.array([[0.,1.],[1.,0.]]); return
    for seq in itertools.product(range(n), repeat=n-2):
        deg = [1]*n
        for x in seq: deg[x] += 1
        s = list(seq); d = deg[:]
        edges = []
        import heapq
        leaves = [i for i in range(n) if d[i]==1]; heapq.heapify(leaves)
        sq = list(s)
        for x in sq:
            leaf = heapq.heappop(leaves)
            edges.append((leaf,x)); d[leaf]-=1; d[x]-=1
            if d[x]==1: heapq.heappush(leaves,x)
        u,v = [i for i in range(n) if d[i]==1]
        edges.append((u,v))
        A = np.zeros((n,n))
        for a,b in edges: A[a,b]=A[b,a]=1
        ev = np.round(np.sort(np.linalg.eigvalsh(A)),9)
        key = (tuple(ev), tuple(sorted(deg)))
        if key in seen: continue
        seen[key] = True
        yield A

def nowhere_zero_eigs(A, tol=1e-7):
    """distinct eigenvalues admitting a nowhere-vanishing eigenvector.
    Coordinate i vanishes identically on the eigenspace iff row i of an orthonormal
    eigenspace basis is zero; if no coordinate does, a generic combination is nowhere zero."""
    n = A.shape[0]
    w, V = np.linalg.eigh(A)
    out = []
    i = 0
    while i < n:
        j = i
        while j+1 < n and abs(w[j+1]-w[i]) < 1e-8: j += 1
        B = V[:, i:j+1]
        rownorm = np.linalg.norm(B, axis=1)
        if rownorm.min() > tol: out.append(round(float(w[i]),9))
        i = j+1
    return out

print("P82. Possible Aomoto trees = (T, lambda) with a nowhere-vanishing lambda-eigenvector.\n")
print(f"{'n':>2}{'trees':>7}{'pairs (T,lam)':>15}{'distinct eigs':>15}{'qualify':>9}{'frac':>7}")
tot_q = tot_e = 0
for n in range(1, 10):
    tl = list(trees(n))
    ne = nq = 0
    for A in tl:
        w = np.round(np.linalg.eigvalsh(A), 9)
        dist = sorted(set(w))
        ne += len(dist)
        nq += len(nowhere_zero_eigs(A))
    tot_e += ne; tot_q += nq
    print(f"{n:>2}{len(tl):>7}{ne:>15}{ne:>15}{nq:>9}{nq/ne:>7.2f}")

print("\n(a) does lambda_max always qualify?")
bad = 0
for n in range(1, 10):
    for A in trees(n):
        q = nowhere_zero_eigs(A)
        lam = round(float(np.max(np.linalg.eigvalsh(A))),9)
        if not any(abs(x-lam)<1e-7 for x in q): bad += 1
print(f"  counterexamples to (a): {bad}")

print("\n(b) paths: which k qualify for P_n?")
for n in range(2, 12):
    A = np.zeros((n,n))
    for i in range(n-1): A[i,i+1]=A[i+1,i]=1
    q = nowhere_zero_eigs(A)
    ks = [k for k in range(1,n+1) if any(abs(2*math.cos(k*math.pi/(n+1))-x)<1e-7 for x in q)]
    pred = [k for k in range(1,n+1) if gcd(k,n+1)==1]
    print(f"  P_{n:<2} qualifying k = {ks}   gcd(k,{n+1})=1 predicts {pred}   {'MATCH' if ks==pred else 'MISMATCH'}")

print("\n(c) stars K_{1,m}: qualifying eigenvalues")
for m in range(1, 7):
    n = m+1
    A = np.zeros((n,n))
    for i in range(1,n): A[0,i]=A[i,0]=1
    print(f"  K_1,{m}: {nowhere_zero_eigs(A)}   (+-sqrt{m} = +-{math.sqrt(m):.6f})")
