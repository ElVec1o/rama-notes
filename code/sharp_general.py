"""Delta > (delta-2) kappa + 2 is attained for EVERY delta >= 3 and every kappa >= 2.

Write W = (delta-2) kappa + 2, so the bound reads Delta >= W+1. Take c copies of a theta-critical
tree B of order kappa, and b boundary vertices, and give each branch vertex v exactly
delta - deg_B(v) boundary neighbours. The number of cross edges is

    sum_v (delta - deg_B(v)) = c(delta*kappa - 2(kappa-1)) = W c,

and the chain e <= Delta b with b <= c-1 forces, at Delta = W+1, that c >= W+1. Taking c = W+1 and
b = W = c-1 makes Wc = W(W+1) = Delta b exactly, so every boundary vertex has degree exactly W+1.
Branch vertices have degree delta, and W+1 >= delta, so delta(G) = delta and Delta(G) = W+1.

The branch vertices then form a theta-Aomoto subset: G[S] is c disjoint copies of B, a forest whose
components all have theta as an eigenvalue, and |boundary| = c-1 < c. By the criterion of Banks,
Garza-Vargas and Mukherjee, theta is an eigenvalue of the universal cover. So the bound is attained,
and by the same chain both Delta and n = kappa*c + b are the least possible.

Taking B = P_kappa with theta = 2 cos(pi/(kappa+1)), which is theta-critical since gcd(1,kappa+1)=1,
gives an instance for every kappa >= 2.
"""

import sys
sys.path.insert(0, '.')


def build(delta, kappa):
    W = (delta - 2) * kappa + 2
    c, b = W + 1, W
    edges = []
    nxt = b
    branches = []
    for _ in range(c):
        vs = list(range(nxt, nxt + kappa)); nxt += kappa
        for i in range(kappa - 1):
            edges.append((vs[i], vs[i + 1]))
        branches.append(vs)
    # round robin over boundary slots; each branch vertex takes delta - deg_B(v) distinct ones
    slot = 0
    for vs in branches:
        for j, v in enumerate(vs):
            internal = 2 if 0 < j < kappa - 1 else (1 if kappa > 1 else 0)
            need = delta - internal
            chosen = []
            while len(chosen) < need:
                cand = slot % b
                slot += 1
                if cand not in chosen:
                    chosen.append(cand)
            for h in chosen:
                edges.append((v, h))
    return nxt, sorted((min(a, z), max(a, z)) for a, z in edges), branches, b, c


print(f"{'delta':>6}{'kappa':>6}{'bound':>7}{'Delta':>7}{'delta(G)':>9}{'n':>5}"
      f"{'c':>4}{'b':>4}{'cc>|bd|':>9}{'simple':>8}{'sharp':>7}")
allok = True
for delta in (3, 4, 5, 6):
    for kappa in (2, 3, 4, 5):
        n, e, branches, b, c = build(delta, kappa)
        simple = len(set(e)) == len(e)
        deg = [0] * n
        for a, z in e:
            deg[a] += 1; deg[z] += 1
        S = {v for vs in branches for v in vs}
        bd = {a if a not in S else z for a, z in e if (a in S) != (z in S)}
        bound = (delta - 2) * kappa + 2
        ok = simple and min(deg) == delta and max(deg) == bound + 1 and c > len(bd)
        allok &= ok
        print(f"{delta:>6}{kappa:>6}{bound:>7}{max(deg):>7}{min(deg):>9}{n:>5}"
              f"{c:>4}{b:>4}{str(c > len(bd)):>9}{str(simple):>8}{str(ok):>7}")
print("\nALL ATTAIN THE BOUND" if allok else "\nSOME CASE FAILS")
