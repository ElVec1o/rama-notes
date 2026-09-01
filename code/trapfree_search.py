"""D3 in the trap-free class: minimum degree three, maximum degree four.

RamaLean/DegreeBound.lean proves, from the Aomoto criterion of Banks-Garza-Vargas-Mukherjee, that
a theta-Aomoto subset with theta != 0 forces

    Delta > 2 (delta - 1).

So a graph with delta = 3 and Delta <= 4 has a universal cover with NO nonzero point spectrum.
That is exactly the escape hatch that invalidated every previous attack in this repository: each
time, the root we thought had escaped spec(T) was an eigenvalue of the cover carried by a
theta-Aomoto subset. In this class that cannot happen, so any nonzero root of mu_G lying outside
the BANDS of spec(T) is a genuine counterexample to Conjecture D3, with no Aomoto escape available.

WHERE A VIOLATION COULD LIVE. Heilmann-Lieb puts every root of mu_G in (-2 sqrt(Delta-1),
2 sqrt(Delta-1)) = (-3.4641, 3.4641) here. The universal cover of a graph with degrees in {3,4}
has a spectrum resembling that of the (3,4)-biregular tree, {0} u +-[sqrt3 - sqrt2, sqrt3 + sqrt2]
= {0} u +-[0.3178, 3.1463]. The top end is classical and safe. The window is therefore near the
origin: a root of mu_G strictly between 0 and the lower band edge. Every graph is put to the
resolution-free cavity classifier at its own smallest positive root, so no gap grid is involved.

FROZEN BEFORE THE DATA:
  P79. (a) In this class the Aomoto search finds no nonzero-theta Aomoto subset, confirming the
           Lean bound against the independent numerical test.
       (b) Some graph in the class has a positive root of mu_G below the lower band edge, that is
           the low window is non-empty.
       (c) Prediction: no such graph is found, and the reason is that delta = 3 with Delta <= 4
           forces enough local regularity that the smallest positive matching root stays inside the
           band. If (c) is wrong the find is a counterexample to D3 with the Aomoto escape closed
           off by a machine-checked theorem, which is the strongest possible form of the result.

FALSIFICATION. (a) failing means the Lean bound or its hypotheses are misapplied and nothing else
here means anything. (c) is falsified by a single graph whose smallest positive matching root the
classifier places outside spec.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'
import sys, time, random, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else 'code')
import numpy as np, networkx as nx, sympy as sp
from twocut import mu_of, x
from aomoto_obstruction import adjof, components, is_aomoto
from d3_counterexample import classify

BUDGET = float(os.environ.get('BUDGET', 1500))
ETAS = (1e-4, 1e-5, 1e-6)


def rand_class_graph(n, rng, frac4=0.4):
    """connected simple graph, every degree 3 or 4"""
    for _ in range(400):
        seq = [4 if rng.random() < frac4 else 3 for _ in range(n)]
        if sum(seq) % 2: seq[rng.randrange(n)] ^= 7  # flip 3<->4
        if sum(seq) % 2: continue
        try:
            G = nx.random_degree_sequence_graph(seq, seed=rng.randrange(10**9), tries=25)
        except Exception:
            continue
        if nx.is_connected(G) and min(dict(G.degree()).values()) >= 3 \
           and max(dict(G.degree()).values()) <= 4:
            return G
    return None


def mu_poly(G):
    n = G.number_of_nodes()
    adj = {i: set(G.neighbors(i)) for i in range(n)}
    return sp.Poly(sp.expand(mu_of(adj, set(range(n)))), x)


def smallest_pos_root(P):
    rs = [float(sp.re(z)) for z in P.nroots(n=25, maxsteps=5000)
          if abs(sp.im(z)) < 1e-12 and sp.re(z) > 1e-7]
    return min(rs) if rs else None


def has_nonzero_aomoto(G, thetas):
    n = G.number_of_nodes(); E = [tuple(e) for e in G.edges()]
    for th in thetas:
        for r in range(2, min(n, 9) + 1):
            for S in itertools.combinations(range(n), r):
                if is_aomoto(n, E, S, th)[0]:
                    return True, th, S
    return False, None, None


def main():
    rng = random.Random(20260902)
    print("P79 (frozen): minimum degree three, maximum degree four, where DegreeBound.lean")
    print("proves the cover has no nonzero point spectrum, so the Aomoto escape is closed.\n")

    print("(a) independent check of the Lean bound on small members of the class")
    checked = 0
    for n in (8, 10):
        for _ in range(6):
            G = rand_class_graph(n, rng)
            if G is None: continue
            P = mu_poly(G)
            th = [float(sp.re(z)) for z in P.nroots(n=20)
                  if abs(sp.im(z)) < 1e-12 and sp.re(z) > 1e-7]
            found, t, S = has_nonzero_aomoto(G, th)
            checked += 1
            if found:
                print(f"    n={n}: FOUND a nonzero Aomoto subset at {t:.6f}, S={S}")
                print("    the Lean bound is contradicted; stop and re-examine.")
                return 1
    print(f"    {checked} graphs, no nonzero-theta Aomoto subset found. Consistent with the bound.\n")

    print("(b),(c) the low window: smallest positive root of mu_G against spec(T)")
    print(f"{'n':>4}{'deg profile':>14}{'min pos root':>14}{'classifier':>16}", flush=True)
    t0 = time.time(); tested = 0; hits = []
    for n in (10, 12, 14, 16):
        while time.time() - t0 < BUDGET:
            G = rand_class_graph(n, rng)
            if G is None: break
            E = [tuple(e) for e in G.edges()]
            P = mu_poly(G)
            th = smallest_pos_root(P)
            if th is None: break
            kind = classify(n, E, th, etas=ETAS)[0]
            tested += 1
            d = sorted(dict(G.degree()).values())
            prof = f"{d.count(3)}x3+{d.count(4)}x4"
            if kind == 'outside spec':
                hits.append((n, E, th))
                print(f"{n:>4}{prof:>14}{th:>14.6f}{kind:>16}   <-- VIOLATION", flush=True)
            elif tested % 10 == 0:
                print(f"{n:>4}{prof:>14}{th:>14.6f}{kind:>16}", flush=True)
            if tested % 12 == 0: break
        if time.time() - t0 > BUDGET: break

    print(f"\n{tested} graphs in the class, {time.time()-t0:.0f}s")
    if hits:
        print("\n  P79(c) IS REFUTED, which is the outcome that matters. A graph of minimum degree")
        print("  three has a root of mu_G outside spec(T_G), and by DegreeBound.lean that root")
        print("  CANNOT be rescued by an Aomoto subset. Conjecture D3 is false.")
        json.dump([{'n': n, 'root': th, 'edges': [list(e) for e in E]} for n, E, th in hits],
                  open('data/trapfree_hits.json', 'w'), indent=1)
    else:
        print("\n  P79(c) HOLDS on this sample: no root escaped. D3 survives in the trap-free")
        print("  class, and it survives for a reason that is now isolated, since the Aomoto")
        print("  mechanism is provably unavailable here.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
