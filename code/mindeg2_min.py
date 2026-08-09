"""How small can a minimum-degree-two counterexample be?

The first one found has 92 vertices, against 41 for Hall's pendant-leaf version. This widens
the search over the pendant cycle length k and the two branch parameters, to see whether 92
is close to optimal or merely the first thing tried. Same diagnostic as elsewhere: the
scaling of the density of states at the root, flat in eta outside the spectrum.

Rule 8: instrumented, backgrounded, and capped at 120 vertices so the cavity cost stays
bounded.
"""
import sys, os, math, time, sympy as sp
sys.path.insert(0, 'code')
g = {}
exec(open('code/mindeg2.py').read().split("def main():")[0], g)
branch, whole_graph, mu_brute, dos_ladder, mindeg = (
    g['branch'], g['whole_graph'], g['mu_brute'], g['dos_ladder'], g['mindeg'])
x = sp.Symbol('x')
CKPT = 'private/mindeg2_min_ckpt.txt'

todo = [(k, p, q) for k in range(3, 9) for q in range(3, 10) for p in range(3, 10)]
best = []
t0 = time.time()
print(f"{len(todo)} (k,p,q) combinations, capped at 120 vertices", flush=True)
print(f"{'k':>3}{'p':>3}{'q':>3}{'n':>5}{'dmin':>5}{'root':>10}{'DOS/eta':>22}", flush=True)
for i, (k, p, q) in enumerate(todo):
    nn, ee = whole_graph(p, q, f'C{k}')
    if nn > 120:
        continue
    nb, eb = branch(q, f'C{k}')
    if len(eb) > 26:
        continue
    muH = sp.expand(mu_brute(nb, eb))
    muHv = sp.expand(mu_brute(nb - 1, [(a - 1, b - 1) for a, b in eb if 0 not in (a, b)]))
    last = sp.expand(x * muH - p * muHv)
    co = sp.Poly(last, x).all_coeffs()
    while co and co[-1] == 0:
        co.pop()
    rts = [sp.re(r) for r in sp.Poly(co, x).nroots(n=25, maxsteps=800)
           if abs(sp.im(r)) < 1e-14 and sp.re(r) > 1e-9]
    for r in rts:
        lad = dos_ladder(nn, ee, float(r), etas=(1e-5, 1e-7, 1e-9))
        if max(lad) < 50.0:
            best.append((nn, k, p, q, float(r)))
            print(f"{k:>3}{p:>3}{q:>3}{nn:>5}{mindeg(nn,ee):>5}{float(r):>10.5f}"
                  f"{str([f'{t:.2f}' for t in lad]):>22}", flush=True)
            break
    if (i + 1) % 20 == 0:
        el = time.time() - t0
        print(f"  ... {i+1}/{len(todo)}  {el:.0f}s  best so far "
              f"{min(b[0] for b in best) if best else '-'}", flush=True)
        with open(CKPT + '.tmp', 'w') as f:
            f.write(f"{i+1} best={sorted(best)[:5]}\n")
        os.replace(CKPT + '.tmp', CKPT)
print("\nsmallest minimum-degree-two counterexamples found:")
for nn, k, p, q, r in sorted(best)[:12]:
    print(f"  n={nn}  pendant C{k}, p={p}, q={q}, root={r:.6f}")
