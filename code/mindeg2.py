"""Is minimum degree at least two the repaired hypothesis?

Hall's counterexample needs its pendant leaves: over 36 parameter pairs the leafless variant
never produces a root in a gap (code/hall_family.py). This script asks whether that is an
accident of removing the leaf, or whether min degree 2 genuinely blocks the mechanism.

WHY IT MIGHT. In Hall's construction the leaf at w_i does two things at once. It adds a term
to the cavity equation at w_i, which is what repairs the common spectral parameter, and it
contributes only TRANSIENT states to the decay matrix, so it costs nothing in the decay rate.
A degree-one vertex is exactly what buys both. Any gadget with min degree two contains a
cycle, so its states are recurrent and enter the Perron block, which should push the decay
rate up. The test is whether that cost is fatal.

THE TEST. Keep Hall's branch structure, which is what makes the matching polynomial
computable, and replace the pendant leaf at w_i by a pendant cycle C_k attached at w_i. All
new vertices then have degree two, as do the middle vertices of K_{2,q}, so the whole graph
has min degree two. Controls: the leaf itself, and two leaves, both of which have a degree-one
vertex and should reproduce the counterexample.

Because the branches meet only at the central vertex, the deletion recurrence at c gives

    mu_G = mu_H^{p-1} ( x mu_H - p mu_{H-v} ),

and each branch is small enough to brute force exactly. Every positive root of the last
factor is then tested against spec(T) by the scaling of the density of states: outside the
spectrum the cavity Green function is real and DOS(x + i eta) vanishes linearly in eta, so
DOS/eta is flat; inside, it blows up. This avoids the cavity mass gate, which these
flat-band graphs fail.

Rule 8: this is a Python job of roughly ten minutes, over the five-minute threshold at which
Rust is preferred. It is instrumented with progress, ETA and atomic checkpoints, and the
Rust port is the follow-up if the search has to be widened.
"""

import sys
import os
import math
import time
import sympy as sp
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode

CKPT = quickmode.ckpt('private/mindeg2_ckpt.txt')
x = sp.Symbol('x')


def branch(q, gadget):
    """One branch H rooted at v. Vertices 0=v, 1=w, 2..q+1 = u_j, then the gadget.
    Returns (nverts, edges, mindeg_of_gadget_vertices)."""
    e = [(0, 2 + j) for j in range(q)] + [(2 + j, 1) for j in range(q)]
    n = 2 + q
    if gadget == 'leaf':
        e.append((1, n)); n += 1
    elif gadget == '2leaves':
        e.append((1, n)); e.append((1, n + 1)); n += 2
    elif gadget.startswith('C'):
        k = int(gadget[1:])
        cyc = list(range(n, n + k - 1))
        n += k - 1
        prev = 1
        for a in cyc:
            e.append((prev, a)); prev = a
        e.append((prev, 1))
    else:
        raise ValueError(gadget)
    return n, e


def mu_brute(nv, elist):
    """Matching polynomial by enumeration over edge subsets, exact integers."""
    m = len(elist)
    cnt = {}
    for bits in range(1 << m):
        used, ok, k = set(), True, 0
        b = bits
        t = 0
        while b:
            if b & 1:
                a, c = elist[t]
                if a in used or c in used:
                    ok = False
                    break
                used.add(a); used.add(c); k += 1
            b >>= 1; t += 1
        if ok:
            cnt[k] = cnt.get(k, 0) + 1
    return sum((-1) ** k * c * x ** (nv - 2 * k) for k, c in cnt.items())


def whole_graph(p, q, gadget):
    """The assembled graph G: central c=0 joined to the root of each of p branches."""
    nb, eb = branch(q, gadget)
    edges = []
    n = 1
    for _ in range(p):
        off = n
        for (a, b) in eb:
            edges.append((a + off, b + off))
        edges.append((0, off))          # c -- v_i
        n += nb
    return n, edges


def mindeg(n, edges):
    d = [0] * n
    for a, b in edges:
        d[a] += 1; d[b] += 1
    return min(d)


def dos_ladder(n, edges, root, etas=(1e-5, 1e-7, 1e-9)):
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    de = []
    for a, b in edges:
        de.append((a, b)); de.append((b, a))
    idx = {e: k for k, e in enumerate(de)}
    foll = [[idx[(b, c)] for c in adj[b] if c != a] for (a, b) in de]
    h = [complex(0.0, -0.1)] * len(de)
    out = []
    for eta in etas:
        z = complex(root, eta)
        for _ in range(30000):
            diff = 0.0
            new = [0j] * len(de)
            for k in range(len(de)):
                ssum = z
                for f in foll[k]:
                    ssum -= h[f]
                val = 1.0 / ssum
                diff = max(diff, abs(val - h[k]))
                new[k] = val
            h = new
            if diff < 1e-14:
                break
        acc = 0.0
        for u in range(n):
            ssum = z
            for b in adj[u]:
                ssum -= h[idx[(u, b)]]
            acc += (1.0 / ssum).imag
        out.append(-acc / (math.pi * n) / eta)
    return out


def main():
    gadgets = ['leaf', '2leaves', 'C3', 'C4', 'C5']
    todo = [(g, p, q) for g in gadgets for q in range(3, 8) for p in range(3, 8)]
    print(f"{len(todo)} (gadget, p, q) combinations", flush=True)
    done = 0
    if os.path.exists(CKPT):
        done = int(open(CKPT).readline().split()[0])
        print(f"resuming after {done}", flush=True)

    t0 = time.time()
    tally = {}
    print(f"\n{'gadget':>8}{'p':>3}{'q':>3}{'n':>5}{'dmin':>5}{'root':>10}"
          f"{'DOS/eta':>28}{'verdict':>10}", flush=True)
    for i, (g, p, q) in enumerate(todo):
        if i < done:
            continue
        nb, eb = branch(q, g)
        muH = sp.expand(mu_brute(nb, eb))
        eb_v = [(a - 1, b - 1) for a, b in eb if 0 not in (a, b)]
        muHv = sp.expand(mu_brute(nb - 1, eb_v))
        last = sp.expand(x * muH - p * muHv)
        n, edges = whole_graph(p, q, g)
        dm = mindeg(n, edges)
        if n > 100:
            continue
        # strip the x^k factor: its high multiplicity defeats the root finder
        co = sp.Poly(last, x).all_coeffs()
        while co and co[-1] == 0:
            co.pop()
        red = sp.Poly(co, x)
        roots = [r for r in red.nroots(n=20, maxsteps=400)
                 if abs(sp.im(r)) < 1e-12 and sp.re(r) > 1e-9]
        tally.setdefault(g, [0, 0])
        for r in roots:
            rv = float(sp.re(r))
            lad = dos_ladder(n, edges, rv)
            flat = max(lad) < 50.0
            tally[g][1] += 1
            if flat:
                tally[g][0] += 1
            if flat or roots.index(r) == 0:
                print(f"{g:>8}{p:>3}{q:>3}{n:>5}{dm:>5}{rv:>10.5f}"
                      f"{str([f'{t:.2f}' for t in lad]):>28}"
                      f"{('GAP' if flat else 'in spec'):>10}", flush=True)
        el = time.time() - t0
        rate = (i + 1 - done) / max(el, 1e-9)
        if (i + 1) % 10 == 0:
            print(f"  ... {i+1}/{len(todo)}  {el:.0f}s  "
                  f"ETA {(len(todo)-i-1)/rate/60:.1f}min", flush=True)
            tmp = CKPT + '.tmp'
            with open(tmp, 'w') as f:
                f.write(f"{i+1} {tally}\n")
            os.replace(tmp, CKPT)

    print("\nroots landing in a gap of spec(T), by gadget:")
    for g in gadgets:
        if g in tally:
            hit, tot = tally[g]
            dmin = 1 if g in ('leaf', '2leaves') else 2
            print(f"  {g:>8} (min degree {dmin}): {hit} of {tot} roots in a gap")
    print("\nThe leaf rows are the control and should reproduce the counterexample.")
    print("A gap row for C3, C4 or C5 would be a min-degree-two counterexample and would")
    print("refute the repaired hypothesis outright.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
