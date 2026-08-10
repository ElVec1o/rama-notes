"""Push the adversarial search against Ravichandran-Leake harder, before writing to Xu.

code/adversarial.py reaches 0.887 of the conjectured edge at (a,b) = (3,2), p = 6, q = 9, with
no violation, and 0.739 and 0.726 at (4,3) and (5,4). Since our F_A on unweighted projection
families IS the MSS mixed characteristic polynomial (verified to 1e-13 in code/rl_conj.py), that
search is a direct adversarial test of Xu's Remark 1.6, hence of his Conjecture 1.4, hence of
Ravichandran-Leake Conjecture 1.

Whether the letter to Xu reports evidence FOR his conjecture or a COUNTEREXAMPLE to it turns on
this run, so it is worth doing properly rather than reporting the first number to hand. Three
things are varied that the earlier run held fixed:

  DIMENSION.  (3,2) at p = 6, 8, 10 rather than p = 6 alone. The margin at p = 6 could be a
  small-instance artefact; if the approach ratio climbs with p, the conjecture is closer to
  sharp than the single number suggests, and that is worth telling him either way.

  EFFORT.  More restarts and more steps per restart, with a slower perturbation decay, since
  the earlier run's default schedule was tuned for a sweep across ten parameter sets rather
  than for one hard instance.

  CLASS.  Projections, PSD rank-b, and random biregular graphs, as before, because the earlier
  run found graphs marginally more extremal than general projections at (3,2) and it would be
  careless to drop the class that was winning.

FROZEN BEFORE THE DATA:
  P19. No family reaches the edge: the margin to (sqrt(a-1)+sqrt(b-1))^2 stays strictly
       positive at every (p,q) tested, so the run reports evidence for Conjecture 1.4 rather
       than against it.

A violation would refute Ravichandran-Leake Conjecture 1, which is a statement about their
subject and not ours, so any apparent violation is re-checked against the exact-arithmetic
mixed characteristic polynomial before it is believed.
"""

import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '2'

import sys
import time
import math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mixed_char_poly import mixed_char_poly, band
from tff import build_tff, build_psd_family, restore, random_biregular, graph_to_projections
from adversarial import hill_climb

BUDGET_S = float(__import__('sys').argv[1]) if len(__import__('sys').argv) > 1 else 2100.0


def approach(rmax, a, b):
    """Fraction of the way from the band centre to its upper edge."""
    s, t = math.sqrt(a - 1.0), math.sqrt(b - 1.0)
    centre, half = s * s + t * t, 2.0 * s * t
    return (rmax - centre) / half


def main():
    t0 = time.time()
    print("P19 (frozen): the margin to (sqrt(a-1)+sqrt(b-1))^2 stays strictly positive at every")
    print("(p,q) tested, so this run supports Conjecture 1.4 rather than refuting it.\n")

    rng = np.random.default_rng(90210)
    ALL = [(6, 9, 3, 2), (8, 12, 3, 2), (10, 15, 3, 2), (8, 16, 4, 2)]
    # optional: rl_push.py <budget_seconds> [case_index ...]
    sel = [int(x) for x in sys.argv[2:]] if len(sys.argv) > 2 else list(range(len(ALL)))
    CASES = [ALL[i] for i in sel]

    print(f"{'p':>4}{'q':>4}{'a':>3}{'b':>3}{'edge':>11}{'class':>13}"
          f"{'best max root':>15}{'margin':>12}{'approach':>10}{'verdict':>11}")
    worst_margin = 1e18
    any_violation = False
    for (p, q, a, b) in CASES:
        if time.time() - t0 > BUDGET_S:
            print("  [budget reached; remaining cases skipped]")
            break
        lo, hi = band(a, b)

        # graphs
        gmax, ng = -1e18, 0
        for _ in range(400):
            if time.time() - t0 > BUDGET_S:
                break
            adj = random_biregular(p, q, a, b, rng)
            if adj is None:
                continue
            ng += 1
            r = np.roots(mixed_char_poly(graph_to_projections(adj, p, q))).real
            gmax = max(gmax, float(r.max()))
        if ng:
            m = hi - gmax
            worst_margin = min(worst_margin, m)
            any_violation = any_violation or m < 0
            print(f"{p:>4}{q:>4}{a:>3}{b:>3}{hi:>11.6f}{f'graphs({ng})':>13}"
                  f"{gmax:>15.8f}{m:>+12.8f}{approach(gmax,a,b):>10.4f}"
                  f"{('VIOLATION' if m < 0 else 'holds'):>11}")

        # projections and PSD rank-b, harder schedule than the sweep default
        for label, flag in (("projections", False), ("PSD rank-b", True)):
            if time.time() - t0 > BUDGET_S:
                break
            v_hi, A_hi = hill_climb(p, q, a, b, rng, 'hi', psd_class=flag,
                                    n_restart=30, n_step=1200, eps0=0.6)
            rmax = -v_hi
            m = hi - rmax
            worst_margin = min(worst_margin, m)
            any_violation = any_violation or m < 0
            print(f"{'':>4}{'':>4}{'':>3}{'':>3}{'':>11}{label:>13}"
                  f"{rmax:>15.8f}{m:>+12.8f}{approach(rmax,a,b):>10.4f}"
                  f"{('VIOLATION' if m < 0 else 'holds'):>11}")

    print(f"\n  smallest margin to the conjectured edge over everything: {worst_margin:+.8f}")
    if any_violation:
        print("  P19 IS FALSE. A family exceeds (sqrt(a-1)+sqrt(b-1))^2, which would refute")
        print("  Xu's Conjecture 1.4 and Ravichandran-Leake Conjecture 1. RE-CHECK IN EXACT")
        print("  ARITHMETIC before reporting this to anyone.")
    else:
        print("  P19 holds. No family reaches the edge, in any class, at any dimension tested.")
        print("  This is adversarial evidence FOR Conjecture 1.4 from the plane-family side.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
