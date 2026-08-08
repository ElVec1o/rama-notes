"""Dtrend.py -- does the (D) margin t*/b fall below 1 for EVERY (a,b) as p grows?

Random resolvable commuting families (a parallel classes), so the
orthogonal-partition hypothesis holds identically and only p, a, b vary.
"""
from fractions import Fraction
import sys
sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from Dclaim import deconv, psi0, is_real_rooted_exact
from Dscan3 import tstar
from Dscan4 import mu_from_blocks_fast, resolvable_family

print("%-4s %-3s %-3s %-4s | %-7s %-9s %-9s" % ("p","b","a","seed","(D)","t*(p/b)","t*/b"))
for (a, b) in [(4,2),(5,2),(6,2),(8,2),(4,3),(5,3),(6,3),(5,4),(6,4)]:
    ps = [x for x in range(b*2, 17) if x % b == 0]
    for p in ps:
        for seed in (1, 2):
            blocks = resolvable_family(p, b, a, seed)
            mu = mu_from_blocks_fast(blocks, p)
            rho = deconv(mu, psi0(p, b), p)
            rr = is_real_rooted_exact(rho)[0]
            ts, sat = tstar(mu, p, b, p // b, tmax=Fraction(3 * b))
            print("  %-4d %-3d %-3d %-4d | %-7s %9.5f %9.4f%s" %
                  (p, b, a, seed, rr, ts, ts / b, "  (sat)" if sat else ""))
            sys.stdout.flush()
    print()
