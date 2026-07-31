"""ff_step6.py -- stress test of the CERTIFICATE

    mu = psi_0 box_p rho ,    psi_0(x) = x^{p-p/b}(x-b)^{p/b} ,
    rho := the finite free deconvolution (unique; real-rootedness is a claim),
    certified lower bound  L(mu) := max_{w<0} [ K_chi(w) + K_rho(w) - 1/w ]
                                  = left edge of supp( chi boxplus mu_rho ) ,
    chi = root measure of psi_0 = (1-1/b)delta_0 + (1/b)delta_b .

By the MSS free bound (verified in ff_step5.py),  lambda_min(mu) >= L(mu)
whenever rho is real-rooted.  QUESTION: does L(mu) >= (sqrt(a-1)-sqrt(b-1))^2 ?
"""
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import ff_boxp as F                                                            # noqa
from mcp2 import mcp                                                           # noqa
from dpp_rep import rand_proj_family, noncommutativity                         # noqa
from frac_naimark import GRAPHS, nu_coeffs                                     # noqa
from ff_step1 import band, signed_e_of_mu                                      # noqa
from ff_step4 import psi0, deconv, realrooted                                  # noqa
from ff_step5 import free_edge                                                 # noqa


def certificate(e, p, a, b):
    rho = deconv(e, psi0(p, b), p)
    rr, rts, im = realrooted(rho, p)
    if not rr:
        return None, im, None
    chi = [0.0] * (p - p // b) + [float(b)] * (p // b)
    return free_edge([chi, list(rts)], p, 'min'), im, rts


def run(cases):
    print("%-30s %-11s %-11s %-11s %-11s %s" %
          ("family", "certified", "true lmin", "tree lo", "Psi lmin", "verdict"))
    nreach = ntot = 0
    for name, p, q, a, b, e in cases:
        lo, hi = band(a, b)
        cert, im, _ = certificate(e, p, a, b)
        true_lo = F.minroot_exact(e, p, iters=45)
        Psi = F.boxp_power(psi0(p, b), p, a)
        psilo = F.minroot_exact(Psi, p, iters=45)
        ntot += 1
        if cert is None:
            print("  %-28s   rho NOT real-rooted (maxIm=%.2e)" % (name, im))
            continue
        reach = cert >= lo - 1e-9
        nreach += reach
        print("  %-28s %11.6f %11.6f %11.6f %11.6f  %s"
              % (name, cert, true_lo, lo, psilo,
                 "REACHES tree edge" if reach else "short by %.4f" % (lo - cert)))
    print("  -> certificate reaches the tree lower edge in %d of %d families"
          % (nreach, ntot))
    print()


def gen_random(specs):
    out = []
    for (p, q, a, b, seed) in specs:
        if p % b or p * a != q * b or q > 20:
            continue
        P, r = rand_proj_family(p, q, a, b, seed=seed)
        if r > 1e-10:
            continue
        e = [Fraction(x).limit_denominator(10 ** 10)
             for x in signed_e_of_mu(mcp(np.asarray(P, float)))]
        out.append(('R(%d,%d,%d,%d)s%d' % (p, q, a, b, seed), p, q, a, b, e))
    return out




# ------------------------------------------------- COMMUTING (graph) families
def graph_stress(specs, trials=3, seed=0):
    """The adversarial case at b>=3: commuting families (biregular bipartite
    graphs), which are the LEAST free and where the certificate fails at b=2."""
    from tff import random_biregular
    from frac_naimark import degrees_ok
    rng = np.random.default_rng(seed)
    cases = []
    for (p, q, a, b) in specs:
        for t in range(trials):
            adj = random_biregular(p, q, a, b, rng)
            if adj is None or not degrees_ok(adj, p, q, a, b):
                continue
            c = nu_coeffs(adj, p, q)
            cases.append(('G(%d,%d,%d,%d)#%d' % (p, q, a, b, t), p, q, a, b,
                          [Fraction((-1) ** m * c[p - m]) for m in range(p + 1)]))
    run(cases)


# --------------------------------------------------- MANDATORY REGRESSION
def regression():
    """The scalar family A_k = (b/p) I satisfies every PSD/trace/sum hypothesis
    and VIOLATES the tree band for large p.  The certificate must NOT prove the
    band for it.  Two ways it can be safe: rho fails to be real-rooted (so the
    certificate is inapplicable), or the certificate does not reach the edge."""
    print("=" * 92)
    print("MANDATORY REGRESSION -- scalar family  A_k = (b/p) I")
    print("=" * 92)
    broken = 0
    for (p, a, b) in [(6, 3, 2), (12, 3, 2), (24, 3, 2), (48, 3, 2), (96, 3, 2),
                      (12, 4, 3), (24, 4, 3), (48, 4, 3), (96, 4, 3),
                      (24, 6, 4), (48, 6, 4), (96, 6, 4), (12, 5, 3), (48, 5, 3)]:
        q = p * a // b
        e = F.scalar_family_e(p, q, a, b)
        lo, hi = band(a, b)
        tl = F.minroot_exact(e, p, iters=45)
        cert, im, _ = certificate(e, p, a, b)
        viol = tl < lo - 1e-9
        if cert is None:
            print("  (p,a,b)=(%3d,%d,%d)  rho NOT real-rooted (maxIm=%.2e) -> certificate"
                  " INAPPLICABLE;  true lmin=%.6f tree=%.6f violates band=%s"
                  % (p, a, b, im, tl, lo, viol))
            continue
        bad = (cert >= lo - 1e-9) and viol
        broken += bad
        print("  (p,a,b)=(%3d,%d,%d)  certified=%.6f  true lmin=%.6f  tree=%.6f"
              "  violates band=%s   %s"
              % (p, a, b, cert, tl, lo, viol,
                 "!!! BROKEN" if bad else "ok"))
    print("  broken cases:", broken, "(must be 0)")
    print()

if __name__ == '__main__':
    print("=" * 92)
    print("b >= 3  (the OPEN case)")
    print("=" * 92)
    specs = []
    for seed in (1, 2, 3, 4, 5):
        specs += [(6, 8, 4, 3, seed), (9, 12, 4, 3, seed), (12, 16, 4, 3, seed),
                  (6, 10, 5, 3, seed), (9, 15, 5, 3, seed),
                  (6, 12, 6, 3, seed), (9, 18, 6, 3, seed),
                  (8, 12, 6, 4, seed), (8, 10, 5, 4, seed), (12, 15, 5, 4, seed),
                  (8, 14, 7, 4, seed), (10, 12, 6, 5, seed), (10, 14, 7, 5, seed),
                  (12, 18, 6, 4, seed)]
    cases = gen_random(specs)
    for name, (adj, p, q, a, b) in GRAPHS.items():
        if b >= 3 and p % b == 0:
            c = nu_coeffs(adj, p, q)
            cases.append(('G ' + name, p, q, a, b,
                          [Fraction((-1) ** m * c[p - m]) for m in range(p + 1)]))
    run(cases)

    print("=" * 92)
    print("b = 2  (known by reflection; how does the certificate do there?)")
    print("=" * 92)
    specs2 = []
    for seed in (1, 2, 3):
        specs2 += [(4, 6, 3, 2, seed), (6, 9, 3, 2, seed), (8, 12, 3, 2, seed),
                   (10, 15, 3, 2, seed), (12, 18, 3, 2, seed),
                   (6, 12, 4, 2, seed), (8, 16, 4, 2, seed), (6, 15, 5, 2, seed)]
    run(gen_random(specs2))

    print("=" * 92)
    print("COMMUTING (graph) families at b >= 3 -- the adversarial case")
    print("=" * 92)
    graph_stress([(6, 8, 4, 3), (9, 12, 4, 3), (12, 16, 4, 3), (6, 10, 5, 3),
                  (9, 15, 5, 3), (12, 20, 5, 3), (8, 10, 5, 4), (8, 12, 6, 4),
                  (12, 15, 5, 4), (12, 18, 6, 4), (15, 20, 4, 3), (9, 18, 6, 3),
                  (6, 12, 6, 3)])

    regression()
