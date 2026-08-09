"""Does the coupled induction close, and where?

The route needs F_w < 0 at every right-type path-tree vertex. Bounding the two sides separately
and feeding each into the other gives a closed system. Write Delta = q - r, K = q - 1 for the
largest child count, and let

    kappa(j)  bound the ratio of a LEFT-type vertex with j children,
    mu(j)     bound |F| from below for a RIGHT-type vertex with j children.

A left-type vertex's children are right-type, and min_children gives each of them at least
Delta children, so kappa(j) = lambda + j / mu_min. A right-type vertex's children are left-type,
and child_count_drop caps each of their child counts at j - Delta, so
mu(j) = j / kappa(j - Delta) - lambda. Base case: a leaf has ratio exactly lambda, kappa(0) =
lambda, and right-type leaves cannot occur once Delta >= 1.

mu is DECREASING in j, so the binding value is its limit mu_min = Delta/lambda - 2 lambda,
positive exactly when Delta > 2 lambda^2. That is the first condition. The second is that
mu(j) > 0 for every attainable j, which is a finite check over Delta <= j <= K.

FROZEN BEFORE THE DATA:
  P12. The two conditions hold for every (d,q,r) in which the invariant was measured to hold.

If P12 holds the route closes on those families and the biregular case is proved there. If it
fails somewhere the invariant nevertheless holds, the bounds are lossy and the induction needs
a sharper combinatorial input than child_count_drop alone; that is then the honest finding.
"""
import os, sys, math
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'

def closes(d,q,r,lam):
    D = q - r
    if D < 1: return False, "Delta < 1: right-type leaves possible, sign alternation breaks"
    mu_min = D/lam - 2*lam
    if mu_min <= 0: return False, f"Delta={D} <= 2 lam^2={2*lam*lam:.4f}: mu_min <= 0"
    kappa = lambda j: lam + j/mu_min
    K = q-1
    for j in range(D, K+1):
        if j/kappa(j-D) <= lam:
            return False, f"mu({j}) <= 0: {j}/kappa({j-D})={j/kappa(j-D):.4f} <= lam={lam:.4f}"
    return True, f"closes; mu_min={mu_min:.4f}, worst j gives margin " \
                 f"{min(j/kappa(j-D)-lam for j in range(D,K+1)):.4f}"

print("Does the coupled induction close?  (lambda swept across the gap)\n")
print(f"{'(d,q,r)':>11}{'Delta':>7}{'g':>9}{'closes up to lam =':>20}   reason at the edge")
for (d,q,r) in ((3,6,4),(3,6,5),(3,6,6),(3,9,4),(4,8,4),(3,12,4),(4,12,4),(5,10,4)):
    if (r*q)%d: continue
    g = math.sqrt(q-1)-math.sqrt(d-1)
    best=0.0; reason=""
    for i in range(1,1001):
        lam = i/1000*g
        ok,msg = closes(d,q,r,lam)
        if ok: best=lam
        else:
            reason=msg; break
    frac = best/g
    print(f"{f'({d},{q},{r})':>11}{q-r:>7}{g:>9.4f}"
          f"{f'{best:.4f} ({frac:.0%} of g)':>20}   {reason[:46]}")
print()
print("Comparison with where the invariant was MEASURED to hold (all of them, at 0.99g):")
print("  (3,6,4) (3,6,5) (3,9,4) (3,6,6) (4,8,4)")
