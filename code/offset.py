"""The residual offset, and the exact asymptotic constant.

TWO QUESTIONS LEFT after the exponent was settled at -2/3.

(1) The measured margins sit about 0.088 above the analytic quantile's exponent at the same n.
    Is that a constant of convention or a real departure?  The diagnostic is exact and needs no
    fitting: for each measured graph compute

        N_obs  =  n * (mass of rho between g and x_min),

    the number of roots the ANALYTIC density predicts below the observed smallest root.  The
    quantile convention sets that to 1.  If N_obs is constant across sizes, the offset is the
    convention and nothing more.  If N_obs drifts with n, the finite-graph root distribution
    really does depart from the tree measure at the edge, and the drift exponent measures it.

    FROZEN: P9.  N_obs is constant in n; the offset is a convention.

(2) The asymptotic constant.  Near the inner edge rho(x) = kappa sqrt(x-g) + O(x-g), so
    n * integral = n kappa (2/3) delta^(3/2) = 1 gives

        margin  ->  (3 / (2 kappa n))^(2/3),

    an explicit constant for every (d,q).  That turns "prove the margin is positive" into a
    fully quantified target: a proof must reach a bound of exactly this size.  kappa is
    extracted from the analytic density as the limit of rho(g+delta)/sqrt(delta).
"""
import os, sys, math, json
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quantile import rho_vec, cumulative, quantile_from_cdf

def kappa_of(d,q):
    """rho(g+delta) / sqrt(delta) as delta -> 0."""
    g = math.sqrt(q-1)-math.sqrt(d-1)
    ds = np.array([1e-7,1e-8,1e-9])
    v = rho_vec(d,q,g+ds)/np.sqrt(ds)
    return float(v[-1]), float(np.std(v)/abs(np.mean(v)))

def main():
    D = json.load(open('private/softedge3_data.json'))
    print("(1) N_obs = n * mass(g, x_min): the root count the density puts below the "
          "observed minimum\n")
    print(f"{'family':>9}{'smallest n':>12}{'largest n':>12}{'N_obs first':>13}"
          f"{'N_obs last':>12}{'drift exp':>11}")
    drifts=[]
    for k in sorted(D, key=lambda t:(int(t.split(',')[1])//int(t.split(',')[0]),t)):
        d,q = map(int,k.split(','))
        g = math.sqrt(q-1)-math.sqrt(d-1); S = math.sqrt(q-1)+math.sqrt(d-1)
        xs,c = cumulative(d,q,g,S)
        rows=[]
        for (r,n,meas) in D[k]:
            i = int(np.searchsorted(xs, g+meas))
            if i<=0 or i>=len(c): continue
            rows.append((n, n*float(c[i])))
        if len(rows)<6: continue
        ln=np.log([t[0] for t in rows]); lN=np.log([t[1] for t in rows])
        sl=float(np.polyfit(ln,lN,1)[0])
        print(f"{'('+k+')':>9}{rows[0][0]:>12}{rows[-1][0]:>12}{rows[0][1]:>13.4f}"
              f"{rows[-1][1]:>12.4f}{sl:>+11.4f}")
        drifts.append(sl)
    md=float(np.mean(drifts))
    print(f"\n  mean drift exponent of N_obs: {md:+.4f}  (0 = pure convention)")
    if abs(md) < 0.05:
        print("  P9 HOLDS: N_obs is essentially constant, so the 0.088 offset is the quantile")
        print("  convention and not a departure from the tree measure.")
    else:
        print(f"  P9 FAILS: N_obs drifts like n^{md:+.3f}. The finite-graph root distribution")
        print("  departs from the tree measure at the edge, by that much.")

    print("\n(2) the exact asymptotic constant  margin -> (3/(2 kappa n))^(2/3)\n")
    print(f"{'family':>9}{'g':>9}{'kappa':>11}{'rel err':>10}{'C':>10}"
          f"{'C n^-2/3 at 1e6':>17}{'quantile at 1e6':>17}")
    for k in sorted(D, key=lambda t:(int(t.split(',')[1])//int(t.split(',')[0]),t)):
        d,q = map(int,k.split(','))
        g = math.sqrt(q-1)-math.sqrt(d-1); S = math.sqrt(q-1)+math.sqrt(d-1)
        kap,err = kappa_of(d,q)
        if kap<=0: continue
        C = (3.0/(2.0*kap))**(2.0/3.0)
        xs,c = cumulative(d,q,g,S,N=4000000)
        pr = quantile_from_cdf(xs,c,g,1e6)
        print(f"{'('+k+')':>9}{g:>9.4f}{kap:>11.5f}{err:>10.1e}{C:>10.5f}"
              f"{C*1e6**(-2/3):>17.6e}{(pr if pr else float('nan')):>17.6e}")
    print("\n  If the two right-hand columns agree, the closed-form constant is correct and the")
    print("  asymptotic margin is pinned exactly, not just up to an exponent.")
if __name__=='__main__': sys.exit(main())
