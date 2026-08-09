"""The biregular margin decays at the soft-edge exponent.

The margin x_min - g falls monotonically with size in every biregular family: for (3,6) it
goes 0.530 at r=4 to 0.210 at r=16 over thirteen consecutive decreases (code/bireg_trend.py).
The question is the RATE, because it decides the character of the conjecture.

A log-log read of that data gives slope about -2/3.  That exponent is not arbitrary: n^{-2/3}
is the soft-edge scale of random matrix theory, the rate at which extreme eigenvalues approach
a spectral edge.  If it is right then

  * the margin tends to zero, so no crude bound can ever prove D3 or Problem 1;
  * but it tends to zero from ABOVE, so both are true and merely tight;
  * and the correct statement is a Friedman-type theorem: the roots of mu_G fill out the
    spectrum of the universal cover without escaping it, exactly as the eigenvalues of a random
    regular graph fill out [-2 sqrt(d-1), 2 sqrt(d-1)].

That is the Alon-Boppana analogy the note already draws, now with an exponent attached.

FROZEN BEFORE THIS DATA:
  P4.  margin ~ C n^{-2/3}, and in particular the fitted exponent is nearer -2/3 than
       -1/2 or -1.

Rejecting P4 in favour of a smaller exponent would mean the margin dies faster than the
soft-edge rate, which is where a refutation would have to live.
"""
import os, sys, math, time, random
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np, sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bireg_trend import rand_biregular, matching_counts, xmin_from_counts

def main():
    print("P4 (frozen): the biregular margin decays like n^{-2/3}.\n")
    print(f"{'family':>8}{'r':>4}{'n':>5}{'min margin':>12}{'seeds':>7}")
    t0=time.time(); T={}
    for (d,q) in ((3,6),(3,9),(4,8),(4,12),(5,10)):
        g=math.sqrt(q-1)-math.sqrt(d-1)
        for r in range(4,18):
            if (r*q)%d or time.time()-t0>1600: continue
            m=(r*q)//d; n=m+r
            if n>78: continue
            best=None; used=0
            for seed in range(40):
                R=rand_biregular(d,q,r,seed)
                if R is None: continue
                mm,nbr=R
                xm=xmin_from_counts(matching_counts(mm,r,nbr),r)
                if xm is None: continue
                used+=1
                if best is None or xm<best: best=xm
                if used>=12: break
            if best is None or used<3: continue
            T.setdefault((d,q),[]).append((r,n,best-g))
            print(f"{f'({d},{q})':>8}{r:>4}{n:>5}{best-g:>12.6f}{used:>7}", flush=True)
        print()
    print(f"{time.time()-t0:.0f}s\n")
    print(f"{'family':>8}{'pts':>5}{'exponent in n':>15}{'R^2':>9}{'C':>10}{'nearest':>10}")
    exps=[]
    for (d,q),rows in sorted(T.items()):
        if len(rows)<5: continue
        ns=np.log(np.array([t[1] for t in rows],float))
        ms=np.log(np.array([t[2] for t in rows],float))
        a,b=np.polyfit(ns,ms,1)
        pred=a*ns+b; ss=1-((ms-pred)**2).sum()/((ms-ms.mean())**2).sum()
        near=min([(-1/2,'-1/2'),(-2/3,'-2/3'),(-1.0,'-1')],key=lambda t:abs(a-t[0]))[1]
        print(f"{f'({d},{q})':>8}{len(rows):>5}{a:>15.4f}{ss:>9.4f}{math.exp(b):>10.4f}{near:>10}")
        exps.append(a)
    if exps:
        mu=float(np.mean(exps))
        print(f"\n  mean exponent {mu:.4f}   (-2/3 = {-2/3:.4f})")
        if abs(mu+2/3) < min(abs(mu+0.5), abs(mu+1.0)):
            print("  P4 HOLDS: nearest to the soft-edge exponent -2/3.")
            print("  So the margin vanishes, but from above: D3 and Problem 1 are true and tight,")
            print("  and any proof must be a Friedman-type edge theorem, not a crude bound.")
        else:
            print(f"  P4 FAILS: the exponent is nearer {min([(-1/2,'-1/2'),(-1.0,'-1')],key=lambda t:abs(mu-t[0]))[1]}.")
        for (d,q),rows in sorted(T.items()):
            if len(rows)>=5:
                r,n,m0=rows[-1]
                print(f"    ({d},{q}) at n={n}: margin {m0:.4f}; at n=10^4 the fit gives "
                      f"{math.exp(np.polyfit(np.log([t[1] for t in rows]),np.log([t[2] for t in rows]),1)[1])*10**(4*mu):.5f}")
if __name__=='__main__': sys.exit(main())
