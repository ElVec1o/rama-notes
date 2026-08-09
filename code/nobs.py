"""What drives the N_obs drift: girth, log n, or the min-over-samples estimator?

N_obs, the root count the analytic tree density places below the observed smallest root, sits
near 0.5 but drifts like n^(+0.101) across all twelve families. Three candidates.

  GIRTH. The path tree of a finite graph agrees with the biregular tree only to depth about the
  girth, and random biregular graphs have girth growing like log n. A 1/log n effect looks like
  a small power over a bounded range, which is exactly what is seen.

  LOG n. The same idea without committing to girth as the mechanism: fit against log n and
  compare fit quality with the power law.

  THE ESTIMATOR. N_obs is computed from the MINIMUM over samples. If the smallest root's
  relative fluctuation shrinks as r grows, the minimum over a fixed number of samples moves
  toward the typical value, which would make N_obs drift upward with no departure from the tree
  measure at all. The seed-count check done earlier tested the EXPONENT of the margin, not the
  level or drift of N_obs, so this is untested.

FROZEN BEFORE THE DATA:
  P10. The drift is the estimator. Recomputing N_obs from the sample MEAN rather than the
       minimum removes it.
"""
import os, sys, math, json
for _v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_v]='2'
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from softedge2 import biregular_base, swap_randomize, connected, check_biregular
from softedge3 import matching_counts, ymin_from_counts
from quantile import cumulative

def girth_bip(m, r, nbr):
    adj = {i:set() for i in range(m+r)}
    for i,s in enumerate(nbr):
        for j in s: adj[i].add(m+j); adj[m+j].add(i)
    best = 10**9
    for s0 in range(m+r):
        dist={s0:0}; par={s0:None}; Q=[s0]
        while Q:
            u=Q.pop(0)
            for w in adj[u]:
                if w not in dist: dist[w]=dist[u]+1; par[w]=u; Q.append(w)
                elif w!=par[u]: best=min(best,dist[u]+dist[w]+1)
        if best<=4: break
    return best

def main():
    print("P10 (frozen): the N_obs drift is the min-over-samples estimator.\n")
    print(f"{'family':>9}{'r':>4}{'n':>5}{'girth':>7}{'N_obs(min)':>12}{'N_obs(mean)':>13}"
          f"{'samples':>9}")
    rows=[]
    for (d,q) in ((3,6),(4,8),(3,9),(3,12)):
        g = math.sqrt(q-1)-math.sqrt(d-1); S = math.sqrt(q-1)+math.sqrt(d-1)
        xs,c = cumulative(d,q,g,S)
        for r in range(6,18):
            base = biregular_base(d,q,r)
            if base is None: continue
            m,nbr0 = base; n=m+r
            if n>90: continue
            vals, girths = [], []
            for seed in range(14):
                nbr = swap_randomize(m,r,nbr0,seed)
                if not check_biregular(m,r,nbr,d,q) or not connected(m,r,nbr): continue
                mk = matching_counts(r,nbr)
                if mk is None: continue
                ym = ymin_from_counts(mk,r)
                if ym is None: continue
                vals.append(math.sqrt(ym)-g); girths.append(girth_bip(m,r,nbr))
            if len(vals)<6: continue
            def nobs(delta):
                i=int(np.searchsorted(xs,g+delta))
                return n*float(c[i]) if 0<i<len(c) else float('nan')
            nm, nmean = nobs(min(vals)), nobs(float(np.mean(vals)))
            gir = float(np.mean(girths))
            rows.append((d,q,r,n,gir,nm,nmean))
            print(f"{f'({d},{q})':>9}{r:>4}{n:>5}{gir:>7.2f}{nm:>12.4f}{nmean:>13.4f}"
                  f"{len(vals):>9}", flush=True)
        print()
    A=np.array([(t[3],t[4],t[5],t[6]) for t in rows])
    ln, gir, nmin, nmean = np.log(A[:,0]), A[:,1], A[:,2], A[:,3]
    print(f"  girth over the whole range: {gir.min():.2f} to {gir.max():.2f}")
    print(f"\n{'estimator':>12}{'drift exp in n':>16}{'R^2 power':>11}{'R^2 in log n':>14}")
    for name, v in (("min", nmin), ("mean", nmean)):
        sl,ic = np.polyfit(ln, np.log(v), 1)
        r2p = 1-((np.log(v)-(sl*ln+ic))**2).sum()/((np.log(v)-np.log(v).mean())**2).sum()
        a,b = np.polyfit(ln, v, 1)
        r2l = 1-((v-(a*ln+b))**2).sum()/((v-v.mean())**2).sum()
        print(f"{name:>12}{sl:>+16.4f}{r2p:>11.4f}{r2l:>14.4f}")
    sl_min = np.polyfit(ln, np.log(nmin),1)[0]; sl_mean = np.polyfit(ln, np.log(nmean),1)[0]
    print()
    if abs(sl_mean) < 0.4*abs(sl_min):
        print(f"  P10 HOLDS: the drift falls from {sl_min:+.4f} to {sl_mean:+.4f} on switching")
        print("  to the mean. It is the estimator, not a departure from the tree measure.")
    else:
        print(f"  P10 FAILS: the mean estimator drifts {sl_mean:+.4f}, essentially as much as")
        print(f"  the minimum's {sl_min:+.4f}. The departure is real.")
    if gir.max()-gir.min() < 1.0:
        print(f"  girth varies by only {gir.max()-gir.min():.2f} over the whole range, so it")
        print("  cannot drive a smooth drift; the girth explanation is ruled out.")
if __name__=='__main__': sys.exit(main())
