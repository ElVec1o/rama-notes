"""Dorig.py -- re-audit the ORIGINAL family list (ff_step1.graph_fams + rand_fams,
the list behind the '133 families' / '111 reach the tree edge' claims) with EXACT
Sturm real-rootedness instead of the float |Im| < 1e-7 test."""
import sys
from fractions import Fraction
sys.path.insert(0,'/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
import numpy as np
from ff_step1 import graph_fams, rand_fams
from Dclaim import deconv, psi0, boxp_pow, is_real_rooted_exact, maximag_float

print("%-26s %-13s | %-8s %-9s %-10s %-16s" %
      ("family","(p,q,a,b)","(D) exact","max|Im|","float test","J={j: rho_j rr}"))
nD=nfloat=n=0
for name,p,q,a,b,e in graph_fams()+rand_fams():
    # ff_boxp signed-e convention -> highest-power-first coefficients
    mu = [Fraction((-1)**i)*Fraction(e[i]) for i in range(p+1)]
    rho = deconv(mu, psi0(p,b), p)
    rr = is_real_rooted_exact(rho)[0]
    mi,_ = maximag_float(rho)
    fl = mi < 1e-7
    J=[]
    for j in range(1,a+1):
        r = deconv(mu, boxp_pow(psi0(p,b),p,j), p)
        if is_real_rooted_exact(r)[0]: J.append(j)
    n+=1; nD+=int(rr); nfloat+=int(fl)
    flag = "" if rr==fl else "   <-- float test DISAGREES"
    print("  %-26s (%2d,%2d,%d,%d) | %-8s %.3e %-10s %-16s%s" %
          (name,p,q,a,b,rr,mi,fl,str(J),flag))
    sys.stdout.flush()
print("\n  ---> %d families;  (D) true (exact Sturm) in %d;  float |Im|<1e-7 said %d"
      % (n,nD,nfloat))
