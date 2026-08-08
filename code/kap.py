import sys, math, cmath, itertools, numpy as np
sys.path.insert(0,'code')
exec(open('code/inertia_split.py').read().split('GRAPHS = {')[0].split('"""',2)[2])
ns={}; exec(open('code/universal_cover.py').read().replace("if __name__ == '__main__':",'if False:'), ns)
scan,kappa_above,bands = ns['scan'],ns['kappa_above'],ns['bands']
G = {'twotri':(6,[(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3)]),
     'theta':(6,[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,3)]),
     'tri-P4-tri':(9,[(0,1),(1,2),(2,0),(0,6),(6,7),(7,8),(8,3),(3,4),(4,5),(5,3)])}
S=128
print(f"{'graph':>11}{'x':>9}{'kap':>4}{'m1':>7}{'err':>9}{'wmean':>8}"
      f"{'Qmax/Qmin':>11}{'d+':>7}{'crude':>9}{'true':>9}")
for name,(n,e) in G.items():
    tree,cot = spanning_tree(n,e); b=len(cot)
    if b!=2: print(f"{name:>11}  b={b} skip"); continue
    cG = matching_coeffs(n,e)
    def mu(t):
        a=0.0
        for j in range(len(cG)-1,-1,-1): a=a*t+cG[j]
        return a
    got=None
    for eta in (1e-4,1e-3,1e-2):
        es,ds,_=scan(n,e,-5.0,5.0,1000,eta=eta)
        if abs(kappa_above(es,ds,1,-5.0)-1.0)<=0.03: got=(es,ds); break
    if got is None: continue
    es,ds=got; bs=bands(es,ds,1e-3)
    internal=[(bs[i][1],bs[i+1][0]) for i in range(len(bs)-1) if bs[i+1][0]-bs[i][1]>0.06]
    # batched spectra
    A0=np.zeros((n,n),complex); ci={i:j for j,i in enumerate(cot)}
    for i,(u,v) in enumerate(e):
        if i not in ci: A0[u,v]+=1.0; A0[v,u]+=1.0
    M=S**b; A=np.broadcast_to(A0,(M,n,n)).copy(); th=2*math.pi*np.arange(S)/S
    for i,(u,v) in enumerate(e):
        if i in ci:
            w=np.exp(1j*th[(np.arange(M)//(S**ci[i]))%S]); A[:,u,v]+=w; A[:,v,u]+=np.conj(w)
    lam=np.linalg.eigvalsh(A)
    lo,hi=lam.min(0),lam.max(0)
    for a_,b_ in internal:
        for f in (0.2,0.5,0.8):
            x=a_+f*(b_-a_)
            cross=[k for k in range(n) if lo[k]<=x<=hi[k]]
            kap=len(cross)
            N=(lam>x).sum(1); P=np.prod(x-lam,axis=1)
            mev=float(((N%2)==0).mean()); m=min(mev,1-mev)
            if kap==1:
                k0=cross[0]
                Q=np.prod(np.delete(x-lam,k0,axis=1),axis=1)
                val=float(np.mean((x-lam[:,k0])*np.abs(Q)))
                sgn=1.0 if np.all(Q>0) else (-1.0 if np.all(Q<0) else 0.0)
                form=sgn*val
                wm=float(np.sum(lam[:,k0]*np.abs(Q))/np.sum(np.abs(Q)))
                err=abs(form-mu(x))/max(abs(mu(x)),1e-12)
                aQ=np.abs(Q); Qr=float(aQ.max()/aQ.min())
                lk=lam[:,k0]; up=lk>x
                m1=float(up.mean()); dplus=float(lk.max()-x)
                num=float(np.mean(np.where(up,(lk-x)*aQ,0.0)))
                den=float(np.mean(np.where(~up,(x-lk)*aQ,0.0)))
                # crude: replace |Q| by its extremes and the excursion by its max
                crude=(m1*dplus*float(aQ.max()))/max((1-m1)*float(np.mean(np.where(~up,(x-lk),0.0))/max(1-m1,1e-12))*float(aQ.min()),1e-300)
                print(f"{name:>11}{x:>9.4f}{kap:>4}{m1:>7.4f}{err:>9.1e}{wm:>8.3f}"
                      f"{Qr:>11.2f}{dplus:>7.3f}{crude:>9.2f}{num/max(den,1e-300):>9.4f}")
            else:
                print(f"{name:>11}{x:>9.4f}{kap:>4}{m:>7.4f}{'-':>9}{'-':>8}{'-':>11}{'-':>7}{'-':>9}{'-':>9}")
