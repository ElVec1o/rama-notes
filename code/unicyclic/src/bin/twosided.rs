// IDEA.  For (a,b)-biregular bipartite G write mu_G(x) = x^eps * f(x^2), and set
//     c = (a-1) + (b-1),   m = (a-1)(b-1),   g(z) = f(z + c).
// The (a,b)-biregular tree has spectrum {0} u +-[s-t, s+t], s=sqrt(a-1), t=sqrt(b-1), and
//     x in spec  <=>  x^2 - c  in  [-2 sqrt(m), 2 sqrt(m)],
// the Heilmann-Lieb interval of effective degree m+1.  So the conjecture, for biregular G, is
// exactly:  every root of g lies in [-2 sqrt m, 2 sqrt m].
// The known biregular Ramanujan bound gives the UPPER edge |x| <= s+t; the conjecture is the
// LOWER edge |x| >= |s-t|.  They are the two ends of one interval: the conjecture is the missing
// half of a two-sided Heilmann-Lieb theorem.
//
// This program (i) verifies the two-sided statement numerically, and (ii) tests whether g is
// itself a matching polynomial -- which would let Heilmann-Lieb apply verbatim.  A matching
// polynomial on n vertices has only every other power of z, so a nonzero z^{n-1} coefficient
// disproves it immediately.
use std::collections::HashMap;
type P = Vec<i128>;
fn norm(mut p:P)->P{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&P,b:&P)->P{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn matching_poly(n:usize,e:&[(usize,usize)])->P{
    let mut adj=vec![vec![];n];
    for &(u,v) in e { adj[u].push(v); adj[v].push(u); }
    let mut memo:HashMap<(u64,usize),Vec<i128>>=HashMap::new();
    fn go(v:usize,used:u64,n:usize,adj:&Vec<Vec<usize>>,
          memo:&mut HashMap<(u64,usize),Vec<i128>>)->Vec<i128>{
        let mut v=v; while v<n && (used>>v)&1==1 {v+=1;}
        if v==n {return vec![1];}
        if let Some(r)=memo.get(&(used,v)){return r.clone();}
        let mut res=go(v+1,used|(1u64<<v),n,adj,memo);
        for &w in &adj[v]{ if w>v && (used>>w)&1==0 {
            let sub=go(v+1,used|(1u64<<v)|(1u64<<w),n,adj,memo);
            let mut sh=vec![0i128;sub.len()+1];
            for (i,c) in sub.iter().enumerate(){sh[i+1]+=c;}
            res=add(&res,&sh);} }
        memo.insert((used,v),res.clone()); res }
    let mk=go(0,0,n,&adj,&mut memo);
    let mut p=vec![0i128;n+1];
    for (k,&c) in mk.iter().enumerate(){ if 2*k<=n {p[n-2*k]+= if k%2==0 {c} else {-c};} }
    norm(p) }
/// mu(x) = x^eps * f(x^2): extract f
fn extract_f(mu:&P)->(usize,P){
    let eps = mu.iter().position(|&c| c!=0).unwrap();
    let mut f=vec![];
    let mut i=eps;
    while i < mu.len() { f.push(mu[i]); i+=2; }
    (eps, norm(f)) }
/// g(z) = f(z + c), exact integer shift
fn shift(f:&P, c:i128)->P{
    let n=f.len();
    let mut g=vec![0i128;n];
    // Horner-style synthetic substitution
    let mut cur=f.clone();
    for k in 0..n {
        // g[k] = cur evaluated-remainder constant term after dividing by (z - (-c))? do it directly
        let mut rem=0i128; let mut newp=vec![0i128; cur.len().saturating_sub(1)];
        for i in (0..cur.len()).rev() {
            let coef = cur[i] + rem*c;
            if i>0 { newp[i-1]=coef; } else { g[k]=coef; }
            rem = if i>0 { coef } else { rem };
        }
        // recompute properly: synthetic division of cur by (z + c) ... simpler: direct binomial
        let _ = &newp;
        break;
    }
    // direct binomial expansion (n small)
    let mut out=vec![0i128;n];
    for (i,&fi) in f.iter().enumerate() {
        if fi==0 { continue; }
        // fi * (z + c)^i
        let mut binom=vec![0i128;i+1]; binom[0]=1;
        for _ in 0..i {
            let mut nb=vec![0i128;binom.len()+1];
            for (j,&b) in binom.iter().enumerate(){ nb[j+1]+=b; nb[j]+=b*c; }
            binom=nb;
        }
        for (j,&b) in binom.iter().enumerate(){ if j<out.len() { out[j]+=fi*b; } }
    }
    norm(out) }
fn roots(p:&P, lo:f64, hi:f64)->Vec<f64>{
    let pf:Vec<f64>=p.iter().map(|&c| c as f64).collect();
    let ev=|x:f64| pf.iter().rev().fold(0.0,|a,&k| a*x+k);
    let m=1_000_000usize; let mut r=vec![]; let mut px=lo; let mut pv=ev(lo);
    for i in 1..=m { let x=lo+(hi-lo)*(i as f64)/(m as f64); let v=ev(x);
        if pv*v<0.0 { let (mut l,mut rr)=(px,x);
            for _ in 0..80 { let mid=0.5*(l+rr); if ev(l)*ev(mid)<=0.0 {rr=mid;} else {l=mid;} }
            r.push(0.5*(l+rr)); } px=x; pv=v; }
    r }
fn kpq(p:usize,q:usize)->(usize,Vec<(usize,usize)>){
    let mut e=vec![]; for i in 0..p { for j in 0..q { e.push((i,p+j)); } } (p+q,e) }
fn sub_reg(n:usize,e:&[(usize,usize)])->(usize,Vec<(usize,usize)>){
    let mut o=vec![]; for (k,&(u,v)) in e.iter().enumerate(){ o.push((u,n+k)); o.push((v,n+k)); }
    (n+e.len(),o) }
fn main(){
    println!("g(z) = f(z+c),  c=(a-1)+(b-1),  m=(a-1)(b-1).  Conjecture <=> roots(g) in [-2rt m, 2rt m].\n");
    let mut ts: Vec<(String,usize,Vec<(usize,usize)>,f64,f64)> = vec![];
    { let (n,e)=kpq(3,4); ts.push(("K_{3,4}".into(),n,e,4.0,3.0)); }
    { let (n,e)=kpq(3,5); ts.push(("K_{3,5}".into(),n,e,5.0,3.0)); }
    { let (n,e)=kpq(4,5); ts.push(("K_{4,5}".into(),n,e,5.0,4.0)); }
    { let (n,e)=kpq(2,4); ts.push(("K_{2,4}".into(),n,e,4.0,2.0)); }
    // subdivision of K_4: (3,2)-biregular, the b=2 control
    let k4=vec![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)];
    { let (n,e)=sub_reg(4,&k4); ts.push(("S(K_4)".into(),n,e,3.0,2.0)); }
    for (name,n,e,a,b) in ts {
        let mu=matching_poly(n,&e);
        let (eps,f)=extract_f(&mu);
        let c=((a-1.0)+(b-1.0)) as i128;
        let m=(a-1.0)*(b-1.0);
        let g=shift(&f, c);
        let bound=2.0*m.sqrt();
        let rs=roots(&g,-3.0*bound-5.0, 3.0*bound+5.0);
        let maxabs=rs.iter().cloned().map(f64::abs).fold(0.0f64,f64::max);
        // is g a matching polynomial? needs alternating zero coefficients (only every other power)
        let deg=g.len()-1;
        let second = if deg>=1 { g[deg-1] } else { 0 };
        println!("{:10} (a,b)=({},{})  eps={}  c={}  2rt(m)={:.4}", name, a, b, eps, c, bound);
        println!("   g = {:?}", g);
        println!("   roots(g) max|.| = {:.4}   within HL interval: {}",
                 maxabs, if maxabs <= bound + 1e-6 {"YES"} else {"NO"});
        println!("   z^(deg-1) coeff = {}  =>  g is a matching polynomial: {}",
                 second, if second==0 {"possible"} else {"IMPOSSIBLE"});
        println!();
    }
}
