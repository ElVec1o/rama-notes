// The sharp open case: (a,b)-biregular with b >= 3, at d=1.  Memory-bounded (n <= 26).
// Gap edge |sqrt(a-1) - sqrt(b-1)|.  A root inside refutes.
// Also reports the invariant-region threshold u* = [(2P+Q) - sqrt(Q^2+4PQ)]/2 against gap^2,
// which is the condition for the Green's-function induction to close.
use std::collections::HashMap;
type P = Vec<i128>;
fn norm(mut p:P)->P{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&P,b:&P)->P{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn matching_poly(n:usize, e:&[(usize,usize)])->P{
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
fn min_pos_root(p:&P)->f64{
    let pf:Vec<f64>=p.iter().map(|&c| c as f64).collect();
    let ev=|x:f64| pf.iter().rev().fold(0.0,|a,&k| a*x+k);
    let (lo,hi,m)=(1e-9f64, 3.5f64, 2_000_000usize);
    let mut best=f64::INFINITY; let mut px=lo; let mut pv=ev(lo);
    for i in 1..=m { let x=lo+(hi-lo)*(i as f64)/(m as f64); let v=ev(x);
        if pv*v<0.0 { let (mut l,mut r)=(px,x);
            for _ in 0..100 { let mid=0.5*(l+r); if ev(l)*ev(mid)<=0.0 {r=mid;} else {l=mid;} }
            let rt=0.5*(l+r); if rt>1e-7 && rt<best {best=rt;} }
        px=x; pv=v; }
    best }
fn kpq(p:usize,q:usize)->(usize,Vec<(usize,usize)>){
    let mut e=vec![]; for i in 0..p { for j in 0..q { e.push((i,p+j)); } } (p+q,e) }
/// incidence graph of a (v,k,lambda) design given as blocks: points + blocks, biregular
fn incidence(points:usize, blocks:&[Vec<usize>])->(usize,Vec<(usize,usize)>){
    let mut e=vec![];
    for (i,b) in blocks.iter().enumerate(){ for &p in b { e.push((p, points+i)); } }
    (points+blocks.len(), e) }
fn main(){
    println!("(a,b)-biregular, b >= 3, at d=1.  a = degree of the small side.");
    println!("{:34} {:>6} {:>9} {:>9} {:>7}  {:>8}", "graph","(a,b)","gap edge","min root","ratio","u*/gap^2");
    let mut tests: Vec<(String,usize,Vec<(usize,usize)>,f64,f64)> = vec![];
    // K_{p,q}: p-side has degree q, q-side has degree p; need min degree >= 3
    for &(p,q) in &[(3usize,4usize),(3,5),(3,6),(3,7),(4,5),(4,6),(3,8),(4,7),(5,6)] {
        if p+q > 26 { continue; }
        let (n,e)=kpq(p,q);
        tests.push((format!("K_{{{},{}}}",p,q), n, e, q as f64, p as f64));
    }
    // Fano plane incidence: (3,3)-regular -> no gap, skip; use a 2-design with unequal degrees
    // biplane-ish: 7 points, blocks of size 4 -> points degree 4, blocks degree 4 (regular) skip
    // truncated: 6 points, 4 blocks of size 3 -> point degree 2, block degree 3
    let blocks = vec![vec![0,1,2], vec![0,3,4], vec![1,3,5], vec![2,4,5]];
    let (n,e)=incidence(6,&blocks);
    tests.push(("design 6pts/4blocks (2,3)".into(), n, e, 3.0, 2.0));
    for (name,n,e,a,b) in tests {
        let (s,t)=((a-1.0).sqrt(),(b-1.0).sqrt());
        let gap=(s-t).abs();
        if gap < 1e-9 { println!("{:34} {:>6} regular, no gap", name, format!("({},{})",a,b)); continue; }
        let mp=matching_poly(n,&e);
        let mr=min_pos_root(&mp);
        // invariant region threshold
        let (pp,qq)=(a-1.0, b-1.0);
        let ustar=((2.0*pp+qq)-(qq*qq+4.0*pp*qq).sqrt())/2.0;
        println!("{:34} {:>6} {:>9.5} {:>9.5} {:>7.3}  {:>8.3}  {}",
                 name, format!("({},{})",a,b), gap, mr, mr/gap, ustar/(gap*gap),
                 if mr < gap {"*** IN GAP: REFUTED ***"} else {"ok"});
    }
}
