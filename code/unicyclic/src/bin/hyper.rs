// SFM Problem 1 at r >= 3.  H is a (d,r)-regular hypergraph; B_H its incidence graph, a
// (d,r)-biregular bipartite graph.  Problem 1 asks: no root mu of mu_{B_H} with
// 0 < |mu| < |sqrt(d-1) - sqrt(r-1)|.
// The r=2 proof runs through Yan-Yeh: mu_{S(H)}(x) = x^{m-n} mu_H(x^2 - d), so g(z) = f(z+c) is a
// GRAPH matching polynomial and Heilmann-Lieb applies, two-sidedly.  For r >= 3 we test whether g
// could still be a matching polynomial: a matching polynomial on n vertices uses only every other
// power, so a nonzero subleading coefficient rules it out.
use std::collections::HashMap;
type P = Vec<i128>;
fn norm(mut p:P)->P{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&P,b:&P)->P{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn mcounts(n:usize,e:&[(usize,usize)])->Vec<i128>{
    let mut adj=vec![0u64;n];
    for &(u,v) in e { adj[u]|=1u64<<v; adj[v]|=1u64<<u; }
    let mut memo:HashMap<u64,Vec<i128>>=HashMap::new();
    fn go(al:u64,adj:&Vec<u64>,n:usize,m:&mut HashMap<u64,Vec<i128>>)->Vec<i128>{
        if let Some(r)=m.get(&al){return r.clone();}
        let mut v=0usize; while v<n && (al>>v)&1==0 {v+=1;}
        if v==n {return vec![1];}
        let rest=al & !(1u64<<v);
        let mut res=go(rest,adj,n,m);
        let mut nb=adj[v]&rest;
        while nb!=0 { let w=nb.trailing_zeros() as usize; nb&=nb-1;
            let s=go(rest & !(1u64<<w),adj,n,m);
            let mut sh=vec![0i128;s.len()+1];
            for (i,c) in s.iter().enumerate(){sh[i+1]+=c;}
            res=add(&res,&sh); }
        m.insert(al,res.clone()); res }
    go((1u64<<n)-1,&adj,n,&mut memo) }
fn shift(f:&P,c:i128)->P{
    fn binom(n:usize,k:usize)->i128{ let mut r=1i128; for i in 0..k { r=r*((n-i) as i128)/((i+1) as i128);} r }
    let mut out=vec![0i128;f.len()];
    for (i,&fi) in f.iter().enumerate(){ if fi==0 {continue;}
        for j in 0..=i { out[j]+=fi*binom(i,j)*c.pow((i-j) as u32); } }
    norm(out) }
/// hypergraph given as list of edges (each a Vec of vertex indices)
fn incidence(nv:usize, edges:&[Vec<usize>])->(usize,Vec<(usize,usize)>){
    let mut e=vec![];
    for (i,b) in edges.iter().enumerate(){ for &v in b { e.push((v, nv+i)); } }
    (nv+edges.len(), e) }
fn main(){
    // (name, |V|, edges, d, r)
    let hs: Vec<(&str,usize,Vec<Vec<usize>>,f64,f64)> = vec![
      ("(2,3) on 6 pts, 4 triples", 6,
        vec![vec![0,1,2],vec![0,3,4],vec![1,3,5],vec![2,4,5]], 2.0, 3.0),
      ("(3,3) Fano plane", 7,
        vec![vec![0,1,2],vec![0,3,4],vec![0,5,6],vec![1,3,5],vec![1,4,6],vec![2,3,6],vec![2,4,5]], 3.0, 3.0),
      ("(2,4) on 8 pts, 4 quads", 8,
        vec![vec![0,1,2,3],vec![0,1,4,5],vec![2,4,6,7],vec![3,5,6,7]], 2.0, 4.0),
      ("(3,4) on 8 pts, 6 quads", 8,
        vec![vec![0,1,2,3],vec![0,1,4,5],vec![2,3,4,5],vec![0,2,6,7],vec![1,3,6,7],vec![4,5,6,7]], 3.0, 4.0),
    ];
    println!("{:28} {:>6} {:>8} {:>10} {:>7}  g subleading", "hypergraph","(d,r)","gap","min|root|","ratio");
    for (name,nv,edges,d,r) in hs {
        let (n,e)=incidence(nv,&edges);
        if n>26 { println!("  {:26} skipped", name); continue; }
        let ne=edges.len();
        let p=nv.min(ne);
        let c=(d-1.0)+(r-1.0);
        let cnt=mcounts(n,&e);
        let mut f=vec![0i128;p+1];
        for (k,&v) in cnt.iter().enumerate(){ if k<=p { f[p-k]+= if k%2==0 {v} else {-v}; } }
        let f=norm(f);
        let g=shift(&f, c as i128);
        let gap=((d-1.0).sqrt()-(r-1.0).sqrt()).abs();
        // min positive root of mu_{B_H}: mu(x)=x^(q-p) f(x^2), so min |root| = sqrt(min positive root of f)
        let fe=|y:f64| f.iter().rev().fold(0.0,|a,&k| a*y + k as f64);
        let (lo,hi,m)=(1e-9f64, 30.0f64, 3_000_000usize);
        let mut best=f64::INFINITY; let mut px=lo; let mut pv=fe(lo);
        for i in 1..=m { let y=lo+(hi-lo)*(i as f64)/(m as f64); let v=fe(y);
            if pv*v<0.0 { let (mut l,mut rr)=(px,y);
                for _ in 0..90 { let mid=0.5*(l+rr); if fe(l)*fe(mid)<=0.0 {rr=mid;} else {l=mid;} }
                let rt=0.5*(l+rr); if rt>1e-7 && rt<best {best=rt;} }
            px=y; pv=v; }
        let minroot = best.sqrt();
        let deg=g.len()-1;
        let sub = if deg>=1 { g[deg-1] } else { 0 };
        println!("  {:26} ({},{}) {:>8.4} {:>10.4} {:>7.3}   {} {}",
                 name, d, r, gap, minroot, minroot/gap, sub,
                 if sub==0 {"(could be a matching poly)"} else {"=> NOT a matching poly"});
    }
    println!("\nr=2 is the case where g IS a graph matching polynomial and Heilmann-Lieb applies.");
}
