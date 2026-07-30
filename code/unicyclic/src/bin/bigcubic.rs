// The ratios min|root|/gap-edge for subdivisions of cubic graphs fell 1.97 -> 1.47 as the graph
// grew.  If they cross 1 the conjecture is refuted at d=1.  Larger-girth cubic graphs push the
// matching polynomial toward the universal cover spectrum, so this is where it breaks if anywhere.
use std::collections::HashMap;
type P = Vec<i128>;
fn norm(mut p:P)->P{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&P,b:&P)->P{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn match_counts(n:usize, adj:&Vec<Vec<usize>>)->Vec<i128>{
    let mut memo:HashMap<(u64,usize),Vec<i128>>=HashMap::new();
    fn go(v:usize, used:u64, n:usize, adj:&Vec<Vec<usize>>,
          memo:&mut HashMap<(u64,usize),Vec<i128>>)->Vec<i128>{
        let mut v=v; while v<n && (used>>v)&1==1 { v+=1; }
        if v==n { return vec![1]; }
        if let Some(r)=memo.get(&(used,v)) { return r.clone(); }
        let mut res=go(v+1, used|(1u64<<v), n, adj, memo);
        for &w in &adj[v] { if w>v && (used>>w)&1==0 {
            let sub=go(v+1, used|(1u64<<v)|(1u64<<w), n, adj, memo);
            let mut sh=vec![0i128; sub.len()+1];
            for (i,c) in sub.iter().enumerate(){ sh[i+1]+=c; }
            res=add(&res,&sh); } }
        memo.insert((used,v),res.clone()); res }
    go(0,0,n,adj,&mut memo) }
fn matching_poly(n:usize, e:&[(usize,usize)])->P{
    let mut adj=vec![vec![];n];
    for &(u,v) in e { adj[u].push(v); adj[v].push(u); }
    let mk=match_counts(n,&adj);
    let mut p=vec![0i128;n+1];
    for (k,&c) in mk.iter().enumerate(){ if 2*k<=n { p[n-2*k]+= if k%2==0 {c} else {-c}; } }
    norm(p) }
fn subdivide(n:usize,e:&[(usize,usize)])->(usize,Vec<(usize,usize)>){
    let mut o=vec![]; for (k,&(u,v)) in e.iter().enumerate(){ o.push((u,n+k)); o.push((v,n+k)); }
    (n+e.len(), o) }
/// generalized Petersen graph GP(n,k): outer cycle, inner star polygon, spokes
fn gp(n:usize,k:usize)->(usize,Vec<(usize,usize)>){
    let mut e=vec![];
    for i in 0..n { e.push((i,(i+1)%n)); e.push((i, n+i)); e.push((n+i, n+(i+k)%n)); }
    e.sort(); e.dedup(); (2*n, e) }
/// bipartite incidence-style cubic graphs by name
fn named()->Vec<(&'static str, usize, Vec<(usize,usize)>)>{
    let mut v: Vec<(&'static str, usize, Vec<(usize,usize)>)> = vec![];
    // Heawood graph: incidence graph of Fano plane, 14 vertices, girth 6
    let fano = [[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]];
    let mut e=vec![]; for (i,l) in fano.iter().enumerate(){ for &p in l.iter(){ e.push((p, 7+i)); } }
    v.push(("Heawood", 14, e));
    let (n,e)=gp(8,3); v.push(("Moebius-Kantor GP(8,3)", n, e));
    let (n,e)=gp(9,2); v.push(("GP(9,2)", n, e));
    let (n,e)=gp(10,2); v.push(("dodecahedron-ish GP(10,2)", n, e));
    v }
fn main(){
    let gap = 2f64.sqrt()-1.0;
    println!("subdivisions of cubic graphs; universal cover (3,2)-biregular, gap edge {:.5}", gap);
    for (name,n,e) in named() {
        let (sn,se)=subdivide(n,&e);
        if sn > 40 { println!("  {:26} skipped (n={}, memoized DP would exhaust memory)", name, sn); continue; }
        let mp=matching_poly(sn,&se);
        let pf:Vec<f64>=mp.iter().map(|&c| c as f64).collect();
        let ev=|x:f64| pf.iter().rev().fold(0.0,|a,&k| a*x+k);
        let (lo,hi,m)=(0.0f64, 1.2f64, 3_000_000usize);
        let mut minpos=f64::INFINITY; let mut px=lo+1e-9; let mut pv=ev(px);
        for i in 1..=m { let x=lo+(hi-lo)*(i as f64)/(m as f64); let vv=ev(x);
            if pv*vv<0.0 { let (mut l,mut r)=(px,x);
                for _ in 0..100 { let mid=0.5*(l+r); if ev(l)*ev(mid)<=0.0 {r=mid;} else {l=mid;} }
                let root=0.5*(l+r); if root>1e-7 && root<minpos { minpos=root; } }
            px=x; pv=vv; }
        println!("  S({:24}) n={:3}  min positive root = {:.6}  ratio {:.4}  {}",
                 name, sn, minpos, minpos/gap,
                 if minpos < gap { "*** IN GAP -- REFUTED ***" } else { "ok" });
    }
}
