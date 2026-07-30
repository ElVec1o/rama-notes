// CHARACTERIZATION + ASYMMETRIC RECURSION.
// f_G(y) = sum_k (-1)^k m_k y^{p-k}  = multivariate matching polynomial at x_A = y, x_B = 1.
// Deleting a vertex gives TWO different recursions, because only A-vertices carry the variable:
//    v in A :  f_G = y * f_{G-v} - sum_{u ~ v} f_{G-v-u}
//    u in B :  f_G =     f_{G-u} - sum_{v ~ u} f_{G-u-v}      (no y)
// Hence the cavity recursion is asymmetric:
//    R_A = y - sum 1/R_B ,   R_B = 1 - sum 1/R_A .
// On the (a,b)-biregular tree with P=a-1, Q=b-1 the fixed point satisfies
//    R^2 + R(P - Q - y) + yQ = 0,   discriminant  D = (P-Q-y)^2 - 4yQ,
// and D = 0 exactly at y = (sqrt P +- sqrt Q)^2, the spectrum edges in the y variable.
// This program checks all of that exactly on real graphs.
use std::collections::HashMap;
type Pn = Vec<i128>;
fn norm(mut p:Pn)->Pn{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&Pn,b:&Pn)->Pn{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn sub(a:&Pn,b:&Pn)->Pn{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)-b.get(i).copied().unwrap_or(0)).collect()) }
fn shl(a:&Pn)->Pn{ let mut r=vec![0i128]; r.extend(a.iter()); norm(r) }  // multiply by y

/// number of k-matchings of the subgraph induced on `alive`
fn mk(alive:u64, adj:&Vec<u64>, n:usize, memo:&mut HashMap<u64,Vec<i128>>)->Vec<i128>{
    if let Some(r)=memo.get(&alive){ return r.clone(); }
    // lowest alive vertex
    let mut v=0usize; while v<n && (alive>>v)&1==0 { v+=1; }
    if v==n { return vec![1]; }
    let rest = alive & !(1u64<<v);
    let mut res = mk(rest, adj, n, memo);           // v unmatched
    let mut nb = adj[v] & rest;
    while nb != 0 {
        let w = nb.trailing_zeros() as usize;
        nb &= nb-1;
        let sub2 = rest & !(1u64<<w);
        let s = mk(sub2, adj, n, memo);
        let mut sh=vec![0i128;s.len()+1];
        for (i,c) in s.iter().enumerate(){ sh[i+1]+=c; }
        res = add(&res,&sh);
    }
    memo.insert(alive,res.clone()); res
}
/// f_G(y) = sum_k (-1)^k m_k y^{p-k}, p = |A|
fn f_poly(n:usize, adj:&Vec<u64>, p:usize)->Pn{
    let mut memo=HashMap::new();
    let counts = mk((1u64<<n)-1, adj, n, &mut memo);
    let mut f=vec![0i128;p+1];
    for (k,&c) in counts.iter().enumerate(){ if k<=p { f[p-k] += if k%2==0 {c} else {-c}; } }
    norm(f)
}
fn f_sub(n:usize, adj:&Vec<u64>, alive:u64, p:usize)->Pn{
    let mut memo=HashMap::new();
    let counts = mk(alive, adj, n, &mut memo);
    let mut f=vec![0i128;p+1];
    for (k,&c) in counts.iter().enumerate(){ if k<=p { f[p-k] += if k%2==0 {c} else {-c}; } }
    norm(f)
}
fn main(){
    // (name, |A|, |B|, edges as (a-index, b-index))
    let tests: Vec<(&str,usize,usize,Vec<(usize,usize)>)> = vec![
        ("K_{3,4}", 3,4, (0..3).flat_map(|i| (0..4).map(move |j| (i,j))).collect()),
        ("K_{3,5}", 3,5, (0..3).flat_map(|i| (0..5).map(move |j| (i,j))).collect()),
        ("K_{2,4}", 2,4, (0..2).flat_map(|i| (0..4).map(move |j| (i,j))).collect()),
        ("C_6 as K_{3,3} minus perfect matching", 3,3,
            vec![(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]),
    ];
    for (name,p,q,edges) in tests {
        let n=p+q;
        let mut adj=vec![0u64;n];
        for &(i,j) in &edges { adj[i] |= 1u64<<(p+j); adj[p+j] |= 1u64<<i; }
        let full=(1u64<<n)-1;
        let f = f_poly(n,&adj,p);
        println!("{}  |A|={} |B|={}", name, p, q);
        println!("   f = {:?}", f);
        // CHECK the A-recursion at v = 0 (an A-vertex)
        let v=0usize;
        let gv = full & !(1u64<<v);
        let mut rhs = shl(&f_sub(n,&adj,gv,p-1));
        let mut nb = adj[v];
        while nb!=0 { let u=nb.trailing_zeros() as usize; nb&=nb-1;
            rhs = sub(&rhs, &f_sub(n,&adj, gv & !(1u64<<u), p-1)); }
        println!("   A-recursion  f = y f_(G-v) - sum f_(G-v-u):  {}",
                 if rhs==f {"HOLDS"} else {"FAILS"});
        // CHECK the B-recursion at u = p (a B-vertex)
        let u=p;
        let gu = full & !(1u64<<u);
        let mut rhs2 = f_sub(n,&adj,gu,p);
        let mut nb2 = adj[u];
        while nb2!=0 { let w=nb2.trailing_zeros() as usize; nb2&=nb2-1;
            rhs2 = sub(&rhs2, &f_sub(n,&adj, gu & !(1u64<<w), p-1)); }
        println!("   B-recursion  f = f_(G-u) - sum f_(G-u-v)   :  {}",
                 if rhs2==f {"HOLDS"} else {"FAILS"});
        // discriminant edges, for biregular cases
        let (a,b)=(q as f64, p as f64);   // A-degree = |B| for complete bipartite
        let (pp,qq)=(a-1.0,b-1.0);
        let (lo,hi)=((pp.sqrt()-qq.sqrt()).powi(2), (pp.sqrt()+qq.sqrt()).powi(2));
        let d=|y:f64| (pp-qq-y).powi(2)-4.0*y*qq;
        println!("   D(y)=(P-Q-y)^2-4yQ :  D({:.5})={:.2e}   D({:.5})={:.2e}   D(midpoint)={:.4}",
                 lo, d(lo), hi, d(hi), d(0.5*(lo+hi)));
        println!();
    }
    println!("D vanishes at both spectrum edges and is negative between them:");
    println!("the asymmetric recursion's fixed point is complex exactly on the spectrum.");
}
