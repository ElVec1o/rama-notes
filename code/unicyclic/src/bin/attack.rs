// TWO JOBS.
// (A) FALSIFY AT d=1.  The conjecture says roots of mu_{1,G} (the ordinary matching polynomial)
//     lie in spec(T_G).  The path-tree argument does NOT give this: P_8 is a subtree of the
//     (3,2)-biregular tree yet has eigenvalue 2cos(4pi/9)=0.347 inside its gap (0, sqrt2-1).
//     So we hunt for G whose universal cover is (3,2)-biregular -- i.e. G a subdivision of a cubic
//     graph, or (3,2)-biregular bipartite -- with a matching-polynomial root in the gap.
// (B) PUSH d HIGHER on K_{2,3} using mu_{d,G} = E[chi_H]/chi_G over (d+1)-covers (Hall-Puder-Sawin),
//     which is polynomial time per cover instead of exponential, plus conjugacy reduction on the
//     first free permutation.
use std::collections::HashMap;

type P = Vec<i128>;
fn norm(mut p: P) -> P { while p.len()>1 && *p.last().unwrap()==0 { p.pop(); } p }
fn add(a:&P,b:&P)->P{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }

/// count k-matchings by branching on the lowest unmatched vertex; memo on the matched-mask
fn match_counts(n: usize, adj: &Vec<Vec<usize>>) -> Vec<i128> {
    let mut memo: HashMap<(u64,usize), Vec<i128>> = HashMap::new();
    fn go(v: usize, used: u64, n: usize, adj: &Vec<Vec<usize>>,
          memo: &mut HashMap<(u64,usize), Vec<i128>>) -> Vec<i128> {
        let mut v = v;
        while v < n && (used >> v) & 1 == 1 { v += 1; }
        if v == n { return vec![1]; }
        if let Some(r) = memo.get(&(used, v)) { return r.clone(); }
        // leave v unmatched
        let mut res = go(v+1, used | (1u64<<v), n, adj, memo);
        // match v to a later neighbour
        for &w in &adj[v] {
            if w > v && (used >> w) & 1 == 0 {
                let sub = go(v+1, used | (1u64<<v) | (1u64<<w), n, adj, memo);
                let mut shifted = vec![0i128; sub.len()+1];
                for (i,c) in sub.iter().enumerate() { shifted[i+1] += c; }
                res = add(&res, &shifted);
            }
        }
        memo.insert((used, v), res.clone());
        res
    }
    go(0, 0, n, adj, &mut memo)
}
fn matching_poly(n: usize, edges: &[(usize,usize)]) -> P {
    let mut adj = vec![vec![]; n];
    for &(u,v) in edges { adj[u].push(v); adj[v].push(u); }
    let mk = match_counts(n, &adj);
    let mut p = vec![0i128; n+1];
    for (k,&c) in mk.iter().enumerate() { if 2*k<=n { p[n-2*k] += if k%2==0 {c} else {-c}; } }
    norm(p)
}
fn roots_of(poly: &[f64], lo: f64, hi: f64) -> Vec<f64> {
    let ev = |x: f64| poly.iter().rev().fold(0.0, |a,&k| a*x + k);
    let m = 2_000_000usize;
    let mut r = vec![]; let mut px=lo; let mut pv=ev(lo);
    for i in 1..=m {
        let x = lo + (hi-lo)*(i as f64)/(m as f64); let v = ev(x);
        if pv*v < 0.0 { let (mut l,mut rr)=(px,x);
            for _ in 0..100 { let mid=0.5*(l+rr);
                if ev(l)*ev(mid) <= 0.0 { rr=mid; } else { l=mid; } }
            r.push(0.5*(l+rr)); }
        px=x; pv=v;
    }
    r
}
/// subdivision of a graph: each edge gets a new degree-2 vertex
fn subdivide(n: usize, e: &[(usize,usize)]) -> (usize, Vec<(usize,usize)>) {
    let mut out = vec![];
    for (k,&(u,v)) in e.iter().enumerate() { out.push((u, n+k)); out.push((v, n+k)); }
    (n + e.len(), out)
}
fn main() {
    let gap = 2f64.sqrt() - 1.0; // (3,2)-biregular tree gap edge
    println!("=== (A) d=1 falsification: universal cover (3,2)-biregular, gap (0,{:.5}) ===", gap);
    // cubic graphs; their subdivisions have (3,2)-biregular universal cover
    let cubics: Vec<(&str, usize, Vec<(usize,usize)>)> = vec![
        ("K_4",      4, vec![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),
        ("K_{3,3}",  6, vec![(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]),
        ("prism",    6, vec![(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]),
        ("cube Q_3", 8, vec![(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7)]),
        ("Moebius-Kantor K_{3,3} subdiv-like / Wagner", 8,
                     vec![(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0),(0,4),(1,5),(2,6),(3,7)]),
        ("Petersen", 10, vec![(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
                              (0,5),(1,6),(2,7),(3,8),(4,9)]),
    ];
    let mut worst = f64::INFINITY; let mut worst_name = String::new();
    for (name, n, e) in cubics.iter() {
        let (sn, se) = subdivide(*n, e);
        if sn > 60 { continue; }
        let mp = matching_poly(sn, &se);
        let pf: Vec<f64> = mp.iter().map(|&c| c as f64).collect();
        let rts = roots_of(&pf, -3.0, 3.0);
        let minpos = rts.iter().cloned().map(f64::abs).filter(|&r| r>1e-7)
            .fold(f64::INFINITY, f64::min);
        let inside: Vec<f64> = rts.iter().cloned()
            .filter(|&r| r.abs()>1e-7 && r.abs()<gap-1e-7).collect();
        if minpos < worst { worst = minpos; worst_name = format!("S({})", name); }
        println!("  S({:12}) n={:3}  min|root| = {:.5}  ratio {:.3}  | in gap: {}",
                 name, sn, minpos, minpos/gap,
                 if inside.is_empty() { "NONE".into() } else { format!("{:?}", inside) });
    }
    println!("  tightest: {} at min|root| = {:.5} (gap edge {:.5})", worst_name, worst, gap);
    // long paths, for contrast: these are trees, so T = G and the conjecture is vacuous, but they
    // show how far INTO the gap a subtree eigenvalue can sit
    let pl: Vec<f64> = (2..=14).map(|m: usize| 2.0*(std::f64::consts::PI*((m as f64)/2.0).floor()
        /((m+1) as f64)).cos()).collect();
    let _ = pl;
    println!("  (for contrast, P_8 as an abstract subtree has eigenvalue {:.5}, inside the gap,",
             2.0*(4.0*std::f64::consts::PI/9.0).cos());
    println!("   so the containment is NOT a formal consequence of the path-tree argument)");
}
