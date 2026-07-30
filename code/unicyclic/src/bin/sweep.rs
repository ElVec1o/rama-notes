// Falsification sweep for: roots of mu_{d,G} lie in spec(T), T = universal cover.
// Test bed: biregular bipartite graphs, where spec(T) is known exactly for the (a,b)-biregular tree,
//   spec = {0} u +-[ |s-t| , s+t ],  s = sqrt(a-1), t = sqrt(b-1),
// so the gap is (0, |s-t|).  Also report the SMALLEST nonzero |root| against the gap edge: if the
// conjecture is tight the ratio approaches 1, if it is loose the bound is uninteresting.
fn perms(r: usize) -> Vec<Vec<usize>> {
    let mut o = vec![]; let mut c: Vec<usize> = (0..r).collect();
    fn rec(k: usize, c: &mut Vec<usize>, o: &mut Vec<Vec<usize>>) {
        if k == c.len() { o.push(c.clone()); return; }
        for i in k..c.len() { c.swap(k, i); rec(k+1, c, o); c.swap(k, i); } }
    rec(0, &mut c, &mut o); o
}
fn matching_poly(n: usize, e: &[(usize, usize)]) -> Vec<i128> {
    let mut cnt = vec![0i128; n/2 + 2];
    fn rec(i: usize, used: u128, k: usize, e: &[(usize,usize)], c: &mut Vec<i128>) {
        c[k] += 1;
        for j in i..e.len() { let (u,v) = e[j]; let b = (1u128<<u)|(1u128<<v);
            if used & b == 0 { rec(j+1, used|b, k+1, e, c); } } }
    rec(0, 0, 0, e, &mut cnt);
    let mut p = vec![0i128; n+1];
    for (k,&c) in cnt.iter().enumerate() { if 2*k <= n { p[n-2*k] += if k%2==0 {c} else {-c}; } }
    p
}
/// complete bipartite K_{p,q}
fn kpq(p: usize, q: usize) -> (usize, Vec<(usize,usize)>) {
    let mut e = vec![]; for i in 0..p { for j in 0..q { e.push((i, p+j)); } }
    (p+q, e)
}
/// subdivision of K_4: 4 branch vertices + 6 subdivision vertices -> (3,2)-biregular
fn sub_k4() -> (usize, Vec<(usize,usize)>) {
    let pairs = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)];
    let mut e = vec![];
    for (k,&(u,v)) in pairs.iter().enumerate() { e.push((u, 4+k)); e.push((v, 4+k)); }
    (10, e)
}
/// spanning tree by BFS; returns the indices of the non-tree edges
fn free_edges(n: usize, e: &[(usize,usize)]) -> Vec<usize> {
    let mut par = (0..n).collect::<Vec<_>>();
    fn find(p: &mut Vec<usize>, x: usize) -> usize { if p[x]!=x { let r=find(p,p[x]); p[x]=r; } p[x] }
    let mut free = vec![];
    for (i,&(u,v)) in e.iter().enumerate() {
        let (a,b) = (find(&mut par,u), find(&mut par,v));
        if a==b { free.push(i); } else { par[a]=b; }
    }
    free
}
fn main() {
    // (name, n, edges, degrees (a,b), dmax)
    let mut ts: Vec<(String, usize, Vec<(usize,usize)>, (f64,f64), usize)> = vec![];
    for &(p,q,dm) in &[(2usize,3usize,4usize),(2,4,3),(2,5,3),(3,4,2),(3,5,2)] {
        let (n,e) = kpq(p,q);
        ts.push((format!("K_{{{},{}}}", p, q), n, e, (q as f64, p as f64), dm));
    }
    { let (n,e) = sub_k4(); ts.push(("subdivision of K_4".into(), n, e, (3.0,2.0), 2)); }

    for (name, n, e, (a,b), dmax) in ts.iter() {
        let (s,t) = ((a-1.0).sqrt(), (b-1.0).sqrt());
        let gap = (s-t).abs();
        let free = free_edges(*n, e);
        println!("=== {:20} b_1={}  ({},{})-biregular  gap = (0,{:.5}) ===",
                 name, free.len(), a, b, gap);
        if gap < 1e-9 { println!("    regular: no gap, nothing to test\n"); continue; }
        for d in 1..=*dmax {
            let ps = perms(d);
            let mut sel = vec![0usize; free.len()];
            let mut tot = vec![0i128; n*d + 1]; let mut cnt = 0i128;
            loop {
                let mut le = vec![];
                for (ei,&(u,v)) in e.iter().enumerate() {
                    let p: &Vec<usize> = match free.iter().position(|&f| f==ei) {
                        Some(k) => &ps[sel[k]], None => &ps[0] };
                    for i in 0..d { le.push((u*d+i, v*d+p[i])); }
                }
                for (i,c) in matching_poly(n*d, &le).iter().enumerate() { tot[i] += c; }
                cnt += 1;
                let mut k = 0;
                loop { if k==free.len() { break; } sel[k]+=1;
                    if sel[k] < ps.len() { break; } sel[k]=0; k+=1; }
                if k==free.len() { break; }
            }
            let poly: Vec<f64> = tot.iter().map(|&c| c as f64/cnt as f64).collect();
            let ev = |x: f64| poly.iter().rev().fold(0.0, |acc,&k| acc*x + k);
            let (lo,hi,m) = (-4.0f64, 4.0f64, 800_000usize);
            let mut roots = vec![]; let mut px=lo; let mut pv=ev(lo);
            for i in 1..=m {
                let x = lo + (hi-lo)*(i as f64)/(m as f64); let v = ev(x);
                if pv*v < 0.0 { let (mut l,mut r)=(px,x);
                    for _ in 0..100 { let mid=0.5*(l+r);
                        if ev(l)*ev(mid) <= 0.0 { r=mid; } else { l=mid; } }
                    roots.push(0.5*(l+r)); }
                px=x; pv=v;
            }
            let viol: Vec<f64> = roots.iter().cloned()
                .filter(|&r| r.abs() > 1e-6 && r.abs() < gap - 1e-6).collect();
            let minpos = roots.iter().cloned().map(f64::abs)
                .filter(|&r| r > 1e-6).fold(f64::INFINITY, f64::min);
            println!("   d={}  {:3} roots | min |root| = {:.5}  (gap edge {:.5}, ratio {:.3}) | in gap: {}",
                     d, roots.len(), minpos, gap, minpos/gap,
                     if viol.is_empty() { "NONE".into() } else { format!("{:?}", viol) });
        }
        println!();
    }
}
