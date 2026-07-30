// Push d higher on K_{2,3} using mu_{d,G} = E[chi_H]/chi_G over (d+1)-covers (Hall-Puder-Sawin):
// char polys are polynomial time per cover, unlike matching polynomials.  Plus conjugacy reduction:
// the cover's isomorphism type depends on (sigma_1, sigma_2) only up to simultaneous conjugation,
// so sigma_1 may be fixed to one representative per cycle type, weighted by class size.
fn perms(r: usize) -> Vec<Vec<usize>> {
    let mut o=vec![]; let mut c:Vec<usize>=(0..r).collect();
    fn rec(k:usize,c:&mut Vec<usize>,o:&mut Vec<Vec<usize>>){ if k==c.len(){o.push(c.clone());return;}
        for i in k..c.len(){c.swap(k,i);rec(k+1,c,o);c.swap(k,i);} }
    rec(0,&mut c,&mut o); o }
fn partitions(r: usize) -> Vec<Vec<usize>> {
    fn go(rem: usize, max: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if rem == 0 { out.push(cur.clone()); return; }
        for p in (1..=max.min(rem)).rev() { cur.push(p); go(rem-p, p, cur, out); cur.pop(); } }
    let mut o=vec![]; go(r, r, &mut vec![], &mut o); o }
fn perm_of_type(t: &[usize], r: usize) -> Vec<usize> {
    let mut p = vec![0usize; r]; let mut s = 0;
    for &len in t { for i in 0..len { p[s+i] = s + (i+1) % len; } s += len; }
    p }
fn class_size(t: &[usize], r: usize) -> f64 {
    let fact = |n: usize| (1..=n).fold(1f64, |a,b| a*b as f64);
    let mut d = 1f64; let mut i = 0;
    while i < t.len() { let mut m = 1; while i+m < t.len() && t[i+m]==t[i] { m += 1; }
        d *= (t[i] as f64).powi(m as i32) * fact(m); i += m; }
    fact(r) / d }
fn charpoly(m: &Vec<Vec<f64>>) -> Vec<f64> {
    let n = m.len();
    let mut acc = vec![vec![0f64;n];n]; let mut co = vec![0f64;n+1]; co[n]=1.0; let mut c=1f64;
    for k in 1..=n {
        let mut t = vec![vec![0f64;n];n];
        for i in 0..n { for l in 0..n { let v=m[i][l]; if v!=0.0 { for j in 0..n { t[i][j]+=v*acc[l][j]; } } } }
        for i in 0..n { t[i][i]+=c; }
        acc = t;
        let mut tr=0f64; for i in 0..n { for l in 0..n { tr += m[i][l]*acc[l][i]; } }
        c = -tr/(k as f64); co[n-k]=c;
    }
    co }
fn poly_div(num: &[f64], den: &[f64]) -> Vec<f64> {
    let mut n = num.to_vec(); let dn = den.len()-1;
    let mut q = vec![0f64; n.len()-dn];
    for i in (0..q.len()).rev() {
        let c = n[i+dn]/den[dn]; q[i]=c;
        for j in 0..=dn { n[i+j] -= c*den[j]; } }
    q }
fn main() {
    // K_{2,3}: parts {0,1},{2,3,4}; tree = (0,2),(0,3),(0,4),(1,2); free = (1,3),(1,4)
    let (n, edges, free) = (5usize,
        vec![(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)], vec![4usize,5]);
    let gap = 2f64.sqrt() - 1.0;
    let base: Vec<Vec<f64>> = { let mut a = vec![vec![0f64;n];n];
        for &(u,v) in &edges { a[u][v]+=1.0; a[v][u]+=1.0; } a };
    let chi_g = charpoly(&base);
    println!("K_{{2,3}}: gap (0,{:.5}); mu_d via E[chi_H]/chi_G over (d+1)-covers", gap);
    for d in 1..=6usize {
        let r = d + 1;
        let ps = perms(r);
        let types = partitions(r);
        let mut tot = vec![0f64; n*r + 1]; let mut wsum = 0f64;
        for t in types.iter() {
            let s1 = perm_of_type(t, r); let w = class_size(t, r);
            for s2 in ps.iter() {
                let mut a = vec![vec![0f64; n*r]; n*r];
                for (ei,&(u,v)) in edges.iter().enumerate() {
                    let p: &Vec<usize> = match free.iter().position(|&f| f==ei) {
                        Some(0) => &s1, Some(_) => s2, None => &ps[0] };
                    for i in 0..r { let (x,y)=(u*r+i, v*r+p[i]); a[x][y]+=1.0; a[y][x]+=1.0; } }
                let cp = charpoly(&a);
                for (i,c) in cp.iter().enumerate() { tot[i] += w * c; }
                wsum += w;
            }
        }
        let avg: Vec<f64> = tot.iter().map(|c| c/wsum).collect();
        let mu = poly_div(&avg, &chi_g);
        let ev = |x: f64| mu.iter().rev().fold(0.0, |a,&k| a*x + k);
        let (lo,hi,m)=(-3.0f64,3.0f64,1_500_000usize);
        let mut rts=vec![]; let mut px=lo; let mut pv=ev(lo);
        for i in 1..=m { let x=lo+(hi-lo)*(i as f64)/(m as f64); let v=ev(x);
            if pv*v<0.0 { let (mut l,mut rr)=(px,x);
                for _ in 0..100 { let mid=0.5*(l+rr); if ev(l)*ev(mid)<=0.0 {rr=mid;} else {l=mid;} }
                rts.push(0.5*(l+rr)); } px=x; pv=v; }
        let minpos = rts.iter().cloned().map(f64::abs).filter(|&x| x>1e-6)
            .fold(f64::INFINITY, f64::min);
        let viol: Vec<f64> = rts.iter().cloned()
            .filter(|&x| x.abs()>1e-6 && x.abs()<gap-1e-6).collect();
        println!("  d={}  (r={}, deg mu={})  min|root| = {:.6}  ratio {:.4}  | in gap: {}",
                 d, r, mu.len()-1, minpos, minpos/gap,
                 if viol.is_empty() { "NONE".into() } else { format!("{:?}", viol) });
    }
}
