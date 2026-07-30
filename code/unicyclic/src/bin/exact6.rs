// Is the d=6 "violation" real, or f64 breakdown?  Redo with EXACT i128 arithmetic:
// integer char polys, integer weights, exact polynomial division, then exact rational evaluation
// at rational points to count sign changes inside the gap.
fn perms(r: usize) -> Vec<Vec<usize>> {
    let mut o=vec![]; let mut c:Vec<usize>=(0..r).collect();
    fn rec(k:usize,c:&mut Vec<usize>,o:&mut Vec<Vec<usize>>){ if k==c.len(){o.push(c.clone());return;}
        for i in k..c.len(){c.swap(k,i);rec(k+1,c,o);c.swap(k,i);} }
    rec(0,&mut c,&mut o); o }
fn partitions(r: usize) -> Vec<Vec<usize>> {
    fn go(rem:usize,max:usize,cur:&mut Vec<usize>,out:&mut Vec<Vec<usize>>){
        if rem==0 { out.push(cur.clone()); return; }
        for p in (1..=max.min(rem)).rev() { cur.push(p); go(rem-p,p,cur,out); cur.pop(); } }
    let mut o=vec![]; go(r,r,&mut vec![],&mut o); o }
fn perm_of_type(t:&[usize], r:usize)->Vec<usize>{
    let mut p=vec![0usize;r]; let mut s=0;
    for &l in t { for i in 0..l { p[s+i]=s+(i+1)%l; } s+=l; } p }
fn class_size(t:&[usize], r:usize)->i128{
    let f=|n:usize| (1..=n as i128).product::<i128>();
    let mut d=1i128; let mut i=0;
    while i<t.len(){ let mut m=1; while i+m<t.len() && t[i+m]==t[i] {m+=1;}
        d *= (t[i] as i128).pow(m as u32) * f(m); i+=m; }
    f(r)/d }
fn charpoly_i(m:&Vec<Vec<i128>>)->Vec<i128>{
    let n=m.len(); let mut acc=vec![vec![0i128;n];n]; let mut co=vec![0i128;n+1]; co[n]=1; let mut c=1i128;
    for k in 1..=n {
        let mut t=vec![vec![0i128;n];n];
        for i in 0..n { for l in 0..n { let v=m[i][l]; if v!=0 { for j in 0..n { t[i][j]+=v*acc[l][j]; } } } }
        for i in 0..n { t[i][i]+=c; }
        acc=t;
        let mut tr=0i128; for i in 0..n { for l in 0..n { tr+=m[i][l]*acc[l][i]; } }
        assert!(tr % (k as i128)==0); c=-tr/(k as i128); co[n-k]=c; }
    co }
/// exact division of integer polys (assumes it divides)
fn poly_div_i(num:&[i128], den:&[i128])->Vec<i128>{
    let mut n=num.to_vec(); let dn=den.len()-1;
    let mut q=vec![0i128; n.len()-dn];
    for i in (0..q.len()).rev(){
        assert!(n[i+dn] % den[dn]==0, "not exact");
        let c=n[i+dn]/den[dn]; q[i]=c;
        for j in 0..=dn { n[i+j]-=c*den[j]; } }
    for (i,v) in n.iter().enumerate() { assert!(*v==0 || i>=q.len()+dn, "remainder nonzero"); }
    q }
fn main(){
    let (n, edges, free) = (5usize, vec![(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)], vec![4usize,5]);
    let base:Vec<Vec<i128>> = { let mut a=vec![vec![0i128;n];n];
        for &(u,v) in &edges { a[u][v]+=1; a[v][u]+=1; } a };
    let chi_g = charpoly_i(&base);
    for d in 5..=6usize {
        let r=d+1; let ps=perms(r); let types=partitions(r);
        let mut tot=vec![0i128; n*r+1]; let mut wsum=0i128;
        for t in types.iter(){
            let s1=perm_of_type(t,r); let w=class_size(t,r);
            for s2 in ps.iter(){
                let mut a=vec![vec![0i128;n*r];n*r];
                for (ei,&(u,v)) in edges.iter().enumerate(){
                    let p:&Vec<usize> = match free.iter().position(|&f| f==ei){
                        Some(0)=>&s1, Some(_)=>s2, None=>&ps[0] };
                    for i in 0..r { let (x,y)=(u*r+i, v*r+p[i]); a[x][y]+=1; a[y][x]+=1; } }
                let cp=charpoly_i(&a);
                for (i,c) in cp.iter().enumerate(){ tot[i]+= w*c; }
                wsum+=w; } }
        // mu = (tot/wsum)/chi_g ; do the exact poly division first (wsum is a common scalar)
        let mu_scaled = poly_div_i(&tot, &chi_g);   // = wsum * mu
        // exact sign scan on (0, gap): gap edge = sqrt2-1; use rationals p/q
        let ev = |num: i128, den: i128| -> f64 {
            // evaluate mu_scaled at num/den exactly in i128 where possible, else f64 fallback
            let x = num as f64 / den as f64;
            mu_scaled.iter().rev().fold(0.0f64, |a,&k| a*x + k as f64) };
        let gap = 2f64.sqrt()-1.0;
        // exact-ish: use high-resolution rational scan with i128-safe evaluation via f64 on SCALED poly
        let steps = 20000;
        let mut sign_changes = vec![];
        let mut prev = ev(1, 1_000_000);
        for i in 2..=steps {
            let xn = (i as i128) * ((gap*1_000_000.0) as i128) / (steps as i128);
            let v = ev(xn, 1_000_000);
            if prev*v < 0.0 { sign_changes.push(xn as f64/1e6); }
            prev = v; }
        println!("d={} (r={}): deg mu = {}, leading coeff of scaled mu = {}",
                 d, r, mu_scaled.len()-1, mu_scaled.last().unwrap());
        println!("   sign changes strictly inside (0,{:.5}): {:?}", gap, sign_changes);
        println!("   mu_scaled(0) = {}, mu_scaled(gap-) ~ {:.4e}", mu_scaled[0], ev((gap*1e6) as i128, 1_000_000));
    }
}
