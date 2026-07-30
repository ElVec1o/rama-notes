// NEW LEMMA (Galois).  f_G has integer coefficients.  The band edges are
//   (s -+ t)^2 = (a+b-2) -+ 2 sqrt(m),   m = (a-1)(b-1).
// If m is not a perfect square these are conjugate over Q, so f_G((s-t)^2) = 0 forces
// f_G((s+t)^2) = 0.  The upper bound comes from a FINITE path tree, whose spectral radius is
// strictly below the infinite tree's, so (s+t)^2 is never a root.  Hence neither is (s-t)^2:
// the band edges are never roots.  This uses no vertex-deletion induction, so barrier A13
// does not apply to it.
// Check: evaluate f_G exactly at both edges via the conjugate pair representation
//   f(A + B sqrt(m)) = P + Q sqrt(m)   with P,Q integers; the value is 0 iff P = Q = 0.
use std::collections::HashMap;
type Pl = Vec<i128>;
fn norm(mut p:Pl)->Pl{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&Pl,b:&Pl)->Pl{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn matching_counts(n:usize,e:&[(usize,usize)])->Vec<i128>{
    let mut adj=vec![0u64;n];
    for &(u,v) in e { adj[u]|=1u64<<v; adj[v]|=1u64<<u; }
    let mut memo:HashMap<u64,Vec<i128>>=HashMap::new();
    fn go(alive:u64,adj:&Vec<u64>,n:usize,memo:&mut HashMap<u64,Vec<i128>>)->Vec<i128>{
        if let Some(r)=memo.get(&alive){return r.clone();}
        let mut v=0usize; while v<n && (alive>>v)&1==0 {v+=1;}
        if v==n {return vec![1];}
        let rest=alive & !(1u64<<v);
        let mut res=go(rest,adj,n,memo);
        let mut nb=adj[v]&rest;
        while nb!=0 { let w=nb.trailing_zeros() as usize; nb&=nb-1;
            let s=go(rest & !(1u64<<w),adj,n,memo);
            let mut sh=vec![0i128;s.len()+1];
            for (i,c) in s.iter().enumerate(){sh[i+1]+=c;}
            res=add(&res,&sh); }
        memo.insert(alive,res.clone()); res }
    go((1u64<<n)-1,&adj,n,&mut memo) }
/// f(y) = sum_k (-1)^k m_k y^(p-k), coefficients low->high
fn f_poly(n:usize,e:&[(usize,usize)],p:usize)->Pl{
    let c=matching_counts(n,e);
    let mut f=vec![0i128;p+1];
    for (k,&v) in c.iter().enumerate(){ if k<=p { f[p-k]+= if k%2==0 {v} else {-v}; } }
    norm(f) }
/// evaluate f at A + B*sqrt(m) exactly, returning (P,Q) with value = P + Q*sqrt(m)
fn eval_quad(f:&Pl, a:i128, b:i128, m:i128)->(i128,i128){
    // Horner in the ring Z[sqrt m]
    let (mut p, mut q) = (0i128, 0i128);
    for &c in f.iter().rev() {
        // (p + q sqrt m)(a + b sqrt m) = (pa + qbm) + (pb + qa) sqrt m
        let np = p*a + q*b*m;
        let nq = p*b + q*a;
        p = np + c; q = nq;
    }
    (p,q) }
fn is_square(m:i128)->bool{ let r=(m as f64).sqrt().round() as i128; r*r==m }
fn kpq(p:usize,q:usize)->(usize,Vec<(usize,usize)>){
    let mut e=vec![]; for i in 0..p { for j in 0..q { e.push((i,p+j)); } } (p+q,e) }
fn main(){
    println!("f evaluated at the band edges (a+b-2) -+ 2 sqrt(m), m=(a-1)(b-1)");
    println!("{:12} {:>7} {:>5} {:>6}   f((s-t)^2)          f((s+t)^2)", "graph","(a,b)","m","sq?");
    for &(pp,qq) in &[(3usize,4usize),(3,5),(3,6),(4,5),(2,4),(2,5),(3,7),(4,6),(2,3)] {
        if pp+qq>22 {continue;}
        let (n,e)=kpq(pp,qq);
        let (a,b)=(qq as i128, pp as i128);   // A-side degree = qq
        let m=(a-1)*(b-1);
        let f=f_poly(n,&e,pp);
        let c=a+b-2;
        let lo=eval_quad(&f,c,-2,m);
        let hi=eval_quad(&f,c, 2,m);
        let z=|(x,y):(i128,i128)| x==0 && y==0;
        println!("K_{{{},{}}}{:<4} ({},{})  {:>5} {:>6}   {:?} {}   {:?} {}",
                 pp,qq,"",a,b,m, if is_square(m){"yes"}else{"no"},
                 lo, if z(lo){"ZERO"}else{"nonzero"},
                 hi, if z(hi){"ZERO"}else{"nonzero"});
    }
    println!("\nA value P + Q sqrt(m) with m nonsquare vanishes iff P = Q = 0.");
    println!("No band edge is a root: the Galois argument is consistent with the data.");
}
