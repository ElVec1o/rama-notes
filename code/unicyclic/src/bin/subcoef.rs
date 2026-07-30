// A15.  G is (a,b)-biregular bipartite, parts of sizes p <= q, degree a on the p-side and b on the
// q-side, so p*a = q*b and a >= b.  Let f_G be defined by mu_G(x) = x^(q-p) f_G(x^2), and let
// g(z) = f_G(z + c) with c = (a-1) + (b-1).  CLAIM: [z^{p-1}] g = p*(b-2), exactly.
// Consequence: a matching polynomial of degree p has zero coefficient at z^{p-1}, so g can be a
// matching polynomial only if b = 2.  With Yan-Yeh (b=2 => g = mu_H) this is an iff.
// Second consequence: the roots of g have mean -(b-2), so they are centred at 0 exactly when b=2.
use std::collections::HashMap;
fn norm(mut p:Vec<i128>)->Vec<i128>{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&Vec<i128>,b:&Vec<i128>)->Vec<i128>{ let n=a.len().max(b.len());
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
fn binom(n:usize,k:usize)->i128{ let mut r=1i128; for i in 0..k { r=r*((n-i) as i128)/((i+1) as i128);} r }
fn shift(f:&Vec<i128>,c:i128)->Vec<i128>{
    let mut out=vec![0i128;f.len()];
    for (i,&fi) in f.iter().enumerate(){ if fi==0 {continue;}
        for j in 0..=i { out[j]+=fi*binom(i,j)*c.pow((i-j) as u32); } }
    norm(out) }
/// bipartite graph on parts [0,na) and [na, na+nb)
fn run(name:&str, na:usize, nb:usize, e:&[(usize,usize)]) {
    let n=na+nb;
    let mut da=vec![0usize;na]; let mut db=vec![0usize;nb];
    for &(u,v) in e { da[u]+=1; db[v-na]+=1; }
    let (a0,b0)=(da[0],db[0]);
    if da.iter().any(|&d|d!=a0)||db.iter().any(|&d|d!=b0){ println!("  {:24} NOT biregular",name); return; }
    // orient so p <= q, with degree a on the p-side
    let (p,a,b) = if na<=nb {(na,a0,b0)} else {(nb,b0,a0)};
    let c=(a as i128-1)+(b as i128-1);
    let cnt=mcounts(n,e);
    let mut f=vec![0i128;p+1];
    for (k,&v) in cnt.iter().enumerate(){ if k<=p { f[p-k]+= if k%2==0 {v} else {-v}; } }
    let f=norm(f);
    let g=shift(&f,c);
    let got = if g.len()>=2 { g[g.len()-2] } else { 0 };
    let pred = (p as i128)*(b as i128-2);
    // mean of the roots of g
    let mean = -(got as f64)/(p as f64);
    println!("  {:24} p={:2} (a,b)=({},{})  [z^(p-1)]g = {:5}   p(b-2) = {:5}  {}   mean root {:+.3}",
        name,p,a,b,got,pred, if got==pred {"OK"} else {"FAIL"}, mean);
    assert_eq!(got,pred,"A15 FAILED on {}",name);
}
fn main(){
    println!("A15:  [z^(p-1)] f_G(z + a + b - 2)  ==  p*(b-2)\n");
    // complete bipartite K_{na,nb}
    for (na,nb) in [(2,2),(2,3),(2,5),(3,3),(3,4),(3,5),(3,6),(4,4),(4,5),(4,6),(5,5),(2,7),(4,8)] {
        let e:Vec<_> = (0..na).flat_map(|u|(0..nb).map(move|v|(u,na+v))).collect();
        run(&format!("K_{{{},{}}}",na,nb),na,nb,&e); }
    // cycles C_{2n} = (2,2)-biregular
    for m in [3usize,4,5,6] {
        let e:Vec<_> = (0..m).flat_map(|i|vec![(i,m+i),(i,m+(i+1)%m)]).collect();
        run(&format!("C_{}",2*m),m,m,&e); }
    // subdivisions of regular graphs: (D,2)-biregular
    { // S(K_4): 4 vertices deg 3, 6 edge-vertices deg 2
      let ed=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)];
      let e:Vec<_> = ed.iter().enumerate().flat_map(|(i,&(u,v))|vec![(u,4+i),(v,4+i)]).collect();
      run("S(K_4)",4,6,&e); }
    { // S(Petersen) too big; S(K_{3,3}): 6 vertices deg 3, 9 edge-vertices
      let ed:Vec<_>=(0..3).flat_map(|u|(0..3).map(move|v|(u,3+v))).collect();
      let e:Vec<_> = ed.iter().enumerate().flat_map(|(i,&(u,v))|vec![(u,6+i),(v,6+i)]).collect();
      run("S(K_{3,3})",6,9,&e); }
    // incidence graphs of hypergraphs (the four from before)
    let hs:Vec<(&str,usize,Vec<Vec<usize>>)> = vec![
      ("inc (2,3) 6pt/4tri",6,vec![vec![0,1,2],vec![0,3,4],vec![1,3,5],vec![2,4,5]]),
      ("inc Fano (3,3)",7,vec![vec![0,1,2],vec![0,3,4],vec![0,5,6],vec![1,3,5],vec![1,4,6],vec![2,3,6],vec![2,4,5]]),
      ("inc (2,4) 8pt/4quad",8,vec![vec![0,1,2,3],vec![0,1,4,5],vec![2,4,6,7],vec![3,5,6,7]]),
      ("inc (3,4) 8pt/6quad",8,vec![vec![0,1,2,3],vec![0,1,4,5],vec![2,3,4,5],vec![0,2,6,7],vec![1,3,6,7],vec![4,5,6,7]]),
    ];
    for (name,nv,edges) in hs {
        let e:Vec<_>=edges.iter().enumerate().flat_map(|(i,b)|b.iter().map(move|&v|(v,nv+i)).collect::<Vec<_>>()).collect();
        run(name,nv,edges.len(),&e); }
    println!("\nAll checks passed.  g has zero subleading coefficient iff b = min(a,b) = 2.");
}
