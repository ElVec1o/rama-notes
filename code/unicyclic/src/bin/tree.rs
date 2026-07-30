// The conjectured interval [-2 sqrt(m)], m=(a-1)(b-1), IS the (a,b)-biregular tree spectrum
// transported: the band edges (s -+ t)^2 minus the centre s^2+t^2 are -+2st = -+2 sqrt(m).
// Question: how much of it do finite graphs use, and is the LOWER edge ever approached?
// Second moment is universal: sum rho^2 = p[(b-2)^2 + a(b-1)], so the bulk fill fraction
// (mean square)/(4m) is graph-independent.  Only the extremes can vary.
// HARD CAP at 18 vertices: the matching DP is memoized over vertex subsets.
use std::collections::HashMap;
fn norm(mut p:Vec<i128>)->Vec<i128>{ while p.len()>1 && *p.last().unwrap()==0 {p.pop();} p }
fn add(a:&Vec<i128>,b:&Vec<i128>)->Vec<i128>{ let n=a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0)+b.get(i).copied().unwrap_or(0)).collect()) }
fn mcounts(n:usize,e:&[(usize,usize)])->Vec<i128>{
    assert!(n<=18,"vertex cap");
    let mut adj=vec![0u32;n];
    for &(u,v) in e { adj[u]|=1u32<<v; adj[v]|=1u32<<u; }
    let mut memo:HashMap<u32,Vec<i128>>=HashMap::new();
    fn go(al:u32,adj:&Vec<u32>,n:usize,m:&mut HashMap<u32,Vec<i128>>)->Vec<i128>{
        if let Some(r)=m.get(&al){return r.clone();}
        let mut v=0usize; while v<n && (al>>v)&1==0 {v+=1;}
        if v==n {return vec![1];}
        let rest=al & !(1u32<<v);
        let mut res=go(rest,adj,n,m);
        let mut nb=adj[v]&rest;
        while nb!=0 { let w=nb.trailing_zeros() as usize; nb&=nb-1;
            let s=go(rest & !(1u32<<w),adj,n,m);
            let mut sh=vec![0i128;s.len()+1];
            for (i,c) in s.iter().enumerate(){sh[i+1]+=c;}
            res=add(&res,&sh); }
        m.insert(al,res.clone()); res }
    go((1u32<<n)-1,&adj,n,&mut memo) }
fn girth_bip(na:usize,e:&[(usize,usize)])->usize{
    let mut nbr=vec![0u64;na];
    for &(u,v) in e { nbr[u]|=1u64<<(v-na); }
    for i in 0..na { for j in (i+1)..na {
        if (nbr[i]&nbr[j]).count_ones()>=2 { return 4; } } }
    6 }
fn run(name:&str,na:usize,nb:usize,e:&[(usize,usize)]){
    let n=na+nb; if n>18 { println!("  {:20} SKIPPED (>{} vertices)",name,18); return; }
    let mut da=vec![0usize;na]; let mut db=vec![0usize;nb];
    for &(u,v) in e { da[u]+=1; db[v-na]+=1; }
    let (a0,b0)=(da[0],db[0]);
    if da.iter().any(|&d|d!=a0)||db.iter().any(|&d|d!=b0){ println!("  {} not biregular",name); return; }
    let (p,a,b)=if na<=nb {(na,a0,b0)} else {(nb,b0,a0)};
    let c=((a-1)+(b-1)) as f64; let m=((a-1)*(b-1)) as f64;
    let cnt=mcounts(n,e);
    let mut f=vec![0f64;p+1];
    for (k,&v) in cnt.iter().enumerate(){ if k<=p { f[p-k]+= if k%2==0 {v as f64} else {-(v as f64)}; } }
    // roots of f, then rho = y - c
    let fe=|y:f64| f.iter().rev().fold(0.0,|acc,&k| acc*y + k);
    let (lo,hi,steps)=(-1e-9f64, 4.0*m+2.0*c+40.0, 4_000_000usize);
    let mut roots:Vec<f64>=vec![]; let mut px=lo; let mut pv=fe(lo);
    for i in 1..=steps { let y=lo+(hi-lo)*(i as f64)/(steps as f64); let v=fe(y);
        if pv*v<0.0 { let (mut l,mut r)=(px,y);
            for _ in 0..80 { let mid=0.5*(l+r); if fe(l)*fe(mid)<=0.0 {r=mid;} else {l=mid;} }
            roots.push(0.5*(l+r)); }
        px=y; pv=v; }
    let rhos:Vec<f64>=roots.iter().map(|&y|y-c).collect();
    if rhos.is_empty() { println!("  {:20} no real roots found",name); return; }
    let minr=rhos.iter().cloned().fold(f64::INFINITY,f64::min);
    let maxr=rhos.iter().cloned().fold(f64::NEG_INFINITY,f64::max);
    let edge=2.0*m.sqrt();
    let ms:f64=rhos.iter().map(|r|r*r).sum::<f64>()/(rhos.len() as f64);
    let g=girth_bip(na.min(nb), &(if na<=nb {e.to_vec()} else {
        e.iter().map(|&(u,v)|(v-na,u+nb)).collect::<Vec<_>>() }));
    println!("  {:20} (a,b)=({},{}) girth{:>2}  band +-{:6.3}   min {:8.3} ({:5.1}% of lower edge)   max {:7.3} ({:5.1}%)   bulk fill {:5.1}%",
        name,a,b,g,edge,minr,100.0*minr/(-edge),maxr,100.0*maxr/edge,100.0*ms/(edge*edge));
}
fn main(){
    println!("How much of the transported tree band do finite graphs use?\n");
    for (na,nb) in [(3,3),(3,4),(4,4),(3,5),(4,5)] {
        let e:Vec<_>=(0..na).flat_map(|u|(0..nb).map(move|v|(u,na+v))).collect();
        run(&format!("K_{{{},{}}}",na,nb),na,nb,&e); }
    { let e:Vec<_>=(0..6).flat_map(|i|vec![(i,6+i),(i,6+(i+1)%6)]).collect(); run("C_12",6,6,&e); }
    { let mut e=vec![]; for i in 0..3 { for x in 0..2 { for y in 0..2 {
        e.push((2*i+x,6+2*i+y)); } } } run("3 x C_4",6,6,&e); }
    { let mut e=vec![]; for blk in 0..2 { for u in 0..3 { for v in 0..3 {
        e.push((3*blk+u,6+3*blk+v)); } } } run("2 x K_{3,3}",6,6,&e); }
    { let e:Vec<_>=(0..6usize).flat_map(|i|(0..3usize).map(move|k|(i,6+(i+k)%6))).collect();
      run("circ6[0,1,2]",6,6,&e); }
    { let e:Vec<_>=(0..7usize).flat_map(|i|[0usize,1,3].iter().map(move|&k|(i,7+(i+k)%7)).collect::<Vec<_>>()).collect();
      run("Heawood (girth 6)",7,7,&e); }
    { let e:Vec<_>=(0..7usize).flat_map(|i|(0..3usize).map(move|k|(i,7+(i+k)%7))).collect();
      run("circ7[0,1,2]",7,7,&e); }
    { // Pappus graph: incidence graph of AG(2,3), 9+9, 3-regular, girth 6
      let lines:[[usize;3];9]=[[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],
                              [0,4,8],[1,5,6],[2,3,7]];
      let e:Vec<_>=lines.iter().enumerate().flat_map(|(i,l)|l.iter().map(move|&v|(v,9+i)).collect::<Vec<_>>()).collect();
      run("Pappus (girth 6)",9,9,&e); }
}
