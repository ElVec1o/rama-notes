// How far does universality go?  For (a,b)-biregular bipartite G with p <= q, the shifted
// polynomial g(z) = f_G(z+c), c = a+b-2, has:
//   [z^p]     = 1
//   [z^(p-1)] = p(b-2)                                  (A15)
//   [z^(p-2)] = (p/2)[(p-1)(b-2)^2 - a(b-1)]            (A16, claim)
// all independent of G.  The claim for [z^(p-2)] follows because in a biregular bipartite graph
//   m_2 = C(N,2) - p*C(a,2) - q*C(b,2),  N = pa = qb,
// two distinct edges sharing both endpoints being impossible.  Where does the graph itself first
// enter?  m_3 should depend on the number of 4-cycles, so [z^(p-3)] should NOT be universal.
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
fn binom(n:usize,k:usize)->i128{ if k>n {return 0;} let mut r=1i128; for i in 0..k { r=r*((n-i) as i128)/((i+1) as i128);} r }
fn shift(f:&Vec<i128>,c:i128)->Vec<i128>{
    let mut out=vec![0i128;f.len()];
    for (i,&fi) in f.iter().enumerate(){ if fi==0 {continue;}
        for j in 0..=i { out[j]+=fi*binom(i,j)*c.pow((i-j) as u32); } }
    norm(out) }
fn c4count(na:usize,nb:usize,e:&[(usize,usize)])->i128{
    // 4-cycles = sum over pairs of left vertices of C(common neighbours, 2)
    let mut nbr=vec![0u64;na];
    for &(u,v) in e { nbr[u]|=1u64<<(v-na); }
    let _=nb;
    let mut t=0i128;
    for i in 0..na { for j in (i+1)..na {
        let c=(nbr[i]&nbr[j]).count_ones() as usize; t+=binom(c,2); } }
    t }
fn run(name:&str,na:usize,nb:usize,e:&[(usize,usize)])->Option<(usize,usize,usize,i128,i128,i128)>{
    let n=na+nb;
    let mut da=vec![0usize;na]; let mut db=vec![0usize;nb];
    for &(u,v) in e { da[u]+=1; db[v-na]+=1; }
    let (a0,b0)=(da[0],db[0]);
    if da.iter().any(|&d|d!=a0)||db.iter().any(|&d|d!=b0){ return None; }
    let (p,a,b)=if na<=nb {(na,a0,b0)} else {(nb,b0,a0)};
    let c=(a as i128-1)+(b as i128-1);
    let cnt=mcounts(n,e);
    let mut f=vec![0i128;p+1];
    for (k,&v) in cnt.iter().enumerate(){ if k<=p { f[p-k]+= if k%2==0 {v} else {-v}; } }
    let g=shift(&norm(f),c);
    let gi=|j:usize| -> i128 { if g.len()>j {g[j]} else {0} };
    let c1=gi(p.wrapping_sub(1)); let c2=gi(p.wrapping_sub(2)); let c3=gi(p.wrapping_sub(3));
    let pred1=(p as i128)*(b as i128-2);
    let pred2=((p as i128)*((p as i128-1)*(b as i128-2).pow(2) - (a as i128)*(b as i128-1)))/2;
    let q4=c4count(na.min(nb),na.max(nb), &(if na<=nb {e.to_vec()} else {
        e.iter().map(|&(u,v)|(v-na,u+nb)).collect::<Vec<_>>() }));
    assert_eq!(c1,pred1,"A15 FAIL {}",name);
    let ok2 = p<2 || c2==pred2;
    println!("  {:22} p={:2} (a,b)=({},{})  [p-1]={:6}  [p-2]={:8} pred {:8} {}  C4={:3}  [p-3]={:10}",
        name,p,a,b,c1,c2,if p>=2 {pred2} else {0}, if ok2 {"OK"} else {"FAIL"}, q4, if p>=3 {c3} else {0});
    assert!(ok2,"A16 FAIL {}",name);
    let c4c=gi(p.wrapping_sub(4));
    if let Some(m)=C4MAP.lock().unwrap().as_mut(){ m.insert(name.to_string(),c4c); }
    Some((p,a,b,c3,q4,0))
}
use std::sync::Mutex;
static C4MAP: Mutex<Option<HashMap<String,i128>>> = Mutex::new(None);
fn x4(name:&str)->i128{ C4MAP.lock().unwrap().as_ref().and_then(|m|m.get(name).copied()).unwrap_or(0) }
fn main(){
    *C4MAP.lock().unwrap()=Some(HashMap::new());
    println!("A16:  [z^(p-2)] g == (p/2)[(p-1)(b-2)^2 - a(b-1)]\n");
    for (na,nb) in [(2,2),(2,3),(3,3),(3,4),(3,5),(3,6),(4,4),(4,5),(4,6),(5,5),(4,8),(2,5),(2,7)] {
        let e:Vec<_>=(0..na).flat_map(|u|(0..nb).map(move|v|(u,na+v))).collect();
        run(&format!("K_{{{},{}}}",na,nb),na,nb,&e); }
    // (2,2)-biregular on p=q=4: C_8 versus 2 disjoint C_4 -- same (p,a,b), different C_4 count
    let mut groups:Vec<((usize,usize,usize),Vec<(String,i128,i128)>)>=vec![];
    let mut record=|name:String,na:usize,nb:usize,e:Vec<(usize,usize)>,groups:&mut Vec<((usize,usize,usize),Vec<(String,i128,i128)>)>|{
        if let Some((p,a,b,c3,q4,_))=run(&name,na,nb,&e){
            if let Some(g)=groups.iter_mut().find(|(k,_)|*k==(p,a,b)) { g.1.push((name,c3,q4)); }
            else { groups.push(((p,a,b),vec![(name,c3,q4)])); } } };
    { let e:Vec<_>=(0..4).flat_map(|i|vec![(i,4+i),(i,4+(i+1)%4)]).collect();
      record("C_8".into(),4,4,e,&mut groups); }
    { let mut e=vec![]; for i in 0..2 { e.push((2*i,4+2*i)); e.push((2*i,4+2*i+1));
        e.push((2*i+1,4+2*i)); e.push((2*i+1,4+2*i+1)); }
      record("C_4 + C_4".into(),4,4,e,&mut groups); }
    { let e:Vec<_>=(0..6).flat_map(|i|vec![(i,6+i),(i,6+(i+1)%6)]).collect();
      record("C_12".into(),6,6,e,&mut groups); }
    { let mut e=vec![]; for i in 0..3 { e.push((2*i,6+2*i)); e.push((2*i,6+2*i+1));
        e.push((2*i+1,6+2*i)); e.push((2*i+1,6+2*i+1)); }
      record("3 x C_4".into(),6,6,e,&mut groups); }
    { let mut e=vec![]; for i in 0..2 { e.push((i,6+i)); e.push((i,6+(i+1)%2)); }
      for i in 0..4 { e.push((2+i,6+2+i)); e.push((2+i,6+2+(i+1)%4)); }
      record("C_4 + C_8".into(),6,6,e,&mut groups); }
    // --- b >= 3, same (p,a,b), different structure ---
    { // 2 disjoint copies of K_{3,3}: 6+6, 3-regular
      let mut e=vec![]; for blk in 0..2 { for u in 0..3 { for v in 0..3 {
        e.push((3*blk+u, 6+3*blk+v)); } } }
      record("2 x K_{3,3}".into(),6,6,e,&mut groups); }
    { // circulant: left i ~ right {i,i+1,i+2} mod 6, 3-regular bipartite, connected
      let e:Vec<_>=(0..6usize).flat_map(|i|(0..3usize).map(move|k|(i,6+(i+k)%6))).collect();
      record("circ6[0,1,2]".into(),6,6,e,&mut groups); }
    { // Heawood graph = incidence graph of the Fano plane: 7+7, 3-regular, girth 6 so no C_4
      let e:Vec<_>=(0..7usize).flat_map(|i|[0usize,1,3].iter().map(move|&k|(i,7+(i+k)%7)).collect::<Vec<_>>()).collect();
      record("Heawood 7+7".into(),7,7,e,&mut groups); }
    { // circulant 7+7 with {0,1,2}: 3-regular bipartite, has 4-cycles
      let e:Vec<_>=(0..7usize).flat_map(|i|(0..3usize).map(move|k|(i,7+(i+k)%7))).collect();
      record("circ7[0,1,2]".into(),7,7,e,&mut groups); }
    { // 4-regular bipartite 6+6, two structures
      let e:Vec<_>=(0..6usize).flat_map(|i|(0..4usize).map(move|k|(i,6+(i+k)%6))).collect();
      record("circ6[0,1,2,3]".into(),6,6,e,&mut groups); }
    { let e:Vec<_>=(0..6usize).flat_map(|i|[0usize,1,2,4].iter().map(move|&k|(i,6+(i+k)%6)).collect::<Vec<_>>()).collect();
      record("circ6[0,1,2,4]".into(),6,6,e,&mut groups); }
    println!("\nSame (p,a,b), differing 4-cycle count -- does [z^(p-3)] stay constant?");
    for ((p,a,b),v) in &groups {
        if v.len()<2 {continue;}
        let all_same = v.iter().all(|x|x.1==v[0].1);
        println!("  (p,a,b)=({},{},{}):",p,a,b);
        for (n,c3,q4) in v { println!("      {:14} C4={:3}  [z^(p-3)]={:8}  [z^(p-4)]={}",n,q4,c3,x4(n)); }
        println!("      => [z^(p-3)] {}", if all_same {"CONSTANT (universal)"} else {"VARIES with the graph"});
        let all4 = v.iter().all(|x|x4(&x.0)==x4(&v[0].0));
        println!("      => [z^(p-4)] {}", if all4 {"CONSTANT (universal)"} else {"VARIES with the graph"}); }
}
