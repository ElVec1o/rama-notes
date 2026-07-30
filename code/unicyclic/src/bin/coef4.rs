// [z^(p-4)] g  for (a,b)-biregular bipartite G,  g(z) = f_G(z+c),  c = a+b-2.
//
// Claim under test:   m_4 = U_4(p,a,b) + C_4(G)     (lambda = +1)
//               =>    [z^(p-4)] g = U(p,a,b) + C_4(G).
//
// The proof counts independent 4-sets of the conflict graph L (= line graph of G) by
// inclusion-exclusion over edge subsets:
//     m_k = sum_H (-1)^{e(H)} * #{subgraphs of L isomorphic to H} * C(N - v(H), k - v(H))
// H ranging over iso types with <= k vertices and no isolated vertex.  This program
// ALSO brute-forces every individual subgraph count in L and compares it with the
// claimed closed form, so the proof is checked step by step, not just end to end.

use std::collections::HashMap;

fn norm(mut p: Vec<i128>) -> Vec<i128> { while p.len() > 1 && *p.last().unwrap() == 0 { p.pop(); } p }
fn addp(a: &Vec<i128>, b: &Vec<i128>) -> Vec<i128> {
    let n = a.len().max(b.len());
    norm((0..n).map(|i| a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0)).collect())
}
/// matching counts m_0, m_1, m_2, ... of the graph on n vertices with edge list e
fn mcounts(n: usize, e: &[(usize, usize)]) -> Vec<i128> {
    let mut adj = vec![0u64; n];
    for &(u, v) in e { adj[u] |= 1u64 << v; adj[v] |= 1u64 << u; }
    let mut memo: HashMap<u64, Vec<i128>> = HashMap::new();
    fn go(al: u64, adj: &Vec<u64>, n: usize, m: &mut HashMap<u64, Vec<i128>>) -> Vec<i128> {
        if let Some(r) = m.get(&al) { return r.clone(); }
        let mut v = 0usize; while v < n && (al >> v) & 1 == 0 { v += 1; }
        if v == n { return vec![1]; }
        let rest = al & !(1u64 << v);
        let mut res = go(rest, adj, n, m);
        let mut nb = adj[v] & rest;
        while nb != 0 {
            let w = nb.trailing_zeros() as usize; nb &= nb - 1;
            let s = go(rest & !(1u64 << w), adj, n, m);
            let mut sh = vec![0i128; s.len() + 1];
            for (i, cc) in s.iter().enumerate() { sh[i + 1] += cc; }
            res = addp(&res, &sh);
        }
        m.insert(al, res.clone()); res
    }
    go((1u64 << n) - 1, &adj, n, &mut memo)
}
fn binom(n: i128, k: i128) -> i128 {
    if k < 0 || n < k { return 0; }
    let mut r = 1i128;
    for i in 0..k { r = r * (n - i) / (i + 1); }
    r
}
fn shift(f: &Vec<i128>, c: i128) -> Vec<i128> {
    let mut out = vec![0i128; f.len()];
    for (i, &fi) in f.iter().enumerate() {
        if fi == 0 { continue; }
        for j in 0..=i { out[j] += fi * binom(i as i128, j as i128) * c.pow((i - j) as u32); }
    }
    norm(out)
}

// ---------------------------------------------------------------- brute force in L
/// count subgraphs of L (given by adjacency bitmask) isomorphic to H (edge list on 0..vh), /aut
fn sub_count(nl: usize, adjl: &Vec<u128>, vh: usize, hedges: &[(usize, usize)], aut: i128) -> i128 {
    let mut idx = vec![0usize; vh];
    let mut total = 0i128;
    fn rec(pos: usize, vh: usize, nl: usize, adjl: &Vec<u128>, hedges: &[(usize, usize)],
           idx: &mut Vec<usize>, total: &mut i128) {
        if pos == vh { *total += 1; return; }
        'outer: for v in 0..nl {
            for i in 0..pos { if idx[i] == v { continue 'outer; } }
            idx[pos] = v;
            // check every H-edge whose both endpoints are already placed
            for &(x, y) in hedges {
                if x <= pos && y <= pos {
                    if (adjl[idx[x]] >> idx[y]) & 1 == 0 { continue 'outer; }
                }
            }
            rec(pos + 1, vh, nl, adjl, hedges, idx, total);
        }
    }
    rec(0, vh, nl, adjl, hedges, &mut idx, &mut total);
    total / aut
}

struct Res { name: String, p: i128, a: i128, b: i128, c4g: i128, m4: i128, coef4: i128 }

fn run(name: &str, na: usize, nb: usize, e: &[(usize, usize)], out: &mut Vec<Res>) {
    let n = na + nb;
    let mut da = vec![0usize; na]; let mut db = vec![0usize; nb];
    for &(u, v) in e { da[u] += 1; db[v - na] += 1; }
    let (a0, b0) = (da[0], db[0]);
    assert!(!da.iter().any(|&d| d != a0) && !db.iter().any(|&d| d != b0), "{} not biregular", name);
    // orient so that p <= q  (i.e. a >= b)
    let (p, q, a, b, la, lb): (i128, i128, i128, i128, Vec<usize>, Vec<usize>) =
        if na <= nb { (na as i128, nb as i128, a0 as i128, b0 as i128,
                       e.iter().map(|x| x.0).collect(), e.iter().map(|x| x.1 - na).collect()) }
        else        { (nb as i128, na as i128, b0 as i128, a0 as i128,
                       e.iter().map(|x| x.1 - na).collect(), e.iter().map(|x| x.0).collect()) };
    assert_eq!(p * a, q * b);
    let c = a + b - 2;
    let bn = e.len();                     // N = |E(G)| = number of L-vertices
    assert_eq!(bn as i128, p * a);
    assert!(bn <= 128, "L too big for u128 mask");

    // ---- conflict graph L on the bn edges of G
    let mut adjl = vec![0u128; bn];
    for i in 0..bn { for j in 0..bn {
        if i != j && (la[i] == la[j] || lb[i] == lb[j]) { adjl[i] |= 1u128 << j; }
    }}
    for i in 0..bn { assert_eq!(adjl[i].count_ones() as i128, c, "{}: L not c-regular", name); }

    // ---- C_4(G) = number of 2x2 all-ones submatrices
    let mut nbr = vec![0u128; p as usize];
    for i in 0..bn { nbr[la[i]] |= 1u128 << lb[i]; }
    let mut c4g = 0i128;
    for i in 0..p as usize { for j in (i + 1)..p as usize {
        c4g += binom((nbr[i] & nbr[j]).count_ones() as i128, 2);
    }}

    // ---- closed forms for the subgraph counts in L
    let nn = p * a;                                        // N
    let e1 = p * binom(a, 2) + q * binom(b, 2);            // |E(L)|
    let t  = p * binom(a, 3) + q * binom(b, 3);            // triangles
    let z  = p * binom(a, 4) + q * binom(b, 4);            // K_4
    let dd = p * binom(a, 2) * binom(a - 2, 2) + q * binom(b, 2) * binom(b - 2, 2); // diamond
    let f_k2   = e1;
    let f_p3   = nn * binom(c, 2);
    let f_k3   = t;
    let f_2k2  = binom(e1, 2) - nn * binom(c, 2);
    let f_p4   = e1 * (c - 1) * (c - 1) - 3 * t;
    let f_k13  = nn * binom(c, 3);
    let f_c4   = 3 * z + c4g;
    let f_paw  = 3 * t * (c - 2);
    let f_diam = dd;
    let f_k4   = z;

    // ---- brute force the same counts
    let b_k2   = sub_count(bn, &adjl, 2, &[(0,1)], 2);
    let b_p3   = sub_count(bn, &adjl, 3, &[(0,1),(1,2)], 2);
    let b_k3   = sub_count(bn, &adjl, 3, &[(0,1),(0,2),(1,2)], 6);
    let b_2k2  = sub_count(bn, &adjl, 4, &[(0,1),(2,3)], 8);
    let b_p4   = sub_count(bn, &adjl, 4, &[(0,1),(1,2),(2,3)], 2);
    let b_k13  = sub_count(bn, &adjl, 4, &[(0,1),(0,2),(0,3)], 6);
    let b_c4   = sub_count(bn, &adjl, 4, &[(0,1),(1,2),(2,3),(0,3)], 8);
    let b_paw  = sub_count(bn, &adjl, 4, &[(0,1),(0,2),(1,2),(0,3)], 2);
    let b_diam = sub_count(bn, &adjl, 4, &[(0,1),(0,2),(0,3),(1,2),(1,3)], 4);
    let b_k4   = sub_count(bn, &adjl, 4, &[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], 24);
    let chk = [("K_2",f_k2,b_k2),("P_3",f_p3,b_p3),("K_3",f_k3,b_k3),("2K_2",f_2k2,b_2k2),
               ("P_4",f_p4,b_p4),("K_1,3",f_k13,b_k13),("C_4",f_c4,b_c4),("paw",f_paw,b_paw),
               ("diamond",f_diam,b_diam),("K_4",f_k4,b_k4)];
    for (nm, f, bb) in chk.iter() {
        assert_eq!(f, bb, "{}: subgraph count {} closed-form {} != brute {}", name, nm, f, bb);
    }

    // ---- m_4 from inclusion-exclusion  (and its universal part U_4)
    let u4 = binom(nn,4) - e1*binom(nn-2,2) + f_p3*(nn-3) - t*(nn-3)
           + f_2k2 - f_p4 - f_k13 + 3*z + f_paw - dd + z;
    let m4_pred = u4 + c4g;

    // ---- brute force m_1..m_4 and the shifted coefficient
    let cnt = mcounts(n, e);
    let g = |k: usize| -> i128 { cnt.get(k).copied().unwrap_or(0) };
    let (m1, m2, m3, m4) = (g(1), g(2), g(3), g(4));
    assert_eq!(m1, nn, "{}: m_1", name);
    assert_eq!(m2, binom(nn,2) - e1, "{}: m_2", name);
    assert_eq!(m3, binom(nn,3) - e1*(nn-2) + nn*binom(c,2) - t, "{}: m_3", name);
    assert_eq!(m4, m4_pred, "{}: m_4 closed form {} != brute {}", name, m4_pred, m4);

    // ---- [z^(p-4)] g  brute force via polynomial shift
    let mut f = vec![0i128; p as usize + 1];
    for (k, &v) in cnt.iter().enumerate() { if (k as i128) <= p {
        f[(p - k as i128) as usize] += if k % 2 == 0 { v } else { -v }; } }
    let gg = shift(&norm(f), c);
    let coef4 = if p >= 4 { *gg.get((p - 4) as usize).unwrap_or(&0) } else { 0 };

    // ---- closed form for [z^(p-4)] g
    let m2f = binom(nn,2) - e1;
    let m3f = binom(nn,3) - e1*(nn-2) + nn*binom(c,2) - t;
    let ubig = binom(p,4)*c.pow(4) - nn*binom(p-1,3)*c.pow(3) + m2f*binom(p-2,2)*c*c
             - m3f*(p-3)*c + u4;
    let pred4 = ubig + c4g;
    if p >= 4 { assert_eq!(coef4, pred4, "{}: [z^(p-4)]g pred {} != brute {}", name, pred4, coef4); }

    // ---- FINAL COMPACT FORM (the deliverable), checked directly:
    //  U = C(p,4)(b-2)^4 - (3/2)a(b-1)(b-2)^2 C(p,3)
    //      + a(b-1)[3a(b-1)+4(b-2)^2]/12 * C(p,2)
    //      - a(b-1)[9a(b-1)+2b^2-14b+14]/24 * p
    let (bm2, bm1) = (b - 2, b - 1);
    // compact U_4 = a^4 C(p,4) - (3/2)a^3(b-1) C(p,3) + a^2(b-1)(12a+11b-19)/12 * C(p,2)
    //               - a(b-1)(12a^2+25ab-41a+6b^2-30b+30)/24 * p
    let n4 = 24*a.pow(4)*binom(p,4) - 36*a.pow(3)*bm1*binom(p,3)
           + 2*a*a*bm1*(12*a+11*b-19)*binom(p,2)
           - a*bm1*(12*a*a+25*a*b-41*a+6*b*b-30*b+30)*p;
    assert_eq!(n4 % 24, 0, "{}: compact U_4 not integral", name);
    assert_eq!(n4/24, u4, "{}: compact U_4 {} != structured U_4 {}", name, n4/24, u4);
    let num = 24*binom(p,4)*bm2.pow(4) - 36*a*bm1*bm2*bm2*binom(p,3)
            + 2*a*bm1*(3*a*bm1 + 4*bm2*bm2)*binom(p,2)
            - a*bm1*(9*a*bm1 + 2*b*b - 14*b + 14)*p;
    assert_eq!(num % 24, 0, "{}: compact U not integral", name);
    let ucompact = num / 24;
    assert_eq!(ucompact, ubig, "{}: compact U {} != structured U {}", name, ucompact, ubig);

    // ---- ladder check: [z^(p-1)], [z^(p-2)], [z^(p-3)]
    let cf = |j: i128| -> i128 { if p >= j { *gg.get((p-j) as usize).unwrap_or(&0) } else { 0 } };
    if p >= 1 { assert_eq!(cf(1), p*bm2, "{}: [z^(p-1)]", name); }
    if p >= 2 { assert_eq!(2*cf(2), 2*binom(p,2)*bm2*bm2 - a*bm1*p, "{}: [z^(p-2)]", name); }
    if p >= 3 { assert_eq!(6*cf(3), 6*binom(p,3)*bm2.pow(3) - 6*a*bm1*bm2*binom(p,2) + a*bm1*bm2*p,
                           "{}: [z^(p-3)]", name); }

    println!("  {:16} p={:2} q={:2} (a,b)=({},{})  N={:2}  C4(G)={:3} | m_4={:9} = U4 {:9} + C4  OK | [z^(p-4)]g = {:8} = U {:9} + C4  {}",
             name, p, q, a, b, nn, c4g, m4, u4, coef4, ubig, if p >= 4 { "OK" } else { "(p<4)" });
    out.push(Res{ name: name.to_string(), p, a, b, c4g, m4, coef4 });
}

fn main() {
    let mut out: Vec<Res> = vec![];
    println!("=== step-by-step: every subgraph count in L, m_2, m_3, m_4, and [z^(p-4)]g ===");

    // complete bipartite
    for (na, nb) in [(2,2),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5),(3,6),(4,4),(4,5),(4,6),(5,5),(2,7),(4,8),(5,6),(6,6),(3,9)] {
        let e: Vec<_> = (0..na).flat_map(|u| (0..nb).map(move |v| (u, na + v))).collect();
        run(&format!("K_{},{}", na, nb), na, nb, &e, &mut out);
    }
    // cycles
    { let e: Vec<_> = (0..4).flat_map(|i| vec![(i, 4 + i), (i, 4 + (i + 1) % 4)]).collect();
      run("C_8", 4, 4, &e, &mut out); }
    { let e: Vec<_> = (0..6).flat_map(|i| vec![(i, 6 + i), (i, 6 + (i + 1) % 6)]).collect();
      run("C_12", 6, 6, &e, &mut out); }
    { let e: Vec<_> = (0..5).flat_map(|i| vec![(i, 5 + i), (i, 5 + (i + 1) % 5)]).collect();
      run("C_10", 5, 5, &e, &mut out); }
    { let e: Vec<_> = (0..8).flat_map(|i| vec![(i, 8 + i), (i, 8 + (i + 1) % 8)]).collect();
      run("C_16", 8, 8, &e, &mut out); }
    // disjoint C_4's
    { let mut e = vec![]; for i in 0..2 { e.push((2*i, 4+2*i)); e.push((2*i, 4+2*i+1));
        e.push((2*i+1, 4+2*i)); e.push((2*i+1, 4+2*i+1)); }
      run("2 x C_4", 4, 4, &e, &mut out); }
    { let mut e = vec![]; for i in 0..3 { e.push((2*i, 6+2*i)); e.push((2*i, 6+2*i+1));
        e.push((2*i+1, 6+2*i)); e.push((2*i+1, 6+2*i+1)); }
      run("3 x C_4", 6, 6, &e, &mut out); }
    { let mut e = vec![]; for i in 0..4 { e.push((2*i, 8+2*i)); e.push((2*i, 8+2*i+1));
        e.push((2*i+1, 8+2*i)); e.push((2*i+1, 8+2*i+1)); }
      run("4 x C_4", 8, 8, &e, &mut out); }
    // C_4 + C_8
    { let mut e = vec![]; for i in 0..2 { e.push((i, 6 + i)); e.push((i, 6 + (i + 1) % 2)); }
      for i in 0..4 { e.push((2+i, 6+2+i)); e.push((2+i, 6+2+(i+1)%4)); }
      run("C_4 + C_8", 6, 6, &e, &mut out); }
    // C_4 + C_12  (p=8)
    { let mut e = vec![]; for i in 0..2 { e.push((i, 8 + i)); e.push((i, 8 + (i + 1) % 2)); }
      for i in 0..6 { e.push((2+i, 8+2+i)); e.push((2+i, 8+2+(i+1)%6)); }
      run("C_4 + C_12", 8, 8, &e, &mut out); }
    { let mut e = vec![]; for i in 0..4 { e.push((i, 8 + i)); e.push((i, 8 + (i + 1) % 4)); }
      for i in 0..4 { e.push((4+i, 8+4+i)); e.push((4+i, 8+4+(i+1)%4)); }
      run("C_8 + C_8", 8, 8, &e, &mut out); }
    // 3-regular 6+6
    { let mut e = vec![]; for blk in 0..2 { for u in 0..3 { for v in 0..3 {
        e.push((3*blk+u, 6+3*blk+v)); }}}
      run("2 x K_3,3", 6, 6, &e, &mut out); }
    { let e: Vec<_> = (0..6usize).flat_map(|i| (0..3usize).map(move |k| (i, 6+(i+k)%6))).collect();
      run("circ6[0,1,2]", 6, 6, &e, &mut out); }
    { let e: Vec<_> = (0..6usize).flat_map(|i| [0usize,1,3].iter().map(move |&k| (i, 6+(i+k)%6)).collect::<Vec<_>>()).collect();
      run("circ6[0,1,3]", 6, 6, &e, &mut out); }
    // 3-regular 7+7
    { let e: Vec<_> = (0..7usize).flat_map(|i| [0usize,1,3].iter().map(move |&k| (i, 7+(i+k)%7)).collect::<Vec<_>>()).collect();
      run("Heawood 7+7", 7, 7, &e, &mut out); }
    { let e: Vec<_> = (0..7usize).flat_map(|i| (0..3usize).map(move |k| (i, 7+(i+k)%7))).collect();
      run("circ7[0,1,2]", 7, 7, &e, &mut out); }
    // 4-regular 6+6, two structures
    { let e: Vec<_> = (0..6usize).flat_map(|i| (0..4usize).map(move |k| (i, 6+(i+k)%6))).collect();
      run("circ6[0,1,2,3]", 6, 6, &e, &mut out); }
    { let e: Vec<_> = (0..6usize).flat_map(|i| [0usize,1,2,4].iter().map(move |&k| (i, 6+(i+k)%6)).collect::<Vec<_>>()).collect();
      run("circ6[0,1,2,4]", 6, 6, &e, &mut out); }
    // (a,b) = (2,1): perfect matchings / p=q with a=b=1 etc.
    { let e: Vec<_> = (0..8usize).map(|i| (i, 8 + i)).collect();
      run("8 x K_2", 8, 8, &e, &mut out); }
    // a != b: 3-regular left, 2-regular right?  p=4,a=3 => N=12, q=6,b=2
    { // left i in 0..4 joined to right {i, i+1, i+2} mod 6 -> not biregular; build incidence of K_4
      // K_4's vertex-edge incidence graph: 6 edges (left, a=2) x 4 vertices (right, b=3) -> p=4,a=3,q=6,b=2
      let ed = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)];
      let mut e = vec![]; for (k,&(u,v)) in ed.iter().enumerate() { e.push((u, 4+k)); e.push((v, 4+k)); }
      run("K_4 incidence", 4, 6, &e, &mut out); }
    { // incidence graph of K_{3,3}: 9 edges, 6 vertices -> p=6,a=3 ; q=9,b=2
      let mut e = vec![]; let mut k = 0;
      for u in 0..3 { for v in 0..3 { e.push((u, 6+k)); e.push((3+v, 6+k)); k += 1; } }
      run("K_3,3 incidence", 6, 9, &e, &mut out); }
    { // Petersen graph incidence (subdivision): 10 vertices deg 3, 15 edges deg 2
      let ed: [(usize,usize);15] = [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
                                    (0,5),(1,6),(2,7),(3,8),(4,9)];
      let mut e = vec![]; for (k,&(u,v)) in ed.iter().enumerate() { e.push((u, 10+k)); e.push((v, 10+k)); }
      run("Petersen incid.", 10, 15, &e, &mut out); }
    // Cube Q3 as bipartite 4+4 3-regular
    { let mut e = vec![]; for u in 0..8usize { if (u as u32).count_ones() % 2 == 0 {
        for bit in 0..3 { let v = u ^ (1 << bit);
          let li = [0usize,3,5,6].iter().position(|&x| x == u).unwrap();
          let ri = [1usize,2,4,7].iter().position(|&x| x == v).unwrap();
          e.push((li, 4 + ri)); } } }
      run("Q_3 cube", 4, 4, &e, &mut out); }

    // ------------------------------------------------ the mandated known values
    println!("\n=== mandated known values of [z^(p-4)] g ===");
    let known = [("C_8",2i128),("2 x C_4",4),("C_12",9),("C_4 + C_8",10),("3 x C_4",12),
                 ("2 x K_3,3",-48),("circ6[0,1,2]",-60),("Heawood 7+7",-126),("circ7[0,1,2]",-119)];
    let mut allok = true;
    for (nm, want) in known.iter() {
        let r = out.iter().find(|r| &r.name == nm).expect("missing graph");
        let ok = r.coef4 == *want;
        allok &= ok;
        println!("  {:16} [z^(p-4)]g = {:6}   expected {:6}   {}", nm, r.coef4, want, if ok {"OK"} else {"*** MISMATCH ***"});
    }
    println!("\n{}", if allok { "ALL MANDATED VALUES REPRODUCED" } else { "*** FAILURE ***" });
    assert!(allok);

    // ------------------------------------------------ universality cross-check
    println!("\n=== same (p,a,b), different C_4(G): is  coef - C_4(G)  constant? ===");
    let mut groups: Vec<((i128,i128,i128), Vec<&Res>)> = vec![];
    for r in &out {
        if let Some(g) = groups.iter_mut().find(|(k,_)| *k == (r.p,r.a,r.b)) { g.1.push(r); }
        else { groups.push(((r.p,r.a,r.b), vec![r])); }
    }
    for ((p,a,b), v) in &groups {
        if v.len() < 2 { continue; }
        let differing_c4 = v.iter().any(|r| r.c4g != v[0].c4g);
        if !differing_c4 { continue; }
        println!("  (p,a,b)=({},{},{}):", p, a, b);
        for r in v { println!("      {:16} C4={:4}  m_4={:10}  m_4-C4={:10}  [z^(p-4)]g={:8}  minus C4={:8}",
                              r.name, r.c4g, r.m4, r.m4 - r.c4g, r.coef4, r.coef4 - r.c4g); }
        let ok = v.iter().all(|r| r.m4 - r.c4g == v[0].m4 - v[0].c4g)
              && v.iter().all(|r| r.coef4 - r.c4g == v[0].coef4 - v[0].c4g);
        println!("      => {}", if ok { "CONSTANT: dependence is exactly +1 * C_4(G)" } else { "*** NOT CONSTANT ***" });
        assert!(ok);
    }
    println!("\nALL CHECKS PASSED ({} named graphs)", out.len());

    // ================= randomized stress test over biregular bipartite graphs =================
    // Start from the "sequential" biregular matrix  row i -> columns {i*a+s mod q}, then apply
    // random 2x2 swaps (which preserve all row and column sums).  For each graph check every
    // subgraph count in L, m_1..m_4 (direct enumeration), and the compact U.
    println!("\n=== randomized stress test ===");
    let mut seed: u64 = 0x243F6A8885A308D3;
    let mut rng = move || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); (seed >> 33) as usize };
    let mut ntested = 0usize;
    let mut nparam = 0usize; let mut nvary = 0usize; let mut maxspread = 0i128;
    let mut params: Vec<(usize,usize,usize)> = vec![];   // (p,a,b)
    for p in 4..=12usize { for a in 1..=8usize { for b in 1..=8usize {
        if p*a % b != 0 { continue; }
        let q = p*a/b;
        if q < p || a > q || b > p { continue; }          // need p<=q, a<=q, b<=p
        if p*a > 34 { continue; }                          // keep L small enough for the O(N^4) sweep
        params.push((p,a,b));
    }}}
    for (p,a,b) in params {
        let q = p*a/b;
        nparam += 1; let mut c4seen: Vec<i128> = vec![];
        for _trial in 0..12 {
            // build sequential matrix then randomize
            let mut m = vec![vec![false; q]; p];
            for i in 0..p { for s in 0..a { m[i][(i*a+s) % q] = true; } }
            for _ in 0..400 {
                let (i,i2,j,j2) = (rng()%p, rng()%p, rng()%q, rng()%q);
                if i==i2 || j==j2 { continue; }
                if m[i][j] && m[i2][j2] && !m[i][j2] && !m[i2][j] {
                    m[i][j]=false; m[i2][j2]=false; m[i][j2]=true; m[i2][j]=true;
                }
            }
            // sanity: biregular
            for i in 0..p { assert_eq!(m[i].iter().filter(|&&x|x).count(), a); }
            for j in 0..q { assert_eq!((0..p).filter(|&i| m[i][j]).count(), b); }
            let mut cells: Vec<(usize,usize)> = vec![];
            for i in 0..p { for j in 0..q { if m[i][j] { cells.push((i,j)); } } }
            let nn = cells.len(); assert_eq!(nn, p*a);
            let mut adjl = vec![0u128; nn];
            for x in 0..nn { for y in 0..nn { if x!=y && (cells[x].0==cells[y].0 || cells[x].1==cells[y].1) { adjl[x] |= 1u128<<y; } } }
            // C_4(G)
            let mut c4g = 0i128;
            for i in 0..p { for i2 in (i+1)..p {
                let cc = (0..q).filter(|&j| m[i][j] && m[i2][j]).count() as i128; c4g += binom(cc,2); } }
            // independent k-sets of L for k=1..4 by direct enumeration
            let ind = |k: usize| -> i128 {
                let mut cnt = 0i128; let mut st = vec![0usize;k];
                fn go(pos:usize,k:usize,start:usize,nn:usize,adjl:&Vec<u128>,st:&mut Vec<usize>,cnt:&mut i128){
                    if pos==k { *cnt+=1; return; }
                    for v in start..nn {
                        if (0..pos).any(|i| (adjl[st[i]]>>v)&1==1) { continue; }
                        st[pos]=v; go(pos+1,k,v+1,nn,adjl,st,cnt);
                    }
                }
                go(0,k,0,nn,&adjl,&mut st,&mut cnt); cnt };
            let (p_,a_,b_,q_) = (p as i128, a as i128, b as i128, q as i128);
            let c = a_+b_-2; let n_ = p_*a_;
            let e1 = p_*binom(a_,2)+q_*binom(b_,2);
            let t  = p_*binom(a_,3)+q_*binom(b_,3);
            let z  = p_*binom(a_,4)+q_*binom(b_,4);
            let dd = p_*binom(a_,2)*binom(a_-2,2)+q_*binom(b_,2)*binom(b_-2,2);
            // subgraph counts, closed form vs brute
            let pairs: [(&str,i128,i128);10] = [
              ("K_2",   e1,                          sub_count(nn,&adjl,2,&[(0,1)],2)),
              ("P_3",   n_*binom(c,2),               sub_count(nn,&adjl,3,&[(0,1),(1,2)],2)),
              ("K_3",   t,                           sub_count(nn,&adjl,3,&[(0,1),(0,2),(1,2)],6)),
              ("2K_2",  binom(e1,2)-n_*binom(c,2),   sub_count(nn,&adjl,4,&[(0,1),(2,3)],8)),
              ("P_4",   e1*(c-1)*(c-1)-3*t,          sub_count(nn,&adjl,4,&[(0,1),(1,2),(2,3)],2)),
              ("K_1,3", n_*binom(c,3),               sub_count(nn,&adjl,4,&[(0,1),(0,2),(0,3)],6)),
              ("C_4",   3*z+c4g,                     sub_count(nn,&adjl,4,&[(0,1),(1,2),(2,3),(0,3)],8)),
              ("paw",   3*t*(c-2),                   sub_count(nn,&adjl,4,&[(0,1),(0,2),(1,2),(0,3)],2)),
              ("diam",  dd,                          sub_count(nn,&adjl,4,&[(0,1),(0,2),(0,3),(1,2),(1,3)],4)),
              ("K_4",   z,                           sub_count(nn,&adjl,4,&[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],24)),
            ];
            for (nm,f,bb) in pairs.iter() { assert_eq!(f,bb,"(p,a,b)=({},{},{}) {} : {} != {}",p,a,b,nm,f,bb); }
            assert_eq!(dd, 6*z, "D = 6Z identity");
            // m_1..m_4
            assert_eq!(ind(1), n_);
            assert_eq!(ind(2), binom(n_,2)-e1);
            assert_eq!(ind(3), binom(n_,3)-e1*(n_-2)+n_*binom(c,2)-t);
            let f_p3=n_*binom(c,2); let f_2k2=binom(e1,2)-f_p3; let f_p4=e1*(c-1)*(c-1)-3*t;
            let f_k13=n_*binom(c,3); let f_paw=3*t*(c-2);
            let u4 = binom(n_,4)-e1*binom(n_-2,2)+f_p3*(n_-3)-t*(n_-3)+f_2k2-f_p4-f_k13+3*z+f_paw-dd+z;
            assert_eq!(ind(4), u4+c4g, "(p,a,b)=({},{},{}) m_4 mismatch",p,a,b);
            // compact U vs structured U
            let m2f=binom(n_,2)-e1; let m3f=binom(n_,3)-e1*(n_-2)+n_*binom(c,2)-t;
            let ubig = binom(p_,4)*c.pow(4)-n_*binom(p_-1,3)*c.pow(3)+m2f*binom(p_-2,2)*c*c-m3f*(p_-3)*c+u4;
            let (bm2,bm1)=(b_-2,b_-1);
            let n4 = 24*a_.pow(4)*binom(p_,4) - 36*a_.pow(3)*bm1*binom(p_,3)
                   + 2*a_*a_*bm1*(12*a_+11*b_-19)*binom(p_,2)
                   - a_*bm1*(12*a_*a_+25*a_*b_-41*a_+6*b_*b_-30*b_+30)*p_;
            assert_eq!(n4%24,0); assert_eq!(n4/24, u4, "(p,a,b)=({},{},{}) compact U_4",p,a,b);
            let num = 24*binom(p_,4)*bm2.pow(4) - 36*a_*bm1*bm2*bm2*binom(p_,3)
                    + 2*a_*bm1*(3*a_*bm1+4*bm2*bm2)*binom(p_,2)
                    - a_*bm1*(9*a_*bm1+2*b_*b_-14*b_+14)*p_;
            assert_eq!(num%24,0); assert_eq!(num/24, ubig, "(p,a,b)=({},{},{}) compact U",p,a,b);
            ntested += 1;
            if !c4seen.contains(&c4g) { c4seen.push(c4g); }
        }
        if c4seen.len() > 1 { nvary += 1;
            let sp = c4seen.iter().max().unwrap() - c4seen.iter().min().unwrap();
            if sp > maxspread { maxspread = sp; } }
    }
    println!("  {} random biregular graphs over {} distinct (p,a,b): all subgraph counts, m_1..m_4, and compact U verified", ntested, nparam);
    println!("  {} of the {} parameter triples produced >1 distinct C_4(G) value (max spread {})", nvary, nparam, maxspread);
    println!("\n*** EVERYTHING VERIFIED ***");
}
