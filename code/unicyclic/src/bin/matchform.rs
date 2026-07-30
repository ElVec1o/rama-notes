// Independent check of the reformulation:  A = mu_G  and  B = -mu_{G - V(C)},
// where mu is the ordinary matching polynomial and C is the unique cycle of G.
// If true the recurrence becomes  V_d = mu_G * V_{d-1} - mu_{G-V(C)}^2 * V_{d-2},
// which collapses to Hall's conjecture at G = C_n (there G - V(C) is empty, mu = 1).

type Poly = Vec<i128>;

fn pnorm(mut p: Poly) -> Poly { while p.len() > 1 && *p.last().unwrap() == 0 { p.pop(); } p }
fn padd(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    pnorm((0..n).map(|i| a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0)).collect())
}
fn psub(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    pnorm((0..n).map(|i| a.get(i).copied().unwrap_or(0) - b.get(i).copied().unwrap_or(0)).collect())
}
fn pneg(a: &Poly) -> Poly { pnorm(a.iter().map(|c| -c).collect()) }
fn pdiv_exact(a: &Poly, k: i128) -> Poly {
    for c in a { assert!(c % k == 0); }
    pnorm(a.iter().map(|c| c / k).collect())
}
fn pfmt(p: &Poly) -> String {
    let mut s = String::new();
    for i in (0..p.len()).rev() {
        let c = p[i]; if c == 0 { continue; }
        if !s.is_empty() { s.push_str(if c > 0 { " + " } else { " - " }); } else if c < 0 { s.push('-'); }
        let a = c.abs();
        if a != 1 || i == 0 { s.push_str(&a.to_string()); }
        if i >= 1 { s.push('x'); }
        if i >= 2 { s.push_str(&format!("^{}", i)); }
    }
    if s.is_empty() { "1".into() } else { s }
}

fn charpoly(m: &Vec<Vec<i128>>) -> Poly {
    let n = m.len();
    let mut acc = vec![vec![0i128; n]; n];
    let mut coeffs = vec![0i128; n + 1]; coeffs[n] = 1;
    let mut c = 1i128;
    for k in 1..=n {
        let mut t = vec![vec![0i128; n]; n];
        for i in 0..n { for l in 0..n { let v = m[i][l]; if v != 0 {
            for j in 0..n { t[i][j] += v * acc[l][j]; } } } }
        for i in 0..n { t[i][i] += c; }
        acc = t;
        let mut tr = 0i128;
        for i in 0..n { for l in 0..n { tr += m[i][l] * acc[l][i]; } }
        c = -tr / (k as i128);
        coeffs[n - k] = c;
    }
    pnorm(coeffs)
}

/// matching polynomial sum_k (-1)^k m_k x^{n-2k} of the graph on `n` vertices with `edges`
fn matching_poly(n: usize, edges: &[(usize, usize)]) -> Poly {
    let mut counts = vec![0i128; n / 2 + 2];
    fn rec(i: usize, used: u64, k: usize, edges: &[(usize, usize)], counts: &mut Vec<i128>) {
        counts[k] += 1;
        for j in i..edges.len() {
            let (u, v) = edges[j];
            let bit = (1u64 << u) | (1u64 << v);
            if used & bit == 0 { rec(j + 1, used | bit, k + 1, edges, counts); }
        }
    }
    rec(0, 0, 0, edges, &mut counts);
    let mut p = vec![0i128; n + 1];
    for (k, &c) in counts.iter().enumerate() {
        if 2 * k <= n { p[n - 2 * k] += if k % 2 == 0 { c } else { -c }; }
    }
    pnorm(p)
}

struct G { n: usize, edges: Vec<(usize, usize)>, e: usize, cycle: Vec<usize> }

fn main() {
    let cyc = |m: usize| -> Vec<(usize, usize)> { (0..m).map(|i| (i, (i + 1) % m)).collect() };
    let mut gs: Vec<(&str, G)> = vec![];
    gs.push(("C_3", G { n: 3, edges: cyc(3), e: 2, cycle: vec![0,1,2] }));
    gs.push(("C_5", G { n: 5, edges: cyc(5), e: 4, cycle: vec![0,1,2,3,4] }));
    { let mut e = cyc(3); e.push((0,3));
      gs.push(("tadpole T(3,1)", G { n: 4, edges: e, e: 2, cycle: vec![0,1,2] })); }
    { let mut e = cyc(4); e.push((0,4));
      gs.push(("tadpole T(4,1)", G { n: 5, edges: e, e: 3, cycle: vec![0,1,2,3] })); }
    { let mut e = cyc(3); e.push((0,3)); e.push((1,4));
      gs.push(("C_3 + 2 pendants", G { n: 5, edges: e, e: 2, cycle: vec![0,1,2] })); }
    { let mut e = cyc(3); e.push((0,3)); e.push((3,4));
      gs.push(("C_3 + path P2", G { n: 5, edges: e, e: 2, cycle: vec![0,1,2] })); }
    { let mut e = cyc(3); e.push((0,3)); e.push((0,4)); e.push((0,5));
      gs.push(("C_3 + star K_1,3", G { n: 6, edges: e, e: 2, cycle: vec![0,1,2] })); }
    { let mut e = cyc(4); e.push((0,4)); e.push((2,5));
      gs.push(("C_4 + 2 opp pendants", G { n: 6, edges: e, e: 3, cycle: vec![0,1,2,3] })); }
    { let mut e = cyc(4); e.push((0,4)); e.push((4,5)); e.push((5,6));
      gs.push(("C_4 + path P3", G { n: 7, edges: e, e: 3, cycle: vec![0,1,2,3] })); }
    { let mut e = cyc(6); e.push((0,6)); e.push((3,7));
      gs.push(("C_6 + 2 pendants", G { n: 8, edges: e, e: 5, cycle: vec![0,1,2,3,4,5] })); }
    { let mut e = cyc(5); e.push((0,5)); e.push((5,6)); e.push((1,7)); e.push((2,8));
      gs.push(("C_5 + mixed trees", G { n: 9, edges: e, e: 4, cycle: vec![0,1,2,3,4] })); }

    println!("check:  A == mu_G   and   B == -mu_{{G - V(C)}}\n");
    let mut all = true;
    for (name, g) in gs.iter() {
        // A, B from the twisted char poly, via z = +1 and z = -1
        let adj = |w: i128| -> Vec<Vec<i128>> {
            let mut a = vec![vec![0i128; g.n]; g.n];
            for (i, &(u, v)) in g.edges.iter().enumerate() {
                let val = if i == g.e { w } else { 1 };
                a[u][v] += val; a[v][u] += val;
            }
            a
        };
        let (cp, cm) = (charpoly(&adj(1)), charpoly(&adj(-1)));
        let a_tw = pdiv_exact(&padd(&cp, &cm), 2);
        let b_tw = pdiv_exact(&psub(&cp, &cm), 4);

        // mu_G and mu_{G - V(C)}
        let mu_g = matching_poly(g.n, &g.edges);
        let keep: Vec<usize> = (0..g.n).filter(|v| !g.cycle.contains(v)).collect();
        let idx = |v: usize| keep.iter().position(|&k| k == v).unwrap();
        let sub_edges: Vec<(usize, usize)> = g.edges.iter()
            .filter(|(u, v)| keep.contains(u) && keep.contains(v))
            .map(|&(u, v)| (idx(u), idx(v))).collect();
        let mu_sub = matching_poly(keep.len(), &sub_edges);

        let ok_a = a_tw == mu_g;
        let ok_b = b_tw == pneg(&mu_sub);
        if !ok_a || !ok_b { all = false; }
        println!("  {:22}  A == mu_G : {:5}    B == -mu_{{G-V(C)}} : {:5}",
                 name, if ok_a { "OK" } else { "FAIL" }, if ok_b { "OK" } else { "FAIL" });
        println!("       mu_G        = {}", pfmt(&mu_g));
        println!("       mu_{{G-V(C)}} = {}", pfmt(&mu_sub));
    }
    println!("\n  all: {}", if all { "CONFIRMED" } else { "REFUTED" });
    println!("\n  So the recurrence is  V_d = mu_G * V_{{d-1}} - mu_{{G-V(C)}}^2 * V_{{d-2}},  V_0 = 1, V_1 = mu_G.");
    println!("  For G = C_n the deleted graph is empty, mu = 1, giving the Chebyshev U recurrence in mu_{{C_n}}.");
}
