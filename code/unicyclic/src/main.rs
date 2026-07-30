// Does the exponential-formula / Chebyshev method for cycles extend to other graphs?
//
// CLAIM UNDER TEST.  Let G be connected with first Betti number 1 (unicyclic: one cycle, trees
// hanging off).  Fix the unique non-tree edge e.  Let
//     chi^+ = char poly of G,           chi^- = char poly of G with edge e weighted -1,
//     A = (chi^+ + chi^-)/2,            B = (chi^+ - chi^-)/4.
// (These are the coefficients in the twisted char poly det(xI - A(z)) = A(x) + B(x)(z + 1/z),
//  obtained by evaluating at z = +1 and z = -1.)  Define
//     V_0 = 1,  V_1 = A,  V_d = A*V_{d-1} - B^2*V_{d-2}.
// Then      E[char poly of a random r-lift]  =  chi^+ * V_{r-1},
// equivalently the d-matching polynomial is  mu_{d,G} = V_d.
// For a cycle C_m this is A = 2T_m(x/2), B = -1, V_d = U_d(T_m(x/2)): the known case.
//
// TESTS
//   1. gauge fixing: full brute force over all edges == single permutation on e
//   2. main formula vs brute-forced lift average, many graphs, r = 1..6
//   3. independent check against the DEFINITION of mu_d (average matching polynomial over covers)
//   4. NEGATIVE CONTROLS: graphs with Betti number >= 2 must FAIL (theta, bowtie, K_4, K_{2,3})
//   5. random sweep over unicyclic graphs
//
// Exact integer arithmetic throughout (i128).

use std::collections::HashMap;

type Poly = Vec<i128>; // coeff[i] = coefficient of x^i

fn pnorm(mut p: Poly) -> Poly {
    while p.len() > 1 && *p.last().unwrap() == 0 { p.pop(); }
    p
}
fn padd(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut r = vec![0i128; n];
    for i in 0..n { r[i] = a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0); }
    pnorm(r)
}
fn psub(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut r = vec![0i128; n];
    for i in 0..n { r[i] = a.get(i).copied().unwrap_or(0) - b.get(i).copied().unwrap_or(0); }
    pnorm(r)
}
fn pmul(a: &Poly, b: &Poly) -> Poly {
    let mut r = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 { continue; }
        for (j, &y) in b.iter().enumerate() { r[i + j] += x * y; }
    }
    pnorm(r)
}
fn pscale(a: &Poly, k: i128) -> Poly { pnorm(a.iter().map(|c| c * k).collect()) }
fn pdiv_exact(a: &Poly, k: i128) -> Poly {
    for c in a { assert!(c % k == 0, "not divisible by {}", k); }
    pnorm(a.iter().map(|c| c / k).collect())
}
fn pfmt(p: &Poly) -> String {
    let mut s = String::new();
    for i in (0..p.len()).rev() {
        let c = p[i];
        if c == 0 { continue; }
        if !s.is_empty() { s.push_str(if c > 0 { " + " } else { " - " }); }
        else if c < 0 { s.push('-'); }
        let a = c.abs();
        if a != 1 || i == 0 { s.push_str(&a.to_string()); }
        if i >= 1 { s.push('x'); }
        if i >= 2 { s.push_str(&format!("^{}", i)); }
    }
    if s.is_empty() { "0".into() } else { s }
}

/// char poly det(xI - M) of an integer matrix, Faddeev-LeVerrier, exact.
fn charpoly(m: &Vec<Vec<i128>>) -> Poly {
    let n = m.len();
    let mut acc = vec![vec![0i128; n]; n];
    let mut coeffs = vec![0i128; n + 1];
    coeffs[n] = 1;
    let mut c = 1i128;
    for k in 1..=n {
        // acc = m*acc + c*I
        let mut t = vec![vec![0i128; n]; n];
        for i in 0..n {
            for l in 0..n {
                let v = m[i][l];
                if v == 0 { continue; }
                for j in 0..n { t[i][j] += v * acc[l][j]; }
            }
        }
        for i in 0..n { t[i][i] += c; }
        acc = t;
        let mut tr = 0i128;
        for i in 0..n { for l in 0..n { tr += m[i][l] * acc[l][i]; } }
        assert!(tr % (k as i128) == 0);
        c = -tr / (k as i128);
        coeffs[n - k] = c;
    }
    pnorm(coeffs)
}

#[derive(Clone)]
struct Graph { n: usize, edges: Vec<(usize, usize)>, e_idx: usize }

impl Graph {
    fn betti(&self) -> i64 { self.edges.len() as i64 - self.n as i64 + 1 }
    /// adjacency with edge e_idx given weight w (+1 or -1)
    fn adj_signed(&self, w: i128) -> Vec<Vec<i128>> {
        let mut a = vec![vec![0i128; self.n]; self.n];
        for (i, &(u, v)) in self.edges.iter().enumerate() {
            let val = if i == self.e_idx { w } else { 1 };
            a[u][v] += val; a[v][u] += val;
        }
        a
    }
    fn chi_plus(&self) -> Poly { charpoly(&self.adj_signed(1)) }
    /// A and B of the twisted char poly, via z = +1 and z = -1
    fn ab(&self) -> (Poly, Poly) {
        let cp = charpoly(&self.adj_signed(1));
        let cm = charpoly(&self.adj_signed(-1));
        (pdiv_exact(&padd(&cp, &cm), 2), pdiv_exact(&psub(&cp, &cm), 4))
    }
}

/// V_0 = 1, V_1 = A, V_d = A*V_{d-1} - B^2*V_{d-2}
fn v_poly(a: &Poly, b: &Poly, d: usize) -> Poly {
    let b2 = pmul(b, b);
    let mut prev = vec![1i128];
    if d == 0 { return prev; }
    let mut cur = a.clone();
    for _ in 2..=d {
        let next = psub(&pmul(a, &cur), &pmul(&b2, &prev));
        prev = cur; cur = next;
    }
    cur
}

fn perms(r: usize) -> Vec<Vec<usize>> {
    let mut out = vec![];
    let mut cur: Vec<usize> = (0..r).collect();
    fn rec(k: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if k == cur.len() { out.push(cur.clone()); return; }
        for i in k..cur.len() { cur.swap(k, i); rec(k + 1, cur, out); cur.swap(k, i); }
    }
    rec(0, &mut cur, &mut out);
    out
}

fn lift_adj(g: &Graph, r: usize, choice: &[usize]) -> Vec<Vec<i128>> {
    let ps = perms(r);
    let n = g.n * r;
    let mut a = vec![vec![0i128; n]; n];
    for (ei, &(u, v)) in g.edges.iter().enumerate() {
        let p = &ps[choice[ei]];
        for i in 0..r {
            let (x, y) = (u * r + i, v * r + p[i]);
            a[x][y] += 1; a[y][x] += 1;
        }
    }
    a
}

/// Average char poly over r-lifts. gauge=true: only edge e_idx varies (identity elsewhere).
/// Returns (sum_of_coeff_polys, count) so the comparison stays exact.
fn lift_avg(g: &Graph, r: usize, gauge: bool) -> (Poly, i128) {
    let ps = perms(r);
    let m = g.edges.len();
    let mut total: Poly = vec![0];
    let mut count: i128 = 0;
    if gauge {
        for pi in 0..ps.len() {
            let mut choice = vec![0usize; m];
            choice[g.e_idx] = pi;
            total = padd(&total, &charpoly(&lift_adj(g, r, &choice)));
            count += 1;
        }
    } else {
        let mut choice = vec![0usize; m];
        loop {
            total = padd(&total, &charpoly(&lift_adj(g, r, &choice)));
            count += 1;
            let mut k = 0;
            loop {
                if k == m { return (total, count); }
                choice[k] += 1;
                if choice[k] < ps.len() { break; }
                choice[k] = 0; k += 1;
            }
        }
    }
    (total, count)
}

// ---- matching polynomial, for the independent check of the DEFINITION of mu_d ----
fn matching_poly(n: usize, edges: &[(usize, usize)]) -> Poly {
    // m_k = number of k-matchings; mu = sum_k (-1)^k m_k x^{n-2k}
    let mut counts = vec![0i128; n / 2 + 1];
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

fn lift_edges(g: &Graph, r: usize, choice: &[usize]) -> Vec<(usize, usize)> {
    let ps = perms(r);
    let mut out = vec![];
    for (ei, &(u, v)) in g.edges.iter().enumerate() {
        let p = &ps[choice[ei]];
        for i in 0..r { out.push((u * r + i, v * r + p[i])); }
    }
    out
}

/// average matching polynomial over all d-covers (the definition of mu_{d,G})
fn mu_direct(g: &Graph, d: usize) -> (Poly, i128) {
    let ps = perms(d);
    let m = g.edges.len();
    let mut total: Poly = vec![0];
    let mut count: i128 = 0;
    let mut choice = vec![0usize; m];
    loop {
        let e = lift_edges(g, d, &choice);
        total = padd(&total, &matching_poly(g.n * d, &e));
        count += 1;
        let mut k = 0;
        loop {
            if k == m { return (total, count); }
            choice[k] += 1;
            if choice[k] < ps.len() { break; }
            choice[k] = 0; k += 1;
        }
    }
}

fn cyc(m: usize) -> Vec<(usize, usize)> { (0..m).map(|i| (i, (i + 1) % m)).collect() }

fn main() {
    // ---------- graph battery ----------
    let mut gs: Vec<(String, Graph)> = vec![];
    let mk = |n: usize, e: Vec<(usize, usize)>, ei: usize| Graph { n, edges: e, e_idx: ei };
    gs.push(("C_3".into(), mk(3, cyc(3), 2)));
    gs.push(("C_4".into(), mk(4, cyc(4), 3)));
    gs.push(("C_5".into(), mk(5, cyc(5), 4)));
    gs.push(("C_6".into(), mk(6, cyc(6), 5)));
    { let mut e = cyc(3); e.push((0, 3)); gs.push(("tadpole T(3,1)".into(), mk(4, e, 2))); }
    { let mut e = cyc(4); e.push((0, 4)); gs.push(("tadpole T(4,1)".into(), mk(5, e, 3))); }
    { let mut e = cyc(5); e.push((0, 5)); gs.push(("tadpole T(5,1)".into(), mk(6, e, 4))); }
    { let mut e = cyc(3); e.push((0, 3)); e.push((1, 4)); gs.push(("C_3 + 2 pendants".into(), mk(5, e, 2))); }
    { let mut e = cyc(3); e.push((0, 3)); e.push((3, 4)); gs.push(("C_3 + path P2".into(), mk(5, e, 2))); }
    { let mut e = cyc(3); e.push((0,3)); e.push((0,4)); e.push((0,5)); gs.push(("C_3 + star K_1,3".into(), mk(6, e, 2))); }
    { let mut e = cyc(4); e.push((0, 4)); e.push((2, 5)); gs.push(("C_4 + 2 opp pendants".into(), mk(6, e, 3))); }
    { let mut e = cyc(4); e.push((0,4)); e.push((4,5)); e.push((5,6)); gs.push(("C_4 + path P3".into(), mk(7, e, 3))); }
    { let mut e = cyc(6); e.push((0,6)); e.push((3,7)); gs.push(("C_6 + 2 pendants".into(), mk(8, e, 5))); }

    println!("=== 1. gauge fixing: full brute force over ALL edges vs one permutation on e ===");
    for (name, g) in gs.iter().take(6) {
        for r in 2..=3 {
            let (sf, cf) = lift_avg(g, r, false);
            let (sg, cg) = lift_avg(g, r, true);
            let ok = pscale(&sf, cg) == pscale(&sg, cf);
            println!("  {:22} r={}  {}", name, r, if ok { "MATCH" } else { "DIFFER" });
        }
    }

    println!("\n=== 2. main formula:  E[char poly of r-lift]  ==  chi_G * V_{{r-1}}(A,B) ===");
    let mut all_ok = true;
    for (name, g) in gs.iter() {
        let (a, b) = g.ab();
        let chi = g.chi_plus();
        let rmax = if g.n <= 5 { 6 } else if g.n <= 6 { 5 } else { 4 };
        let mut res = vec![];
        for r in 1..=rmax {
            let pred = pmul(&chi, &v_poly(&a, &b, r - 1));
            let (s, c) = lift_avg(g, r, true);
            let ok = pscale(&pred, c) == s;
            if !ok { all_ok = false; }
            res.push(if ok { "OK" } else { "FAIL" });
        }
        println!("  {:22} betti={}  r=1..{}: {:?}", name, g.betti(), rmax, res);
        println!("       A(x) = {}", pfmt(&a));
        println!("       B(x) = {}", pfmt(&b));
    }
    println!("  ---> all unicyclic tests passed: {}", all_ok);

    println!("\n=== 3. independent check against the DEFINITION of mu_d (avg matching poly over covers) ===");
    for (name, g) in gs.iter().take(6) {
        let (a, b) = g.ab();
        for d in 1..=2 {
            let (s, c) = mu_direct(g, d);
            let pred = v_poly(&a, &b, d);
            let ok = pscale(&pred, c) == s;
            println!("  {:22} d={}  mu_d == V_d : {}", name, d, if ok { "OK" } else { "FAIL" });
        }
    }

    println!("\n=== 4. NEGATIVE CONTROLS: first Betti number >= 2, formula must FAIL ===");
    let mut negs: Vec<(String, Graph)> = vec![];
    negs.push(("theta graph".into(), mk(4, vec![(0,1),(0,2),(2,1),(0,3),(3,1)], 0)));
    negs.push(("bowtie".into(), mk(5, vec![(0,1),(1,2),(2,0),(2,3),(3,4),(4,2)], 2)));
    negs.push(("K_4".into(), mk(4, vec![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], 5)));
    negs.push(("K_{2,3}".into(), mk(5, vec![(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)], 5)));
    negs.push(("two triangles + bridge".into(), mk(6, vec![(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3)], 2)));
    for (name, g) in negs.iter() {
        let (a, b) = g.ab();
        let chi = g.chi_plus();
        let mut res = vec![];
        for r in 1..=3 {
            let pred = pmul(&chi, &v_poly(&a, &b, r - 1));
            let (s, c) = lift_avg(g, r, false); // full brute force: all edges free
            res.push(if pscale(&pred, c) == s { "holds" } else { "FAILS" });
        }
        println!("  {:24} betti={}  r=1..3: {:?}", name, g.betti(), res);
    }

    println!("\n=== 5. random sweep over unicyclic graphs (seeded, deterministic) ===");
    let mut seed: u64 = 0x9E3779B97F4A7C15;
    let mut next = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let (mut tested, mut passed) = (0, 0);
    for _ in 0..40 {
        let m = 3 + (next() % 4) as usize;              // cycle length 3..6
        let extra = (next() % 3) as usize;              // 0..2 extra tree vertices
        let n = m + extra;
        if n > 7 { continue; }
        let mut e = cyc(m);
        for t in 0..extra {
            let attach = (next() as usize) % (m + t);
            e.push((attach, m + t));
        }
        let g = mk(n, e, m - 1);
        let (a, b) = g.ab();
        let chi = g.chi_plus();
        let rmax = if n <= 5 { 5 } else { 4 };
        let mut ok_all = true;
        for r in 1..=rmax {
            let pred = pmul(&chi, &v_poly(&a, &b, r - 1));
            let (s, c) = lift_avg(&g, r, true);
            if pscale(&pred, c) != s { ok_all = false; }
        }
        tested += 1;
        if ok_all { passed += 1; } else { println!("  FAIL on n={} edges={:?}", n, g.edges); }
    }
    println!("  random unicyclic graphs: {}/{} passed (r up to 5)", passed, tested);
}
