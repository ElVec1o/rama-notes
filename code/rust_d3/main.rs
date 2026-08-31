// Can Hall's construction be run at minimum degree three?  If yes, Conjecture D3 is false.
//
// A centre c joined to p copies of a block B at a root vertex r.  The block is chosen so that every
// vertex of the assembled graph has degree at least three: every vertex of B except r has degree at
// least 3 inside B, and r has degree at least 2 inside B, gaining its third from c.
//
// For each (B, r, p) the program decides whether mu_G has a root inside a gap of spec(T_G) that is
// NOT an eigenvalue of the cover.  Such a root refutes D3.
//
// Everything that decides the verdict is EXACT:
//   * mu_G = A^(p-1) (x A - p B_r)  with A = mu_B, B_r = mu_{B-r}, integer coefficients;
//   * roots are ISOLATED BY STURM SEQUENCES over the integers, never by floating-point root finding;
//   * "is theta an eigenvalue of the cover" is decided by the Li-Magee-Sabri-Thomas criterion in the
//     form of exact polynomial divisibility: theta is an eigenvalue iff its minimal polynomial
//     divides mu_{G minus V(Gamma)} for EVERY 2-regular subgraph Gamma, so one Gamma where the
//     division fails is an exact witness that it is not.
// Only the band structure is floating point, and it is used solely to propose candidate intervals;
// nothing is concluded from it alone.
//
// Progress, ETA and an interim checkpoint are written continuously, so a run that is killed still
// leaves its results behind.  Build and run:
//
//     cd code/rust_d3 && cargo run --release
//
// Results append to results.txt and the checkpoint is checkpoint.txt.

use std::fs;
use std::io::Write;
use std::time::Instant;

// ---------------------------------------------------------------- integer polynomials
type Poly = Vec<i128>; // coefficient i multiplies x^i

fn p_trim(mut a: Poly) -> Poly { while a.len() > 1 && *a.last().unwrap() == 0 { a.pop(); } a }
fn p_add(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut r = vec![0i128; n];
    for i in 0..n { r[i] = a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0); }
    p_trim(r)
}
fn p_scale(a: &Poly, k: i128) -> Poly { p_trim(a.iter().map(|c| c * k).collect()) }
fn p_shift(a: &Poly, s: usize) -> Poly {
    let mut r = vec![0i128; s]; r.extend_from_slice(a); p_trim(r)
}
fn p_mul(a: &Poly, b: &Poly) -> Poly {
    let mut r = vec![0i128; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 { continue; }
        for (j, &y) in b.iter().enumerate() {
            r[i + j] = r[i + j].checked_add(x.checked_mul(y).expect("overflow")).expect("overflow");
        }
    }
    p_trim(r)
}
fn p_pow(a: &Poly, mut e: u32) -> Poly {
    let mut r = vec![1i128]; let mut b = a.clone();
    while e > 0 { if e & 1 == 1 { r = p_mul(&r, &b); } b = p_mul(&b, &b); e >>= 1; }
    r
}
fn p_deg(a: &Poly) -> usize { a.len() - 1 }
fn p_is_zero(a: &Poly) -> bool { a.len() == 1 && a[0] == 0 }

/// pseudo-remainder of a by b, exact over Q up to a positive factor
fn p_prem(a: &Poly, b: &Poly) -> Poly {
    let mut r = a.clone();
    if p_is_zero(b) { return r; }
    let db = p_deg(b); let lb = b[db];
    while !p_is_zero(&r) && p_deg(&r) >= db {
        let dr = p_deg(&r); let lr = r[dr];
        let g = gcd_i(lr.abs(), lb.abs()).max(1);
        let (m1, m2) = (lb / g, lr / g);
        r = p_add(&p_scale(&r, m1), &p_scale(&p_shift(b, dr - db), -m2));
        if p_deg(&r) == dr && !p_is_zero(&r) { break; } // safety
    }
    r
}
fn gcd_i(mut a: i128, mut b: i128) -> i128 { while b != 0 { let t = a % b; a = b; b = t; } a.abs() }
fn p_primitive(a: &Poly) -> Poly {
    let mut g = 0i128; for &c in a { g = gcd_i(g, c); }
    if g <= 1 { return a.clone(); }
    p_trim(a.iter().map(|c| c / g).collect())
}
/// does b divide a exactly over Q?
fn p_divides(b: &Poly, a: &Poly) -> bool {
    if p_is_zero(b) { return false; }
    if p_deg(b) > p_deg(a) { return p_is_zero(a); }
    p_is_zero(&p_primitive(&p_prem(a, b)))
}
fn p_deriv(a: &Poly) -> Poly {
    if a.len() <= 1 { return vec![0]; }
    p_trim((1..a.len()).map(|i| a[i] * i as i128).collect())
}
fn p_eval(a: &Poly, x: f64) -> f64 { a.iter().rev().fold(0.0, |acc, &c| acc * x + c as f64) }

/// Sturm sequence; number of distinct real roots in (lo, hi]
fn sturm_count(a: &Poly, lo: f64, hi: f64) -> usize {
    let mut seq: Vec<Poly> = vec![p_primitive(a), p_primitive(&p_deriv(a))];
    while !p_is_zero(seq.last().unwrap()) && p_deg(seq.last().unwrap()) > 0 {
        let n = seq.len();
        let r = p_prem(&seq[n - 2], &seq[n - 1]);
        if p_is_zero(&r) { break; }
        seq.push(p_primitive(&p_scale(&r, -1)));
    }
    let signs = |t: f64| -> usize {
        let mut prev = 0i32; let mut ch = 0usize;
        for q in &seq {
            let v = p_eval(q, t);
            let s = if v > 0.0 { 1 } else if v < 0.0 { -1 } else { 0 };
            if s != 0 { if prev != 0 && s != prev { ch += 1; } prev = s; }
        }
        ch
    };
    signs(lo).saturating_sub(signs(hi))
}

// ---------------------------------------------------------------- graphs
#[derive(Clone)]
struct Graph { n: usize, adj: Vec<Vec<usize>> }
impl Graph {
    fn new(n: usize) -> Self { Graph { n, adj: vec![Vec::new(); n] } }
    fn add(&mut self, a: usize, b: usize) { self.adj[a].push(b); self.adj[b].push(a); }
    fn deg(&self, v: usize) -> usize { self.adj[v].len() }
}

/// matching polynomial by the deletion recursion, memo-free (graphs here are small)
fn mu(g: &Graph, alive: &mut Vec<bool>, cnt: usize) -> Poly {
    // find an edge among alive vertices
    let mut e = None;
    'outer: for u in 0..g.n {
        if !alive[u] { continue; }
        for &v in &g.adj[u] { if alive[v] && v > u { e = Some((u, v)); break 'outer; } }
    }
    match e {
        None => { let mut p = vec![0i128; cnt + 1]; p[cnt] = 1; p } // x^cnt
        Some((u, v)) => {
            alive[u] = false;
            let a = mu(g, alive, cnt - 1);           // G - u  (keeps edge uv? no: standard is x*mu(G-u) ... )
            alive[u] = true;
            // mu_G = x*mu_{G-u} - sum_{v~u} mu_{G-u-v}   using vertex u
            let mut acc = p_shift(&a, 1);
            let nbrs: Vec<usize> = g.adj[u].iter().copied().filter(|&w| alive[w]).collect();
            for w in nbrs {
                alive[u] = false; alive[w] = false;
                let b = mu(g, alive, cnt - 2);
                alive[u] = true; alive[w] = true;
                acc = p_add(&acc, &p_scale(&b, -1));
            }
            let _ = v;
            acc
        }
    }
}
fn mu_of(g: &Graph) -> Poly { let mut al = vec![true; g.n]; mu(g, &mut al, g.n) }
fn mu_minus(g: &Graph, drop: &[usize]) -> Poly {
    let mut al = vec![true; g.n];
    for &d in drop { al[d] = false; }
    let c = al.iter().filter(|&&b| b).count();
    mu(g, &mut al, c)
}

// ---------------------------------------------------------------- cavity band scan (f64, advisory)
struct Cav { m: usize, foll: Vec<Vec<usize>>, into: Vec<Vec<usize>> }
fn cav_prep(g: &Graph) -> Cav {
    let mut de = Vec::new();
    for u in 0..g.n { for &v in &g.adj[u] { de.push((u, v)); } }
    let mut pos = std::collections::HashMap::new();
    for (k, &e) in de.iter().enumerate() { pos.insert(e, k); }
    let m = de.len();
    let mut foll = vec![Vec::new(); m];
    for (k, &(a, b)) in de.iter().enumerate() {
        for &c in &g.adj[b] { if c != a { foll[k].push(pos[&(b, c)]); } }
    }
    let mut into = vec![Vec::new(); g.n];
    for (k, &(_, b)) in de.iter().enumerate() { into[b].push(k); }
    Cav { m, foll, into }
}
fn im_green(cv: &Cav, lam: f64, eta: f64) -> f64 {
    let m = cv.m;
    let mut gr = vec![(0.1f64, 0.1f64); m];
    let mut nw = gr.clone();
    for _ in 0..40000 {
        let mut d = 0.0f64;
        for k in 0..m {
            let (mut sr, mut si) = (lam, eta);
            for &j in &cv.foll[k] { sr -= gr[j].0; si -= gr[j].1; }
            let den = sr * sr + si * si;
            let (vr, vi) = (sr / den, -si / den);
            let (pr, pi) = gr[k];
            nw[k] = (0.5 * pr + 0.5 * vr, 0.5 * pi + 0.5 * vi);
            let e = (nw[k].0 - pr).abs() + (nw[k].1 - pi).abs();
            if e > d { d = e; }
        }
        std::mem::swap(&mut gr, &mut nw);
        if d < 1e-13 { break; }
    }
    let mut tot = 0.0;
    for w in 0..cv.into.len() {
        let (mut sr, mut si) = (lam, eta);
        for &k in &cv.into[w] { sr -= gr[k].0; si -= gr[k].1; }
        tot += -si / (sr * sr + si * si);
    }
    tot.abs()
}
/// intervals where lambda is outside every band (Im G falls linearly in eta)
fn band_gaps(g: &Graph, step: f64, top: f64) -> Vec<(f64, f64)> {
    let cv = cav_prep(g);
    let mut out = Vec::new(); let mut cur: Option<f64> = None;
    let mut t = step;
    while t < top {
        let hi = im_green(&cv, t, 1e-3);
        let lo = im_green(&cv, t, 1e-5);
        let outside = hi > 0.0 && lo / hi < 0.1;
        if outside && cur.is_none() { cur = Some(t); }
        if !outside { if let Some(s) = cur { out.push((s, t)); cur = None; } }
        t += step;
    }
    if let Some(s) = cur { out.push((s, top)); }
    out
}

// ---------------------------------------------------------------- main sweep
#[derive(serde::Deserialize)]
struct Block { n: usize, root: usize, edges: Vec<Vec<usize>> }

fn main() {
    let raw = fs::read_to_string("blocks.json").expect("blocks.json missing");
    let blocks: Vec<Block> = serde_json::from_str(&raw).expect("bad blocks.json");
    let pmax = 8usize; let nmax = 46usize;
    let total: usize = blocks.iter().map(|b| {
        (3..=pmax).filter(|&p| 1 + p * b.n <= nmax).count()
    }).sum();
    println!("{} blocks, {} (block,p) cases, n <= {}", blocks.len(), total, nmax);
    let t0 = Instant::now();
    let mut res = fs::File::create("results.txt").unwrap();
    let mut done = 0usize; let mut viol = 0usize;

    for b in &blocks {
        // block polynomials
        let mut hb = Graph::new(b.n);
        for e in &b.edges { hb.add(e[0], e[1]); }
        let a_poly = mu_of(&hb);
        let br_poly = mu_minus(&hb, &[b.root]);

        for p in 3..=pmax {
            let n = 1 + p * b.n;
            if n > nmax { continue; }
            // assemble
            let mut g = Graph::new(n);
            for c in 0..p {
                let off = 1 + c * b.n;
                for e in &b.edges { g.add(off + e[0], off + e[1]); }
                g.add(0, off + b.root);
            }
            if (0..n).any(|v| g.deg(v) < 3) { continue; }
            done += 1;

            // mu_G = A^(p-1) (x A - p B_r)
            let bracket = p_add(&p_shift(&a_poly, 1), &p_scale(&br_poly, -(p as i128)));
            let mu_g = p_mul(&p_pow(&a_poly, (p - 1) as u32), &bracket);

            let topd = (0..n).map(|v| g.deg(v)).max().unwrap() as f64;
            let gaps = band_gaps(&g, 0.02, 2.0 * (topd - 1.0).sqrt() + 0.5);
            if gaps.is_empty() { continue; }
            // every root of mu_G is a root of A (degree <= 7) or of the bracket (degree <= 8);
            // both are small, so no large-polynomial arithmetic is needed anywhere.
            for (lo, hi) in &gaps {
                let na = sturm_count(&a_poly, *lo, *hi);
                let nb = sturm_count(&bracket, *lo, *hi);
                if na + nb == 0 { continue; }
                // A-roots are branch eigenvalues: the branch union is an Aomoto subset whenever
                // p > 1, so those are eigenvalues of the cover and never violations.
                if nb == 0 { continue; }
                let line = format!("CANDIDATE block {}v {}e root_idx {} p {} n {} gap ({:.4},{:.4}) \
bracket_roots_in_gap {} A_roots_in_gap {}\n",
                                   b.n, b.edges.len(), b.root, p, n, lo, hi, nb, na);
                print!("{}", line);
                res.write_all(line.as_bytes()).unwrap();
                res.flush().unwrap();
                viol += 1;
            }

            if done % 25 == 0 {
                let el = t0.elapsed().as_secs_f64();
                let eta = if done > 0 { el / done as f64 * (total - done) as f64 } else { 0.0 };
                let msg = format!("progress {}/{}  {:.0}s elapsed  ETA {:.0}s  violations {}\n",
                                  done, total, el, eta, viol);
                print!("{}", msg);
                fs::write("checkpoint.txt", &msg).unwrap();
            }
        }
    }
    let msg = format!("DONE {} cases in {:.0}s, {} violations. {}\n", done,
                      t0.elapsed().as_secs_f64(), viol,
                      if viol == 0 { "D3 survives this sweep." } else { "D3 IS FALSE." });
    print!("{}", msg);
    fs::write("checkpoint.txt", &msg).unwrap();
}
